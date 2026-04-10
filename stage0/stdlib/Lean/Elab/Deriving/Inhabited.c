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
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__18_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__22_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__24_value;
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
v___x_493_ = lean_nat_add(v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec(v___y_491_);
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
lean_ctor_set(v___x_473_, 3, v___y_490_);
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
lean_ctor_set(v_reuseFailAlloc_498_, 3, v___y_490_);
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
v___y_490_ = v___x_504_;
v___y_491_ = v___x_505_;
v___y_492_ = v_size_506_;
goto v___jp_489_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___y_490_ = v___x_504_;
v___y_491_ = v___x_505_;
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
v___x_631_ = lean_nat_add(v___y_628_, v___y_630_);
lean_dec(v___y_630_);
lean_dec(v___y_628_);
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
lean_ctor_set(v___x_611_, 3, v___y_629_);
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
lean_ctor_set(v_reuseFailAlloc_636_, 3, v___y_629_);
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
v___y_628_ = v___x_644_;
v___y_629_ = v___x_643_;
v___y_630_ = v_size_645_;
goto v___jp_627_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___y_628_ = v___x_644_;
v___y_629_ = v___x_643_;
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
lean_inc_n(v_macroStack_1398_, 2);
v___x_1399_ = l_Lean_Elab_getBetterRef(v_ref_1395_, v_macroStack_1398_);
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
lean_inc(v___y_2076_);
v___x_2078_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_oldTraces_2059_, v_data_2077_, v___y_2076_, v___y_2075_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
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
v___y_2075_ = v_m_2097_;
v___y_2076_ = v___y_2088_;
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
v___y_2075_ = v_m_2097_;
v___y_2076_ = v___y_2088_;
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
v___x_2496_ = lean_float_of_nat(v___y_2492_);
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
v___x_2505_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2487_, v_hasTrace_2462_, v___x_2488_, v_options_2461_, v___x_2490_, v___y_2493_, v___f_2486_, v___x_2504_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
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
v___y_2512_ = v___x_2555_;
v___y_2513_ = v_a_2552_;
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
v___y_2517_ = v___x_2555_;
v___y_2518_ = v_a_2552_;
v___y_2519_ = v___x_2564_;
goto v___jp_2516_;
}
}
else
{
lean_dec(v_a_2557_);
v___y_2517_ = v___x_2555_;
v___y_2518_ = v_a_2552_;
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
v___y_2507_ = v___x_2555_;
v___y_2508_ = v_a_2552_;
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
lean_object* v___x_2947_; lean_object* v___x_26195__overap_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_26195__overap_2948_ = lean_panic_fn_borrowed(v___x_2947_, v_msg_2939_);
lean_inc(v___y_2945_);
lean_inc_ref(v___y_2944_);
lean_inc(v___y_2943_);
lean_inc_ref(v___y_2942_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
v___x_2949_ = lean_apply_7(v___x_26195__overap_2948_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, lean_box(0));
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
uint8_t v___x_31212__boxed_3156_; lean_object* v_res_3157_; 
v___x_31212__boxed_3156_ = lean_unbox(v___x_3147_);
v_res_3157_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3146_, v___x_31212__boxed_3156_, v_x_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
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
lean_inc(v___y_3186_);
v___x_3188_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_oldTraces_3169_, v_data_3187_, v___y_3186_, v___y_3185_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
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
v___y_3185_ = v_m_3215_;
v___y_3186_ = v___y_3206_;
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
v___y_3185_ = v_m_3215_;
v___y_3186_ = v___y_3206_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3384_, lean_object* v_us_3385_, lean_object* v_xs_3386_, lean_object* v___x_3387_, lean_object* v___x_3388_, lean_object* v_ctorName_3389_, lean_object* v___x_3390_, lean_object* v___f_3391_, lean_object* v_insts_3392_, lean_object* v_localInst2Index_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v___x_3401_; lean_object* v_env_3402_; lean_object* v___x_3403_; lean_object* v_type_3404_; lean_object* v___y_3406_; uint8_t v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3447_; lean_object* v___y_3448_; uint8_t v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v_val_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3573_; lean_object* v___y_3584_; uint8_t v___x_3594_; uint8_t v___x_3595_; 
v___x_3401_ = lean_st_ref_get(v___y_3399_);
v_env_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc_ref(v_env_3402_);
lean_dec(v___x_3401_);
lean_inc(v_us_3385_);
lean_inc(v_inductiveTypeName_3384_);
v___x_3403_ = l_Lean_Expr_const___override(v_inductiveTypeName_3384_, v_us_3385_);
v_type_3404_ = l_Lean_mkAppN(v___x_3403_, v_xs_3386_);
v___x_3594_ = l_Lean_isStructure(v_env_3402_, v_inductiveTypeName_3384_);
v___x_3595_ = 1;
if (v___x_3594_ == 0)
{
lean_object* v_options_3596_; lean_object* v_inheritedTraceOptions_3597_; uint8_t v_hasTrace_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_dec_ref(v___f_3391_);
v_options_3596_ = lean_ctor_get(v___y_3398_, 2);
v_inheritedTraceOptions_3597_ = lean_ctor_get(v___y_3398_, 13);
v_hasTrace_3598_ = lean_ctor_get_uint8(v_options_3596_, sizeof(void*)*1);
lean_inc(v_ctorName_3389_);
v___x_3599_ = l_Lean_Expr_const___override(v_ctorName_3389_, v_us_3385_);
v___x_3600_ = l_Lean_mkAppN(v___x_3599_, v___x_3390_);
if (v_hasTrace_3598_ == 0)
{
lean_object* v___x_3601_; 
lean_dec(v_ctorName_3389_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc_ref(v___x_3600_);
v___x_3601_ = lean_infer_type(v___x_3600_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; lean_object* v___x_3605_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref(v___x_3601_);
v___x_3603_ = lean_box(0);
v___x_3604_ = 0;
v___x_3605_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3602_, v___x_3603_, v___x_3604_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v_snd_3607_; lean_object* v_fst_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3651_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3605_);
v_snd_3607_ = lean_ctor_get(v_a_3606_, 1);
v_fst_3608_ = lean_ctor_get(v_a_3606_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_a_3606_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3610_ = v_a_3606_;
v_isShared_3611_ = v_isSharedCheck_3651_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_snd_3607_);
lean_inc(v_fst_3608_);
lean_dec(v_a_3606_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3651_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v_snd_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3649_; 
v_snd_3612_ = lean_ctor_get(v_snd_3607_, 1);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_snd_3607_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; 
v_unused_3650_ = lean_ctor_get(v_snd_3607_, 0);
lean_dec(v_unused_3650_);
v___x_3614_ = v_snd_3607_;
v_isShared_3615_ = v_isSharedCheck_3649_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_snd_3612_);
lean_dec(v_snd_3607_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3649_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3616_; 
lean_inc(v_snd_3612_);
lean_inc_ref(v_type_3404_);
v___x_3616_ = l_Lean_Meta_isExprDefEq(v_type_3404_, v_snd_3612_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; uint8_t v___x_3618_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref(v___x_3616_);
v___x_3618_ = lean_unbox(v_a_3617_);
lean_dec(v_a_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_dec(v_fst_3608_);
lean_dec_ref(v___x_3600_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v___x_3619_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3620_ = l_Lean_indentExpr(v_type_3404_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set_tag(v___x_3614_, 7);
lean_ctor_set(v___x_3614_, 1, v___x_3620_);
lean_ctor_set(v___x_3614_, 0, v___x_3619_);
v___x_3622_ = v___x_3614_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3623_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3611_ == 0)
{
lean_ctor_set_tag(v___x_3610_, 7);
lean_ctor_set(v___x_3610_, 1, v___x_3623_);
lean_ctor_set(v___x_3610_, 0, v___x_3622_);
v___x_3625_ = v___x_3610_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3622_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
v___x_3626_ = l_Lean_indentExpr(v_snd_3612_);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3627_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3628_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
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
else
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
lean_del_object(v___x_3614_);
lean_dec(v_snd_3612_);
lean_del_object(v___x_3610_);
v___x_3639_ = lean_box(0);
v___x_3640_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3600_, v_fst_3608_, v___x_3639_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v_fst_3608_);
v___y_3573_ = v___x_3640_;
goto v___jp_3572_;
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_del_object(v___x_3614_);
lean_dec(v_snd_3612_);
lean_del_object(v___x_3610_);
lean_dec(v_fst_3608_);
lean_dec_ref(v___x_3600_);
lean_dec_ref(v_type_3404_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v_a_3641_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3616_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3616_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
lean_dec_ref(v___x_3600_);
lean_dec_ref(v_type_3404_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v_a_3652_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3605_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3605_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
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
return v___x_3657_;
}
}
}
}
else
{
lean_dec_ref(v___x_3600_);
v___y_3573_ = v___x_3601_;
goto v___jp_3572_;
}
}
else
{
lean_object* v___x_3660_; lean_object* v___f_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v_a_3669_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v_a_3684_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v_a_3702_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v_a_3714_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; 
v___x_3660_ = lean_box(v___x_3594_);
v___f_3661_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed), 10, 2);
lean_closure_set(v___f_3661_, 0, v_ctorName_3389_);
lean_closure_set(v___f_3661_, 1, v___x_3660_);
v___x_3662_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3663_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3664_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3597_, v_options_3596_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3812_; uint8_t v___x_3813_; 
v___x_3812_ = l_Lean_trace_profiler;
v___x_3813_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3596_, v___x_3812_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; 
lean_dec_ref(v___f_3661_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc_ref(v___x_3600_);
v___x_3814_ = lean_infer_type(v___x_3600_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref(v___x_3814_);
v___x_3816_ = lean_box(0);
v___x_3817_ = 0;
v___x_3818_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3815_, v___x_3816_, v___x_3817_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v_snd_3820_; lean_object* v_fst_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3864_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3818_);
v_snd_3820_ = lean_ctor_get(v_a_3819_, 1);
v_fst_3821_ = lean_ctor_get(v_a_3819_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_a_3819_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3823_ = v_a_3819_;
v_isShared_3824_ = v_isSharedCheck_3864_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_snd_3820_);
lean_inc(v_fst_3821_);
lean_dec(v_a_3819_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3864_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v_snd_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3862_; 
v_snd_3825_ = lean_ctor_get(v_snd_3820_, 1);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_snd_3820_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; 
v_unused_3863_ = lean_ctor_get(v_snd_3820_, 0);
lean_dec(v_unused_3863_);
v___x_3827_ = v_snd_3820_;
v_isShared_3828_ = v_isSharedCheck_3862_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_snd_3825_);
lean_dec(v_snd_3820_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3862_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; 
lean_inc(v_snd_3825_);
lean_inc_ref(v_type_3404_);
v___x_3829_ = l_Lean_Meta_isExprDefEq(v_type_3404_, v_snd_3825_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; uint8_t v___x_3831_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = lean_unbox(v_a_3830_);
lean_dec(v_a_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3835_; 
lean_dec(v_fst_3821_);
lean_dec_ref(v___x_3600_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v___x_3832_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3833_ = l_Lean_indentExpr(v_type_3404_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set_tag(v___x_3827_, 7);
lean_ctor_set(v___x_3827_, 1, v___x_3833_);
lean_ctor_set(v___x_3827_, 0, v___x_3832_);
v___x_3835_ = v___x_3827_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3851_, 1, v___x_3833_);
v___x_3835_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3836_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3824_ == 0)
{
lean_ctor_set_tag(v___x_3823_, 7);
lean_ctor_set(v___x_3823_, 1, v___x_3836_);
lean_ctor_set(v___x_3823_, 0, v___x_3835_);
v___x_3838_ = v___x_3823_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
v___x_3839_ = l_Lean_indentExpr(v_snd_3825_);
v___x_3840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3840_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3841_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3841_);
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
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_del_object(v___x_3823_);
v___x_3852_ = lean_box(0);
v___x_3853_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3600_, v_fst_3821_, v___x_3852_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v_fst_3821_);
v___y_3573_ = v___x_3853_;
goto v___jp_3572_;
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_del_object(v___x_3827_);
lean_dec(v_snd_3825_);
lean_del_object(v___x_3823_);
lean_dec(v_fst_3821_);
lean_dec_ref(v___x_3600_);
lean_dec_ref(v_type_3404_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v_a_3854_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3829_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3829_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v___x_3600_);
lean_dec_ref(v_type_3404_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v_a_3865_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3818_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3818_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
}
else
{
lean_dec_ref(v___x_3600_);
v___y_3573_ = v___x_3814_;
goto v___jp_3572_;
}
}
else
{
goto v___jp_3729_;
}
}
else
{
goto v___jp_3729_;
}
v___jp_3666_:
{
lean_object* v___x_3670_; double v___x_3671_; double v___x_3672_; double v___x_3673_; double v___x_3674_; double v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3670_ = lean_io_mono_nanos_now();
v___x_3671_ = lean_float_of_nat(v___y_3668_);
v___x_3672_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3673_ = lean_float_div(v___x_3671_, v___x_3672_);
v___x_3674_ = lean_float_of_nat(v___x_3670_);
v___x_3675_ = lean_float_div(v___x_3674_, v___x_3672_);
v___x_3676_ = lean_box_float(v___x_3673_);
v___x_3677_ = lean_box_float(v___x_3675_);
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v_a_3669_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3662_, v___x_3595_, v___x_3663_, v_options_3596_, v___x_3665_, v___y_3667_, v___f_3661_, v___x_3679_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v___y_3573_ = v___x_3680_;
goto v___jp_3572_;
}
v___jp_3681_:
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_a_3684_);
v___y_3667_ = v___y_3682_;
v___y_3668_ = v___y_3683_;
v_a_3669_ = v___x_3685_;
goto v___jp_3666_;
}
v___jp_3686_:
{
if (lean_obj_tag(v___y_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
v_a_3690_ = lean_ctor_get(v___y_3689_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___y_3689_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___y_3689_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___y_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 1);
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
v___y_3667_ = v___y_3687_;
v___y_3668_ = v___y_3688_;
v_a_3669_ = v___x_3695_;
goto v___jp_3666_;
}
}
}
else
{
lean_object* v_a_3698_; 
v_a_3698_ = lean_ctor_get(v___y_3689_, 0);
lean_inc(v_a_3698_);
lean_dec_ref(v___y_3689_);
v___y_3682_ = v___y_3687_;
v___y_3683_ = v___y_3688_;
v_a_3684_ = v_a_3698_;
goto v___jp_3681_;
}
}
v___jp_3699_:
{
lean_object* v___x_3703_; double v___x_3704_; double v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3703_ = lean_io_get_num_heartbeats();
v___x_3704_ = lean_float_of_nat(v___y_3701_);
v___x_3705_ = lean_float_of_nat(v___x_3703_);
v___x_3706_ = lean_box_float(v___x_3704_);
v___x_3707_ = lean_box_float(v___x_3705_);
v___x_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v_a_3702_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3662_, v___x_3595_, v___x_3663_, v_options_3596_, v___x_3665_, v___y_3700_, v___f_3661_, v___x_3709_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v___y_3573_ = v___x_3710_;
goto v___jp_3572_;
}
v___jp_3711_:
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3715_, 0, v_a_3714_);
v___y_3700_ = v___y_3712_;
v___y_3701_ = v___y_3713_;
v_a_3702_ = v___x_3715_;
goto v___jp_3699_;
}
v___jp_3716_:
{
if (lean_obj_tag(v___y_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
v_a_3720_ = lean_ctor_get(v___y_3719_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___y_3719_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___y_3719_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___y_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
lean_ctor_set_tag(v___x_3722_, 1);
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
v___y_3700_ = v___y_3717_;
v___y_3701_ = v___y_3718_;
v_a_3702_ = v___x_3725_;
goto v___jp_3699_;
}
}
}
else
{
lean_object* v_a_3728_; 
v_a_3728_ = lean_ctor_get(v___y_3719_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___y_3719_);
v___y_3712_ = v___y_3717_;
v___y_3713_ = v___y_3718_;
v_a_3714_ = v_a_3728_;
goto v___jp_3711_;
}
}
v___jp_3729_:
{
lean_object* v___x_3730_; lean_object* v_a_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3730_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3399_);
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref(v___x_3730_);
v___x_3732_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3733_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3596_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = lean_io_mono_nanos_now();
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc_ref(v___x_3600_);
v___x_3735_ = lean_infer_type(v___x_3600_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; lean_object* v___x_3739_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref(v___x_3735_);
v___x_3737_ = lean_box(0);
v___x_3738_ = 0;
v___x_3739_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3736_, v___x_3737_, v___x_3738_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v_snd_3741_; lean_object* v_fst_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3771_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref(v___x_3739_);
v_snd_3741_ = lean_ctor_get(v_a_3740_, 1);
v_fst_3742_ = lean_ctor_get(v_a_3740_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_a_3740_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3744_ = v_a_3740_;
v_isShared_3745_ = v_isSharedCheck_3771_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_snd_3741_);
lean_inc(v_fst_3742_);
lean_dec(v_a_3740_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3771_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v_snd_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3769_; 
v_snd_3746_ = lean_ctor_get(v_snd_3741_, 1);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_snd_3741_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; 
v_unused_3770_ = lean_ctor_get(v_snd_3741_, 0);
lean_dec(v_unused_3770_);
v___x_3748_ = v_snd_3741_;
v_isShared_3749_ = v_isSharedCheck_3769_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_snd_3746_);
lean_dec(v_snd_3741_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3769_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; 
lean_inc(v_snd_3746_);
lean_inc_ref(v_type_3404_);
v___x_3750_ = l_Lean_Meta_isExprDefEq(v_type_3404_, v_snd_3746_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; uint8_t v___x_3752_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref(v___x_3750_);
v___x_3752_ = lean_unbox(v_a_3751_);
lean_dec(v_a_3751_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
lean_dec(v_fst_3742_);
lean_dec_ref(v___x_3600_);
v___x_3753_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3404_);
v___x_3754_ = l_Lean_indentExpr(v_type_3404_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set_tag(v___x_3748_, 7);
lean_ctor_set(v___x_3748_, 1, v___x_3754_);
lean_ctor_set(v___x_3748_, 0, v___x_3753_);
v___x_3756_ = v___x_3748_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; lean_object* v___x_3759_; 
v___x_3757_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3745_ == 0)
{
lean_ctor_set_tag(v___x_3744_, 7);
lean_ctor_set(v___x_3744_, 1, v___x_3757_);
lean_ctor_set(v___x_3744_, 0, v___x_3756_);
v___x_3759_ = v___x_3744_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v_a_3763_; 
v___x_3760_ = l_Lean_indentExpr(v_snd_3746_);
v___x_3761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3761_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref(v___x_3762_);
v___y_3682_ = v_a_3731_;
v___y_3683_ = v___x_3734_;
v_a_3684_ = v_a_3763_;
goto v___jp_3681_;
}
}
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
lean_del_object(v___x_3748_);
lean_dec(v_snd_3746_);
lean_del_object(v___x_3744_);
v___x_3766_ = lean_box(0);
v___x_3767_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3600_, v_fst_3742_, v___x_3766_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v_fst_3742_);
v___y_3687_ = v_a_3731_;
v___y_3688_ = v___x_3734_;
v___y_3689_ = v___x_3767_;
goto v___jp_3686_;
}
}
else
{
lean_object* v_a_3768_; 
lean_del_object(v___x_3748_);
lean_dec(v_snd_3746_);
lean_del_object(v___x_3744_);
lean_dec(v_fst_3742_);
lean_dec_ref(v___x_3600_);
v_a_3768_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3768_);
lean_dec_ref(v___x_3750_);
v___y_3682_ = v_a_3731_;
v___y_3683_ = v___x_3734_;
v_a_3684_ = v_a_3768_;
goto v___jp_3681_;
}
}
}
}
else
{
lean_object* v_a_3772_; 
lean_dec_ref(v___x_3600_);
v_a_3772_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3772_);
lean_dec_ref(v___x_3739_);
v___y_3682_ = v_a_3731_;
v___y_3683_ = v___x_3734_;
v_a_3684_ = v_a_3772_;
goto v___jp_3681_;
}
}
else
{
lean_dec_ref(v___x_3600_);
v___y_3687_ = v_a_3731_;
v___y_3688_ = v___x_3734_;
v___y_3689_ = v___x_3735_;
goto v___jp_3686_;
}
}
else
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc_ref(v___x_3600_);
v___x_3774_ = lean_infer_type(v___x_3600_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; lean_object* v___x_3778_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = lean_box(0);
v___x_3777_ = 0;
v___x_3778_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3775_, v___x_3776_, v___x_3777_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v_snd_3780_; lean_object* v_fst_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3810_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v_snd_3780_ = lean_ctor_get(v_a_3779_, 1);
v_fst_3781_ = lean_ctor_get(v_a_3779_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_a_3779_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3783_ = v_a_3779_;
v_isShared_3784_ = v_isSharedCheck_3810_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_snd_3780_);
lean_inc(v_fst_3781_);
lean_dec(v_a_3779_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3810_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v_snd_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3808_; 
v_snd_3785_ = lean_ctor_get(v_snd_3780_, 1);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_snd_3780_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v_snd_3780_, 0);
lean_dec(v_unused_3809_);
v___x_3787_ = v_snd_3780_;
v_isShared_3788_ = v_isSharedCheck_3808_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_snd_3785_);
lean_dec(v_snd_3780_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3808_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; 
lean_inc(v_snd_3785_);
lean_inc_ref(v_type_3404_);
v___x_3789_ = l_Lean_Meta_isExprDefEq(v_type_3404_, v_snd_3785_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; uint8_t v___x_3791_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = lean_unbox(v_a_3790_);
lean_dec(v_a_3790_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_dec(v_fst_3781_);
lean_dec_ref(v___x_3600_);
v___x_3792_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3404_);
v___x_3793_ = l_Lean_indentExpr(v_type_3404_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set_tag(v___x_3787_, 7);
lean_ctor_set(v___x_3787_, 1, v___x_3793_);
lean_ctor_set(v___x_3787_, 0, v___x_3792_);
v___x_3795_ = v___x_3787_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3792_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3784_ == 0)
{
lean_ctor_set_tag(v___x_3783_, 7);
lean_ctor_set(v___x_3783_, 1, v___x_3796_);
lean_ctor_set(v___x_3783_, 0, v___x_3795_);
v___x_3798_ = v___x_3783_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v_a_3802_; 
v___x_3799_ = l_Lean_indentExpr(v_snd_3785_);
v___x_3800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3800_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___x_3801_);
v___y_3712_ = v_a_3731_;
v___y_3713_ = v___x_3773_;
v_a_3714_ = v_a_3802_;
goto v___jp_3711_;
}
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
lean_del_object(v___x_3787_);
lean_dec(v_snd_3785_);
lean_del_object(v___x_3783_);
v___x_3805_ = lean_box(0);
v___x_3806_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3600_, v_fst_3781_, v___x_3805_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v_fst_3781_);
v___y_3717_ = v_a_3731_;
v___y_3718_ = v___x_3773_;
v___y_3719_ = v___x_3806_;
goto v___jp_3716_;
}
}
else
{
lean_object* v_a_3807_; 
lean_del_object(v___x_3787_);
lean_dec(v_snd_3785_);
lean_del_object(v___x_3783_);
lean_dec(v_fst_3781_);
lean_dec_ref(v___x_3600_);
v_a_3807_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3789_);
v___y_3712_ = v_a_3731_;
v___y_3713_ = v___x_3773_;
v_a_3714_ = v_a_3807_;
goto v___jp_3711_;
}
}
}
}
else
{
lean_object* v_a_3811_; 
lean_dec_ref(v___x_3600_);
v_a_3811_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3811_);
lean_dec_ref(v___x_3778_);
v___y_3712_ = v_a_3731_;
v___y_3713_ = v___x_3773_;
v_a_3714_ = v_a_3811_;
goto v___jp_3711_;
}
}
else
{
lean_dec_ref(v___x_3600_);
v___y_3717_ = v_a_3731_;
v___y_3718_ = v___x_3773_;
v___y_3719_ = v___x_3774_;
goto v___jp_3716_;
}
}
}
}
}
else
{
lean_object* v_options_3873_; uint8_t v_hasTrace_3874_; 
lean_dec(v_ctorName_3389_);
lean_dec(v_us_3385_);
v_options_3873_ = lean_ctor_get(v___y_3398_, 2);
v_hasTrace_3874_ = lean_ctor_get_uint8(v_options_3873_, sizeof(void*)*1);
if (v_hasTrace_3874_ == 0)
{
lean_object* v_ref_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec_ref(v___f_3391_);
v_ref_3875_ = lean_ctor_get(v___y_3398_, 5);
v___x_3876_ = l_Lean_SourceInfo_fromRef(v_ref_3875_, v_hasTrace_3874_);
v___x_3877_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3878_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7));
lean_inc_n(v___x_3876_, 7);
v___x_3879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3876_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_3881_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_3882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3876_);
lean_ctor_set(v___x_3882_, 1, v___x_3880_);
lean_ctor_set(v___x_3882_, 2, v___x_3881_);
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21));
lean_inc_ref_n(v___x_3882_, 2);
v___x_3884_ = l_Lean_Syntax_node1(v___x_3876_, v___x_3883_, v___x_3882_);
v___x_3885_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23));
v___x_3886_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__24));
v___x_3887_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3876_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = l_Lean_Syntax_node1(v___x_3876_, v___x_3880_, v___x_3887_);
v___x_3889_ = l_Lean_Syntax_node1(v___x_3876_, v___x_3885_, v___x_3888_);
v___x_3890_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11));
v___x_3891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3876_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = l_Lean_Syntax_node6(v___x_3876_, v___x_3877_, v___x_3879_, v___x_3882_, v___x_3884_, v___x_3889_, v___x_3882_, v___x_3891_);
lean_inc_ref(v_type_3404_);
v___x_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3893_, 0, v_type_3404_);
v___x_3894_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3894_, 0, v___x_3892_);
lean_closure_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3894_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v___y_3584_ = v___x_3895_;
goto v___jp_3583_;
}
else
{
lean_object* v_ref_3896_; lean_object* v_inheritedTraceOptions_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v_a_3905_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v_a_3920_; 
v_ref_3896_ = lean_ctor_get(v___y_3398_, 5);
v_inheritedTraceOptions_3897_ = lean_ctor_get(v___y_3398_, 13);
v___x_3898_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3899_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3900_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3897_, v_options_3873_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_4017_; uint8_t v___x_4018_; 
v___x_4017_ = l_Lean_trace_profiler;
v___x_4018_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3873_, v___x_4017_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
lean_dec_ref(v___f_3391_);
v___x_4019_ = l_Lean_SourceInfo_fromRef(v_ref_3896_, v___x_4018_);
v___x_4020_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_4021_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7));
lean_inc_n(v___x_4019_, 7);
v___x_4022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4019_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
v___x_4023_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_4024_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_4025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4019_);
lean_ctor_set(v___x_4025_, 1, v___x_4023_);
lean_ctor_set(v___x_4025_, 2, v___x_4024_);
v___x_4026_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21));
lean_inc_ref_n(v___x_4025_, 2);
v___x_4027_ = l_Lean_Syntax_node1(v___x_4019_, v___x_4026_, v___x_4025_);
v___x_4028_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23));
v___x_4029_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__24));
v___x_4030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4019_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
v___x_4031_ = l_Lean_Syntax_node1(v___x_4019_, v___x_4023_, v___x_4030_);
v___x_4032_ = l_Lean_Syntax_node1(v___x_4019_, v___x_4028_, v___x_4031_);
v___x_4033_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11));
v___x_4034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4019_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = l_Lean_Syntax_node6(v___x_4019_, v___x_4020_, v___x_4022_, v___x_4025_, v___x_4027_, v___x_4032_, v___x_4025_, v___x_4034_);
lean_inc_ref(v_type_3404_);
v___x_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_type_3404_);
v___x_4037_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_4037_, 0, v___x_4035_);
lean_closure_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_4037_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v___y_3584_ = v___x_4038_;
goto v___jp_3583_;
}
else
{
goto v___jp_3929_;
}
}
else
{
goto v___jp_3929_;
}
v___jp_3902_:
{
lean_object* v___x_3906_; double v___x_3907_; double v___x_3908_; double v___x_3909_; double v___x_3910_; double v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3906_ = lean_io_mono_nanos_now();
v___x_3907_ = lean_float_of_nat(v___y_3904_);
v___x_3908_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3909_ = lean_float_div(v___x_3907_, v___x_3908_);
v___x_3910_ = lean_float_of_nat(v___x_3906_);
v___x_3911_ = lean_float_div(v___x_3910_, v___x_3908_);
v___x_3912_ = lean_box_float(v___x_3909_);
v___x_3913_ = lean_box_float(v___x_3911_);
v___x_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3912_);
lean_ctor_set(v___x_3914_, 1, v___x_3913_);
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v_a_3905_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3898_, v___x_3595_, v___x_3899_, v_options_3873_, v___x_3901_, v___y_3903_, v___f_3391_, v___x_3915_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v___y_3584_ = v___x_3916_;
goto v___jp_3583_;
}
v___jp_3917_:
{
lean_object* v___x_3921_; double v___x_3922_; double v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3921_ = lean_io_get_num_heartbeats();
v___x_3922_ = lean_float_of_nat(v___y_3919_);
v___x_3923_ = lean_float_of_nat(v___x_3921_);
v___x_3924_ = lean_box_float(v___x_3922_);
v___x_3925_ = lean_box_float(v___x_3923_);
v___x_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v_a_3920_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3898_, v___x_3595_, v___x_3899_, v_options_3873_, v___x_3901_, v___y_3918_, v___f_3391_, v___x_3927_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
v___y_3584_ = v___x_3928_;
goto v___jp_3583_;
}
v___jp_3929_:
{
lean_object* v___x_3930_; lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_4016_; 
v___x_3930_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3399_);
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_3933_ = v___x_3930_;
v_isShared_3934_ = v_isSharedCheck_4016_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_4016_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3935_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3936_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3873_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3956_; 
v___x_3937_ = lean_io_mono_nanos_now();
v___x_3938_ = l_Lean_SourceInfo_fromRef(v_ref_3896_, v___x_3936_);
v___x_3939_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3940_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7));
lean_inc_n(v___x_3938_, 7);
v___x_3941_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3938_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_3943_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_3944_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3938_);
lean_ctor_set(v___x_3944_, 1, v___x_3942_);
lean_ctor_set(v___x_3944_, 2, v___x_3943_);
v___x_3945_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21));
lean_inc_ref_n(v___x_3944_, 2);
v___x_3946_ = l_Lean_Syntax_node1(v___x_3938_, v___x_3945_, v___x_3944_);
v___x_3947_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23));
v___x_3948_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__24));
v___x_3949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3938_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
v___x_3950_ = l_Lean_Syntax_node1(v___x_3938_, v___x_3942_, v___x_3949_);
v___x_3951_ = l_Lean_Syntax_node1(v___x_3938_, v___x_3947_, v___x_3950_);
v___x_3952_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11));
v___x_3953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3938_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = l_Lean_Syntax_node6(v___x_3938_, v___x_3939_, v___x_3941_, v___x_3944_, v___x_3946_, v___x_3951_, v___x_3944_, v___x_3953_);
lean_inc_ref(v_type_3404_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set_tag(v___x_3933_, 1);
lean_ctor_set(v___x_3933_, 0, v_type_3404_);
v___x_3956_ = v___x_3933_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_type_3404_);
v___x_3956_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3957_, 0, v___x_3954_);
lean_closure_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3957_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3958_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3958_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
lean_ctor_set_tag(v___x_3961_, 1);
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
v___y_3903_ = v_a_3931_;
v___y_3904_ = v___x_3937_;
v_a_3905_ = v___x_3964_;
goto v___jp_3902_;
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
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
lean_ctor_set_tag(v___x_3969_, 0);
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
v___y_3903_ = v_a_3931_;
v___y_3904_ = v___x_3937_;
v_a_3905_ = v___x_3972_;
goto v___jp_3902_;
}
}
}
}
}
else
{
lean_object* v___x_3976_; uint8_t v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
v___x_3976_ = lean_io_get_num_heartbeats();
v___x_3977_ = 0;
v___x_3978_ = l_Lean_SourceInfo_fromRef(v_ref_3896_, v___x_3977_);
v___x_3979_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3980_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7));
lean_inc_n(v___x_3978_, 7);
v___x_3981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3978_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v___x_3982_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_3983_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_3984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3978_);
lean_ctor_set(v___x_3984_, 1, v___x_3982_);
lean_ctor_set(v___x_3984_, 2, v___x_3983_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__21));
lean_inc_ref_n(v___x_3984_, 2);
v___x_3986_ = l_Lean_Syntax_node1(v___x_3978_, v___x_3985_, v___x_3984_);
v___x_3987_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__23));
v___x_3988_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__24));
v___x_3989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3978_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = l_Lean_Syntax_node1(v___x_3978_, v___x_3982_, v___x_3989_);
v___x_3991_ = l_Lean_Syntax_node1(v___x_3978_, v___x_3987_, v___x_3990_);
v___x_3992_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11));
v___x_3993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3978_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = l_Lean_Syntax_node6(v___x_3978_, v___x_3979_, v___x_3981_, v___x_3984_, v___x_3986_, v___x_3991_, v___x_3984_, v___x_3993_);
lean_inc_ref(v_type_3404_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set_tag(v___x_3933_, 1);
lean_ctor_set(v___x_3933_, 0, v_type_3404_);
v___x_3996_ = v___x_3933_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_type_3404_);
v___x_3996_ = v_reuseFailAlloc_4015_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3997_, 0, v___x_3994_);
lean_closure_set(v___x_3997_, 1, v___x_3996_);
v___x_3998_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3997_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
lean_ctor_set_tag(v___x_4001_, 1);
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
v___y_3918_ = v_a_3931_;
v___y_3919_ = v___x_3976_;
v_a_3920_ = v___x_4004_;
goto v___jp_3917_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
v_a_4007_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3998_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3998_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
lean_ctor_set_tag(v___x_4009_, 0);
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
v___y_3918_ = v_a_3931_;
v___y_3919_ = v___x_3976_;
v_a_3920_ = v___x_4012_;
goto v___jp_3917_;
}
}
}
}
}
}
}
}
}
v___jp_3405_:
{
lean_object* v___x_3414_; uint8_t v___x_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; 
v___x_3414_ = l_Array_append___redArg(v_xs_3386_, v___y_3406_);
lean_dec_ref(v___y_3406_);
v___x_3415_ = 0;
v___x_3416_ = 1;
v___x_3417_ = l_Lean_Meta_mkForallFVars(v___x_3414_, v_type_3404_, v___x_3415_, v___y_3407_, v___y_3407_, v___x_3416_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref(v___x_3417_);
v___x_3419_ = l_Lean_Meta_mkLambdaFVars(v___x_3414_, v___y_3409_, v___x_3415_, v___y_3407_, v___x_3415_, v___y_3407_, v___x_3416_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec_ref(v___x_3414_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3429_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3424_, 0, v_a_3420_);
lean_ctor_set(v___x_3424_, 1, v___y_3408_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v_a_3418_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_a_3418_);
lean_dec(v___y_3408_);
v_a_3430_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3419_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3419_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v___x_3414_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
v_a_3438_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3417_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3417_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
v___jp_3446_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___y_3450_);
lean_ctor_set(v___x_3458_, 1, v___y_3457_);
lean_inc(v___y_3454_);
v___x_3459_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3454_, v___x_3458_, v___y_3452_, v___y_3456_, v___y_3447_, v___y_3455_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_dec_ref(v___x_3459_);
v___y_3406_ = v___y_3448_;
v___y_3407_ = v___y_3449_;
v___y_3408_ = v___y_3451_;
v___y_3409_ = v___y_3453_;
v___y_3410_ = v___y_3452_;
v___y_3411_ = v___y_3456_;
v___y_3412_ = v___y_3447_;
v___y_3413_ = v___y_3455_;
goto v___jp_3405_;
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3448_);
lean_dec_ref(v_type_3404_);
lean_dec_ref(v_xs_3386_);
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3459_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3459_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
v___jp_3468_:
{
uint8_t v___x_3480_; 
v___x_3480_ = lean_nat_dec_eq(v___y_3472_, v___y_3479_);
lean_dec(v___y_3479_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec_ref(v_type_3404_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v___x_3481_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3482_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3481_, v___y_3476_, v___y_3470_, v___y_3474_, v___y_3478_, v___y_3469_, v___y_3477_);
return v___x_3482_;
}
else
{
lean_object* v_options_3483_; uint8_t v_hasTrace_3484_; 
v_options_3483_ = lean_ctor_get(v___y_3469_, 2);
v_hasTrace_3484_ = lean_ctor_get_uint8(v_options_3483_, sizeof(void*)*1);
if (v_hasTrace_3484_ == 0)
{
lean_dec(v___y_3472_);
lean_dec(v___x_3387_);
v___y_3406_ = v___y_3471_;
v___y_3407_ = v___x_3480_;
v___y_3408_ = v___y_3473_;
v___y_3409_ = v___y_3475_;
v___y_3410_ = v___y_3474_;
v___y_3411_ = v___y_3478_;
v___y_3412_ = v___y_3469_;
v___y_3413_ = v___y_3477_;
goto v___jp_3405_;
}
else
{
lean_object* v_inheritedTraceOptions_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v_inheritedTraceOptions_3485_ = lean_ctor_get(v___y_3469_, 13);
v___x_3486_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3487_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3488_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3485_, v_options_3483_, v___x_3487_);
if (v___x_3488_ == 0)
{
lean_dec(v___y_3472_);
lean_dec(v___x_3387_);
v___y_3406_ = v___y_3471_;
v___y_3407_ = v___x_3480_;
v___y_3408_ = v___y_3473_;
v___y_3409_ = v___y_3475_;
v___y_3410_ = v___y_3474_;
v___y_3411_ = v___y_3478_;
v___y_3412_ = v___y_3469_;
v___y_3413_ = v___y_3477_;
goto v___jp_3405_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v___x_3489_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3490_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3475_);
v___x_3491_ = l_Lean_inlineExpr(v___y_3475_, v___x_3490_);
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3489_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_nat_dec_eq(v___y_3472_, v___x_3387_);
lean_dec(v___x_3387_);
lean_dec(v___y_3472_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3494_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3471_);
v___x_3495_ = lean_array_to_list(v___y_3471_);
v___x_3496_ = lean_box(0);
v___x_3497_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3495_, v___x_3496_);
v___x_3498_ = l_Lean_MessageData_ofList(v___x_3497_);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3494_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3499_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v___y_3447_ = v___y_3469_;
v___y_3448_ = v___y_3471_;
v___y_3449_ = v___x_3480_;
v___y_3450_ = v___x_3492_;
v___y_3451_ = v___y_3473_;
v___y_3452_ = v___y_3474_;
v___y_3453_ = v___y_3475_;
v___y_3454_ = v___x_3486_;
v___y_3455_ = v___y_3477_;
v___y_3456_ = v___y_3478_;
v___y_3457_ = v___x_3501_;
goto v___jp_3446_;
}
else
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3447_ = v___y_3469_;
v___y_3448_ = v___y_3471_;
v___y_3449_ = v___x_3480_;
v___y_3450_ = v___x_3492_;
v___y_3451_ = v___y_3473_;
v___y_3452_ = v___y_3474_;
v___y_3453_ = v___y_3475_;
v___y_3454_ = v___x_3486_;
v___y_3455_ = v___y_3477_;
v___y_3456_ = v___y_3478_;
v___y_3457_ = v___x_3502_;
goto v___jp_3446_;
}
}
}
}
}
v___jp_3503_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_box(1);
lean_inc_ref(v___y_3508_);
v___x_3513_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3512_, v_localInst2Index_3393_, v___y_3508_);
v___x_3514_ = lean_array_get_size(v___y_3511_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_size_3515_; 
v_size_3515_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_size_3515_);
v___y_3469_ = v___y_3504_;
v___y_3470_ = v___y_3505_;
v___y_3471_ = v___y_3511_;
v___y_3472_ = v___x_3514_;
v___y_3473_ = v___x_3513_;
v___y_3474_ = v___y_3506_;
v___y_3475_ = v___y_3508_;
v___y_3476_ = v___y_3507_;
v___y_3477_ = v___y_3510_;
v___y_3478_ = v___y_3509_;
v___y_3479_ = v_size_3515_;
goto v___jp_3468_;
}
else
{
lean_inc(v___x_3387_);
v___y_3469_ = v___y_3504_;
v___y_3470_ = v___y_3505_;
v___y_3471_ = v___y_3511_;
v___y_3472_ = v___x_3514_;
v___y_3473_ = v___x_3513_;
v___y_3474_ = v___y_3506_;
v___y_3475_ = v___y_3508_;
v___y_3476_ = v___y_3507_;
v___y_3477_ = v___y_3510_;
v___y_3478_ = v___y_3509_;
v___y_3479_ = v___x_3387_;
goto v___jp_3468_;
}
}
v___jp_3516_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3524_ = lean_array_get_size(v_insts_3392_);
v___x_3525_ = lean_mk_empty_array_with_capacity(v___x_3387_);
v___x_3526_ = lean_nat_dec_lt(v___x_3387_, v___x_3524_);
if (v___x_3526_ == 0)
{
lean_dec(v___x_3388_);
v___y_3504_ = v___y_3522_;
v___y_3505_ = v___y_3519_;
v___y_3506_ = v___y_3520_;
v___y_3507_ = v___y_3518_;
v___y_3508_ = v___y_3517_;
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3523_;
v___y_3511_ = v___x_3525_;
goto v___jp_3503_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_visitedExpr_3531_; uint8_t v___x_3532_; 
v___x_3527_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11);
lean_inc(v___x_3387_);
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3387_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
lean_inc_ref(v___x_3525_);
v___x_3529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___x_3388_);
lean_ctor_set(v___x_3529_, 2, v___x_3525_);
lean_inc_ref(v___y_3517_);
v___x_3530_ = l_Lean_collectFVars(v___x_3529_, v___y_3517_);
v_visitedExpr_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc_ref(v_visitedExpr_3531_);
lean_dec_ref(v___x_3530_);
v___x_3532_ = lean_nat_dec_le(v___x_3524_, v___x_3524_);
if (v___x_3532_ == 0)
{
if (v___x_3526_ == 0)
{
lean_dec_ref(v_visitedExpr_3531_);
v___y_3504_ = v___y_3522_;
v___y_3505_ = v___y_3519_;
v___y_3506_ = v___y_3520_;
v___y_3507_ = v___y_3518_;
v___y_3508_ = v___y_3517_;
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3523_;
v___y_3511_ = v___x_3525_;
goto v___jp_3503_;
}
else
{
size_t v___x_3533_; size_t v___x_3534_; lean_object* v___x_3535_; 
v___x_3533_ = ((size_t)0ULL);
v___x_3534_ = lean_usize_of_nat(v___x_3524_);
v___x_3535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3531_, v_insts_3392_, v___x_3533_, v___x_3534_, v___x_3525_);
lean_dec_ref(v_visitedExpr_3531_);
v___y_3504_ = v___y_3522_;
v___y_3505_ = v___y_3519_;
v___y_3506_ = v___y_3520_;
v___y_3507_ = v___y_3518_;
v___y_3508_ = v___y_3517_;
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3523_;
v___y_3511_ = v___x_3535_;
goto v___jp_3503_;
}
}
else
{
size_t v___x_3536_; size_t v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = ((size_t)0ULL);
v___x_3537_ = lean_usize_of_nat(v___x_3524_);
v___x_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3531_, v_insts_3392_, v___x_3536_, v___x_3537_, v___x_3525_);
lean_dec_ref(v_visitedExpr_3531_);
v___y_3504_ = v___y_3522_;
v___y_3505_ = v___y_3519_;
v___y_3506_ = v___y_3520_;
v___y_3507_ = v___y_3518_;
v___y_3508_ = v___y_3517_;
v___y_3509_ = v___y_3521_;
v___y_3510_ = v___y_3523_;
v___y_3511_ = v___x_3538_;
goto v___jp_3503_;
}
}
}
v___jp_3539_:
{
lean_object* v___x_3547_; 
lean_inc_ref(v_val_3540_);
v___x_3547_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v___x_3548_; lean_object* v_a_3549_; uint8_t v___x_3550_; 
lean_dec_ref(v___x_3547_);
v___x_3548_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3540_, v___y_3544_);
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref(v___x_3548_);
v___x_3550_ = l_Lean_Expr_hasMVar(v_a_3549_);
if (v___x_3550_ == 0)
{
v___y_3517_ = v_a_3549_;
v___y_3518_ = v___y_3541_;
v___y_3519_ = v___y_3542_;
v___y_3520_ = v___y_3543_;
v___y_3521_ = v___y_3544_;
v___y_3522_ = v___y_3545_;
v___y_3523_ = v___y_3546_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec_ref(v_type_3404_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v___x_3551_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13);
v___x_3552_ = lean_unsigned_to_nat(30u);
v___x_3553_ = l_Lean_inlineExprTrailing(v_a_3549_, v___x_3552_);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3551_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3554_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec_ref(v_val_3540_);
lean_dec_ref(v_type_3404_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v_a_3564_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3547_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3547_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
v___jp_3572_:
{
if (lean_obj_tag(v___y_3573_) == 0)
{
lean_object* v_a_3574_; 
v_a_3574_ = lean_ctor_get(v___y_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref(v___y_3573_);
v_val_3540_ = v_a_3574_;
v___y_3541_ = v___y_3394_;
v___y_3542_ = v___y_3395_;
v___y_3543_ = v___y_3396_;
v___y_3544_ = v___y_3397_;
v___y_3545_ = v___y_3398_;
v___y_3546_ = v___y_3399_;
goto v___jp_3539_;
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec_ref(v_type_3404_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v_a_3575_ = lean_ctor_get(v___y_3573_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___y_3573_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___y_3573_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___y_3573_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
v___jp_3583_:
{
if (lean_obj_tag(v___y_3584_) == 0)
{
lean_object* v_a_3585_; 
v_a_3585_ = lean_ctor_get(v___y_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref(v___y_3584_);
v_val_3540_ = v_a_3585_;
v___y_3541_ = v___y_3394_;
v___y_3542_ = v___y_3395_;
v___y_3543_ = v___y_3396_;
v___y_3544_ = v___y_3397_;
v___y_3545_ = v___y_3398_;
v___y_3546_ = v___y_3399_;
goto v___jp_3539_;
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec_ref(v_type_3404_);
lean_dec(v_localInst2Index_3393_);
lean_dec(v___x_3388_);
lean_dec(v___x_3387_);
lean_dec_ref(v_xs_3386_);
v_a_3586_ = lean_ctor_get(v___y_3584_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___y_3584_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___y_3584_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___y_3584_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object** _args){
lean_object* v_inductiveTypeName_4039_ = _args[0];
lean_object* v_us_4040_ = _args[1];
lean_object* v_xs_4041_ = _args[2];
lean_object* v___x_4042_ = _args[3];
lean_object* v___x_4043_ = _args[4];
lean_object* v_ctorName_4044_ = _args[5];
lean_object* v___x_4045_ = _args[6];
lean_object* v___f_4046_ = _args[7];
lean_object* v_insts_4047_ = _args[8];
lean_object* v_localInst2Index_4048_ = _args[9];
lean_object* v___y_4049_ = _args[10];
lean_object* v___y_4050_ = _args[11];
lean_object* v___y_4051_ = _args[12];
lean_object* v___y_4052_ = _args[13];
lean_object* v___y_4053_ = _args[14];
lean_object* v___y_4054_ = _args[15];
lean_object* v___y_4055_ = _args[16];
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_4039_, v_us_4040_, v_xs_4041_, v___x_4042_, v___x_4043_, v_ctorName_4044_, v___x_4045_, v___f_4046_, v_insts_4047_, v_localInst2Index_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec_ref(v_insts_4047_);
lean_dec_ref(v___x_4045_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t v_sz_4057_, size_t v_i_4058_, lean_object* v_bs_4059_){
_start:
{
uint8_t v___x_4060_; 
v___x_4060_ = lean_usize_dec_lt(v_i_4058_, v_sz_4057_);
if (v___x_4060_ == 0)
{
return v_bs_4059_;
}
else
{
lean_object* v_v_4061_; lean_object* v___x_4062_; lean_object* v_bs_x27_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; size_t v___x_4068_; size_t v___x_4069_; lean_object* v___x_4070_; 
v_v_4061_ = lean_array_uget(v_bs_4059_, v_i_4058_);
v___x_4062_ = lean_unsigned_to_nat(0u);
v_bs_x27_4063_ = lean_array_uset(v_bs_4059_, v_i_4058_, v___x_4062_);
v___x_4064_ = l_Lean_Expr_fvarId_x21(v_v_4061_);
lean_dec(v_v_4061_);
v___x_4065_ = 1;
v___x_4066_ = lean_box(v___x_4065_);
v___x_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4064_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = ((size_t)1ULL);
v___x_4069_ = lean_usize_add(v_i_4058_, v___x_4068_);
v___x_4070_ = lean_array_uset(v_bs_x27_4063_, v_i_4058_, v___x_4067_);
v_i_4058_ = v___x_4069_;
v_bs_4059_ = v___x_4070_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object* v_sz_4072_, lean_object* v_i_4073_, lean_object* v_bs_4074_){
_start:
{
size_t v_sz_boxed_4075_; size_t v_i_boxed_4076_; lean_object* v_res_4077_; 
v_sz_boxed_4075_ = lean_unbox_usize(v_sz_4072_);
lean_dec(v_sz_4072_);
v_i_boxed_4076_ = lean_unbox_usize(v_i_4073_);
lean_dec(v_i_4073_);
v_res_4077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_boxed_4075_, v_i_boxed_4076_, v_bs_4074_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object* v_k_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v___x_4086_; 
lean_inc(v___y_4080_);
lean_inc_ref(v___y_4079_);
v___x_4086_ = lean_apply_7(v_k_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, lean_box(0));
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object* v_bs_4096_, lean_object* v_k_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v___f_4105_; lean_object* v___x_4106_; 
lean_inc(v___y_4099_);
lean_inc_ref(v___y_4098_);
v___f_4105_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4105_, 0, v_k_4097_);
lean_closure_set(v___f_4105_, 1, v___y_4098_);
lean_closure_set(v___f_4105_, 2, v___y_4099_);
v___x_4106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_4096_, v___f_4105_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4106_) == 0)
{
return v___x_4106_;
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4106_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object* v_bs_4115_, lean_object* v_k_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4115_, v_k_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec_ref(v_bs_4115_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_bs_4125_, lean_object* v_k_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
size_t v_sz_4134_; size_t v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v_sz_4134_ = lean_array_size(v_bs_4125_);
v___x_4135_ = ((size_t)0ULL);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4134_, v___x_4135_, v_bs_4125_);
v___x_4137_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v___x_4136_, v_k_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
lean_dec_ref(v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_bs_4138_, lean_object* v_k_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4138_, v_k_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4148_, lean_object* v_inductiveTypeName_4149_, lean_object* v_us_4150_, lean_object* v___x_4151_, lean_object* v_ctorName_4152_, lean_object* v___f_4153_, uint8_t v_addHypotheses_4154_, lean_object* v_xs_4155_, lean_object* v_x_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___f_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4164_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4155_, 2);
v___x_4165_ = l_Array_toSubarray___redArg(v_xs_4155_, v___x_4164_, v_numParams_4148_);
v___x_4166_ = l_Subarray_copy___redArg(v___x_4165_);
lean_inc_ref(v___x_4166_);
v___f_4167_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 17, 8);
lean_closure_set(v___f_4167_, 0, v_inductiveTypeName_4149_);
lean_closure_set(v___f_4167_, 1, v_us_4150_);
lean_closure_set(v___f_4167_, 2, v_xs_4155_);
lean_closure_set(v___f_4167_, 3, v___x_4164_);
lean_closure_set(v___f_4167_, 4, v___x_4151_);
lean_closure_set(v___f_4167_, 5, v_ctorName_4152_);
lean_closure_set(v___f_4167_, 6, v___x_4166_);
lean_closure_set(v___f_4167_, 7, v___f_4153_);
v___x_4168_ = lean_box(v_addHypotheses_4154_);
v___x_4169_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4169_, 0, v___x_4168_);
lean_closure_set(v___x_4169_, 1, lean_box(0));
lean_closure_set(v___x_4169_, 2, v___x_4166_);
lean_closure_set(v___x_4169_, 3, v___f_4167_);
v___x_4170_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_xs_4155_, v___x_4169_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4171_, lean_object* v_inductiveTypeName_4172_, lean_object* v_us_4173_, lean_object* v___x_4174_, lean_object* v_ctorName_4175_, lean_object* v___f_4176_, lean_object* v_addHypotheses_4177_, lean_object* v_xs_4178_, lean_object* v_x_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
uint8_t v_addHypotheses_boxed_4187_; lean_object* v_res_4188_; 
v_addHypotheses_boxed_4187_ = lean_unbox(v_addHypotheses_4177_);
v_res_4188_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4171_, v_inductiveTypeName_4172_, v_us_4173_, v___x_4174_, v_ctorName_4175_, v___f_4176_, v_addHypotheses_boxed_4187_, v_xs_4178_, v_x_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec_ref(v_x_4179_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4189_, lean_object* v_a_4190_){
_start:
{
if (lean_obj_tag(v_a_4189_) == 0)
{
lean_object* v___x_4191_; 
v___x_4191_ = l_List_reverse___redArg(v_a_4190_);
return v___x_4191_;
}
else
{
lean_object* v_head_4192_; lean_object* v_tail_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4202_; 
v_head_4192_ = lean_ctor_get(v_a_4189_, 0);
v_tail_4193_ = lean_ctor_get(v_a_4189_, 1);
v_isSharedCheck_4202_ = !lean_is_exclusive(v_a_4189_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4195_ = v_a_4189_;
v_isShared_4196_ = v_isSharedCheck_4202_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_tail_4193_);
lean_inc(v_head_4192_);
lean_dec(v_a_4189_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4202_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4197_ = l_Lean_Level_param___override(v_head_4192_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 1, v_a_4190_);
lean_ctor_set(v___x_4195_, 0, v___x_4197_);
v___x_4199_ = v___x_4195_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4197_);
lean_ctor_set(v_reuseFailAlloc_4201_, 1, v_a_4190_);
v___x_4199_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
v_a_4189_ = v_tail_4193_;
v_a_4190_ = v___x_4199_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4204_, lean_object* v_ctorName_4205_, uint8_t v_addHypotheses_4206_, lean_object* v_indVal_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v_toConstantVal_4215_; lean_object* v_numParams_4216_; lean_object* v_levelParams_4217_; lean_object* v_type_4218_; lean_object* v___f_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v_us_4222_; lean_object* v___x_4223_; lean_object* v___f_4224_; uint8_t v___x_4225_; lean_object* v___x_4226_; 
v_toConstantVal_4215_ = lean_ctor_get(v_indVal_4207_, 0);
lean_inc_ref(v_toConstantVal_4215_);
v_numParams_4216_ = lean_ctor_get(v_indVal_4207_, 1);
lean_inc(v_numParams_4216_);
lean_dec_ref(v_indVal_4207_);
v_levelParams_4217_ = lean_ctor_get(v_toConstantVal_4215_, 1);
lean_inc(v_levelParams_4217_);
v_type_4218_ = lean_ctor_get(v_toConstantVal_4215_, 2);
lean_inc_ref(v_type_4218_);
lean_dec_ref(v_toConstantVal_4215_);
v___f_4219_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4220_ = lean_box(1);
v___x_4221_ = lean_box(0);
v_us_4222_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4217_, v___x_4221_);
v___x_4223_ = lean_box(v_addHypotheses_4206_);
v___f_4224_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 16, 7);
lean_closure_set(v___f_4224_, 0, v_numParams_4216_);
lean_closure_set(v___f_4224_, 1, v_inductiveTypeName_4204_);
lean_closure_set(v___f_4224_, 2, v_us_4222_);
lean_closure_set(v___f_4224_, 3, v___x_4220_);
lean_closure_set(v___f_4224_, 4, v_ctorName_4205_);
lean_closure_set(v___f_4224_, 5, v___f_4219_);
lean_closure_set(v___f_4224_, 6, v___x_4223_);
v___x_4225_ = 0;
v___x_4226_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_4218_, v___f_4224_, v___x_4225_, v___x_4225_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4227_, lean_object* v_ctorName_4228_, lean_object* v_addHypotheses_4229_, lean_object* v_indVal_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
uint8_t v_addHypotheses_boxed_4238_; lean_object* v_res_4239_; 
v_addHypotheses_boxed_4238_ = lean_unbox(v_addHypotheses_4229_);
v_res_4239_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4227_, v_ctorName_4228_, v_addHypotheses_boxed_4238_, v_indVal_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_);
lean_dec(v_a_4236_);
lean_dec_ref(v_a_4235_);
lean_dec(v_a_4234_);
lean_dec_ref(v_a_4233_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object* v_00_u03b1_4240_, lean_object* v_bs_4241_, lean_object* v_k_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4241_, v_k_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4251_, lean_object* v_bs_4252_, lean_object* v_k_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(v_00_u03b1_4251_, v_bs_4252_, v_k_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec_ref(v_bs_4252_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_4262_, lean_object* v_bs_4263_, lean_object* v_k_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4263_, v_k_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_4273_, lean_object* v_bs_4274_, lean_object* v_k_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_4273_, v_bs_4274_, v_k_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4284_, lean_object* v_levelParams_4285_, lean_object* v_type_4286_, lean_object* v_value_4287_, lean_object* v_hints_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; uint8_t v___y_4293_; uint8_t v___y_4300_; lean_object* v_env_4303_; uint8_t v___x_4304_; 
v___x_4291_ = lean_st_ref_get(v___y_4289_);
v_env_4303_ = lean_ctor_get(v___x_4291_, 0);
lean_inc_ref_n(v_env_4303_, 2);
lean_dec(v___x_4291_);
v___x_4304_ = l_Lean_Environment_hasUnsafe(v_env_4303_, v_type_4286_);
if (v___x_4304_ == 0)
{
uint8_t v___x_4305_; 
v___x_4305_ = l_Lean_Environment_hasUnsafe(v_env_4303_, v_value_4287_);
v___y_4300_ = v___x_4305_;
goto v___jp_4299_;
}
else
{
lean_dec_ref(v_env_4303_);
v___y_4300_ = v___x_4304_;
goto v___jp_4299_;
}
v___jp_4292_:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
lean_inc(v_name_4284_);
v___x_4294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4294_, 0, v_name_4284_);
lean_ctor_set(v___x_4294_, 1, v_levelParams_4285_);
lean_ctor_set(v___x_4294_, 2, v_type_4286_);
v___x_4295_ = lean_box(0);
v___x_4296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4296_, 0, v_name_4284_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
v___x_4297_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4297_, 0, v___x_4294_);
lean_ctor_set(v___x_4297_, 1, v_value_4287_);
lean_ctor_set(v___x_4297_, 2, v_hints_4288_);
lean_ctor_set(v___x_4297_, 3, v___x_4296_);
lean_ctor_set_uint8(v___x_4297_, sizeof(void*)*4, v___y_4293_);
v___x_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
return v___x_4298_;
}
v___jp_4299_:
{
if (v___y_4300_ == 0)
{
uint8_t v___x_4301_; 
v___x_4301_ = 1;
v___y_4293_ = v___x_4301_;
goto v___jp_4292_;
}
else
{
uint8_t v___x_4302_; 
v___x_4302_ = 0;
v___y_4293_ = v___x_4302_;
goto v___jp_4292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4306_, lean_object* v_levelParams_4307_, lean_object* v_type_4308_, lean_object* v_value_4309_, lean_object* v_hints_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4306_, v_levelParams_4307_, v_type_4308_, v_value_4309_, v_hints_4310_, v___y_4311_);
lean_dec(v___y_4311_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4314_, lean_object* v_levelParams_4315_, lean_object* v_type_4316_, lean_object* v_value_4317_, lean_object* v_hints_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4314_, v_levelParams_4315_, v_type_4316_, v_value_4317_, v_hints_4318_, v___y_4324_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4327_, lean_object* v_levelParams_4328_, lean_object* v_type_4329_, lean_object* v_value_4330_, lean_object* v_hints_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4327_, v_levelParams_4328_, v_type_4329_, v_value_4330_, v_hints_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object* v___y_4340_, uint8_t v_isExporting_4341_, lean_object* v___x_4342_, lean_object* v___y_4343_, lean_object* v___x_4344_, lean_object* v_a_x3f_4345_){
_start:
{
lean_object* v___x_4347_; lean_object* v_env_4348_; lean_object* v_nextMacroScope_4349_; lean_object* v_ngen_4350_; lean_object* v_auxDeclNGen_4351_; lean_object* v_traceState_4352_; lean_object* v_messages_4353_; lean_object* v_infoState_4354_; lean_object* v_snapshotTasks_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4380_; 
v___x_4347_ = lean_st_ref_take(v___y_4340_);
v_env_4348_ = lean_ctor_get(v___x_4347_, 0);
v_nextMacroScope_4349_ = lean_ctor_get(v___x_4347_, 1);
v_ngen_4350_ = lean_ctor_get(v___x_4347_, 2);
v_auxDeclNGen_4351_ = lean_ctor_get(v___x_4347_, 3);
v_traceState_4352_ = lean_ctor_get(v___x_4347_, 4);
v_messages_4353_ = lean_ctor_get(v___x_4347_, 6);
v_infoState_4354_ = lean_ctor_get(v___x_4347_, 7);
v_snapshotTasks_4355_ = lean_ctor_get(v___x_4347_, 8);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4380_ == 0)
{
lean_object* v_unused_4381_; 
v_unused_4381_ = lean_ctor_get(v___x_4347_, 5);
lean_dec(v_unused_4381_);
v___x_4357_ = v___x_4347_;
v_isShared_4358_ = v_isSharedCheck_4380_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_snapshotTasks_4355_);
lean_inc(v_infoState_4354_);
lean_inc(v_messages_4353_);
lean_inc(v_traceState_4352_);
lean_inc(v_auxDeclNGen_4351_);
lean_inc(v_ngen_4350_);
lean_inc(v_nextMacroScope_4349_);
lean_inc(v_env_4348_);
lean_dec(v___x_4347_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4380_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4361_; 
v___x_4359_ = l_Lean_Environment_setExporting(v_env_4348_, v_isExporting_4341_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 5, v___x_4342_);
lean_ctor_set(v___x_4357_, 0, v___x_4359_);
v___x_4361_ = v___x_4357_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_nextMacroScope_4349_);
lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_ngen_4350_);
lean_ctor_set(v_reuseFailAlloc_4379_, 3, v_auxDeclNGen_4351_);
lean_ctor_set(v_reuseFailAlloc_4379_, 4, v_traceState_4352_);
lean_ctor_set(v_reuseFailAlloc_4379_, 5, v___x_4342_);
lean_ctor_set(v_reuseFailAlloc_4379_, 6, v_messages_4353_);
lean_ctor_set(v_reuseFailAlloc_4379_, 7, v_infoState_4354_);
lean_ctor_set(v_reuseFailAlloc_4379_, 8, v_snapshotTasks_4355_);
v___x_4361_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v_mctx_4364_; lean_object* v_zetaDeltaFVarIds_4365_; lean_object* v_postponed_4366_; lean_object* v_diag_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4377_; 
v___x_4362_ = lean_st_ref_set(v___y_4340_, v___x_4361_);
v___x_4363_ = lean_st_ref_take(v___y_4343_);
v_mctx_4364_ = lean_ctor_get(v___x_4363_, 0);
v_zetaDeltaFVarIds_4365_ = lean_ctor_get(v___x_4363_, 2);
v_postponed_4366_ = lean_ctor_get(v___x_4363_, 3);
v_diag_4367_ = lean_ctor_get(v___x_4363_, 4);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4377_ == 0)
{
lean_object* v_unused_4378_; 
v_unused_4378_ = lean_ctor_get(v___x_4363_, 1);
lean_dec(v_unused_4378_);
v___x_4369_ = v___x_4363_;
v_isShared_4370_ = v_isSharedCheck_4377_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_diag_4367_);
lean_inc(v_postponed_4366_);
lean_inc(v_zetaDeltaFVarIds_4365_);
lean_inc(v_mctx_4364_);
lean_dec(v___x_4363_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4377_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 1, v___x_4344_);
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_mctx_4364_);
lean_ctor_set(v_reuseFailAlloc_4376_, 1, v___x_4344_);
lean_ctor_set(v_reuseFailAlloc_4376_, 2, v_zetaDeltaFVarIds_4365_);
lean_ctor_set(v_reuseFailAlloc_4376_, 3, v_postponed_4366_);
lean_ctor_set(v_reuseFailAlloc_4376_, 4, v_diag_4367_);
v___x_4372_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4373_ = lean_st_ref_set(v___y_4343_, v___x_4372_);
v___x_4374_ = lean_box(0);
v___x_4375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
return v___x_4375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object* v___y_4382_, lean_object* v_isExporting_4383_, lean_object* v___x_4384_, lean_object* v___y_4385_, lean_object* v___x_4386_, lean_object* v_a_x3f_4387_, lean_object* v___y_4388_){
_start:
{
uint8_t v_isExporting_boxed_4389_; lean_object* v_res_4390_; 
v_isExporting_boxed_4389_ = lean_unbox(v_isExporting_4383_);
v_res_4390_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4382_, v_isExporting_boxed_4389_, v___x_4384_, v___y_4385_, v___x_4386_, v_a_x3f_4387_);
lean_dec(v_a_x3f_4387_);
lean_dec(v___y_4385_);
lean_dec(v___y_4382_);
return v_res_4390_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4391_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4392_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
return v___x_4393_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4394_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
return v___x_4395_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4397_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
lean_ctor_set(v___x_4397_, 2, v___x_4396_);
lean_ctor_set(v___x_4397_, 3, v___x_4396_);
lean_ctor_set(v___x_4397_, 4, v___x_4396_);
lean_ctor_set(v___x_4397_, 5, v___x_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object* v_x_4398_, uint8_t v_isExporting_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v___x_4407_; lean_object* v_env_4408_; uint8_t v_isExporting_4409_; lean_object* v___x_4410_; lean_object* v_env_4411_; lean_object* v_nextMacroScope_4412_; lean_object* v_ngen_4413_; lean_object* v_auxDeclNGen_4414_; lean_object* v_traceState_4415_; lean_object* v_messages_4416_; lean_object* v_infoState_4417_; lean_object* v_snapshotTasks_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4472_; 
v___x_4407_ = lean_st_ref_get(v___y_4405_);
v_env_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc_ref(v_env_4408_);
lean_dec(v___x_4407_);
v_isExporting_4409_ = lean_ctor_get_uint8(v_env_4408_, sizeof(void*)*8);
lean_dec_ref(v_env_4408_);
v___x_4410_ = lean_st_ref_take(v___y_4405_);
v_env_4411_ = lean_ctor_get(v___x_4410_, 0);
v_nextMacroScope_4412_ = lean_ctor_get(v___x_4410_, 1);
v_ngen_4413_ = lean_ctor_get(v___x_4410_, 2);
v_auxDeclNGen_4414_ = lean_ctor_get(v___x_4410_, 3);
v_traceState_4415_ = lean_ctor_get(v___x_4410_, 4);
v_messages_4416_ = lean_ctor_get(v___x_4410_, 6);
v_infoState_4417_ = lean_ctor_get(v___x_4410_, 7);
v_snapshotTasks_4418_ = lean_ctor_get(v___x_4410_, 8);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; 
v_unused_4473_ = lean_ctor_get(v___x_4410_, 5);
lean_dec(v_unused_4473_);
v___x_4420_ = v___x_4410_;
v_isShared_4421_ = v_isSharedCheck_4472_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_snapshotTasks_4418_);
lean_inc(v_infoState_4417_);
lean_inc(v_messages_4416_);
lean_inc(v_traceState_4415_);
lean_inc(v_auxDeclNGen_4414_);
lean_inc(v_ngen_4413_);
lean_inc(v_nextMacroScope_4412_);
lean_inc(v_env_4411_);
lean_dec(v___x_4410_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4472_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4425_; 
v___x_4422_ = l_Lean_Environment_setExporting(v_env_4411_, v_isExporting_4399_);
v___x_4423_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 5, v___x_4423_);
lean_ctor_set(v___x_4420_, 0, v___x_4422_);
v___x_4425_ = v___x_4420_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_nextMacroScope_4412_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_ngen_4413_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v_auxDeclNGen_4414_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v_traceState_4415_);
lean_ctor_set(v_reuseFailAlloc_4471_, 5, v___x_4423_);
lean_ctor_set(v_reuseFailAlloc_4471_, 6, v_messages_4416_);
lean_ctor_set(v_reuseFailAlloc_4471_, 7, v_infoState_4417_);
lean_ctor_set(v_reuseFailAlloc_4471_, 8, v_snapshotTasks_4418_);
v___x_4425_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v_mctx_4428_; lean_object* v_zetaDeltaFVarIds_4429_; lean_object* v_postponed_4430_; lean_object* v_diag_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4469_; 
v___x_4426_ = lean_st_ref_set(v___y_4405_, v___x_4425_);
v___x_4427_ = lean_st_ref_take(v___y_4403_);
v_mctx_4428_ = lean_ctor_get(v___x_4427_, 0);
v_zetaDeltaFVarIds_4429_ = lean_ctor_get(v___x_4427_, 2);
v_postponed_4430_ = lean_ctor_get(v___x_4427_, 3);
v_diag_4431_ = lean_ctor_get(v___x_4427_, 4);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4469_ == 0)
{
lean_object* v_unused_4470_; 
v_unused_4470_ = lean_ctor_get(v___x_4427_, 1);
lean_dec(v_unused_4470_);
v___x_4433_ = v___x_4427_;
v_isShared_4434_ = v_isSharedCheck_4469_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_diag_4431_);
lean_inc(v_postponed_4430_);
lean_inc(v_zetaDeltaFVarIds_4429_);
lean_inc(v_mctx_4428_);
lean_dec(v___x_4427_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4469_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4435_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 1, v___x_4435_);
v___x_4437_ = v___x_4433_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_mctx_4428_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v___x_4435_);
lean_ctor_set(v_reuseFailAlloc_4468_, 2, v_zetaDeltaFVarIds_4429_);
lean_ctor_set(v_reuseFailAlloc_4468_, 3, v_postponed_4430_);
lean_ctor_set(v_reuseFailAlloc_4468_, 4, v_diag_4431_);
v___x_4437_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4438_; lean_object* v_r_4439_; 
v___x_4438_ = lean_st_ref_set(v___y_4403_, v___x_4437_);
lean_inc(v___y_4405_);
lean_inc_ref(v___y_4404_);
lean_inc(v___y_4403_);
lean_inc_ref(v___y_4402_);
lean_inc(v___y_4401_);
lean_inc_ref(v___y_4400_);
v_r_4439_ = lean_apply_7(v_x_4398_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, lean_box(0));
if (lean_obj_tag(v_r_4439_) == 0)
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4456_; 
v_a_4440_ = lean_ctor_get(v_r_4439_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_r_4439_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4442_ = v_r_4439_;
v_isShared_4443_ = v_isSharedCheck_4456_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v_r_4439_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4456_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
lean_inc(v_a_4440_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set_tag(v___x_4442_, 1);
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
v___x_4446_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4405_, v_isExporting_4409_, v___x_4423_, v___y_4403_, v___x_4435_, v___x_4445_);
lean_dec_ref(v___x_4445_);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4453_ == 0)
{
lean_object* v_unused_4454_; 
v_unused_4454_ = lean_ctor_get(v___x_4446_, 0);
lean_dec(v_unused_4454_);
v___x_4448_ = v___x_4446_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_dec(v___x_4446_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 0, v_a_4440_);
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4440_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
v_a_4457_ = lean_ctor_get(v_r_4439_, 0);
lean_inc(v_a_4457_);
lean_dec_ref(v_r_4439_);
v___x_4458_ = lean_box(0);
v___x_4459_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4405_, v_isExporting_4409_, v___x_4423_, v___y_4403_, v___x_4435_, v___x_4458_);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4466_ == 0)
{
lean_object* v_unused_4467_; 
v_unused_4467_ = lean_ctor_get(v___x_4459_, 0);
lean_dec(v_unused_4467_);
v___x_4461_ = v___x_4459_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_dec(v___x_4459_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
lean_ctor_set_tag(v___x_4461_, 1);
lean_ctor_set(v___x_4461_, 0, v_a_4457_);
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4457_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v_x_4474_, lean_object* v_isExporting_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
uint8_t v_isExporting_boxed_4483_; lean_object* v_res_4484_; 
v_isExporting_boxed_4483_ = lean_unbox(v_isExporting_4475_);
v_res_4484_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4474_, v_isExporting_boxed_4483_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b1_4485_, lean_object* v_x_4486_, uint8_t v_isExporting_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4486_, v_isExporting_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object* v_00_u03b1_4496_, lean_object* v_x_4497_, lean_object* v_isExporting_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
uint8_t v_isExporting_boxed_4506_; lean_object* v_res_4507_; 
v_isExporting_boxed_4506_ = lean_unbox(v_isExporting_4498_);
v_res_4507_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(v_00_u03b1_4496_, v_x_4497_, v_isExporting_boxed_4506_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4518_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
return v___x_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
return v_res_4528_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4531_ = l_Lean_stringToMessageData(v___x_4530_);
return v___x_4531_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4534_ = l_Lean_stringToMessageData(v___x_4533_);
return v___x_4534_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4));
v___x_4537_ = l_Lean_stringToMessageData(v___x_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4538_, lean_object* v___x_4539_, lean_object* v_inductiveTypeName_4540_, uint8_t v___x_4541_, lean_object* v___x_4542_, lean_object* v_ctorName_4543_, uint8_t v_addHypotheses_4544_, lean_object* v___f_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___y_4554_; lean_object* v___x_4557_; 
lean_inc(v_inductiveTypeName_4540_);
v___x_4557_ = l_Lean_Elab_Deriving_mkContext(v___x_4538_, v___x_4539_, v_inductiveTypeName_4540_, v___x_4541_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v_options_4559_; lean_object* v_currNamespace_4560_; lean_object* v_inheritedTraceOptions_4561_; lean_object* v___x_4562_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
lean_dec_ref(v___x_4557_);
v_options_4559_ = lean_ctor_get(v___y_4550_, 2);
v_currNamespace_4560_ = lean_ctor_get(v___y_4550_, 6);
v_inheritedTraceOptions_4561_ = lean_ctor_get(v___y_4550_, 13);
lean_inc(v_inductiveTypeName_4540_);
v___x_4562_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4540_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; lean_object* v_instName_4564_; lean_object* v_auxFunNames_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; uint8_t v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4646_; uint8_t v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v_a_4668_; lean_object* v___y_4739_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc_n(v_a_4563_, 2);
lean_dec_ref(v___x_4562_);
v_instName_4564_ = lean_ctor_get(v_a_4558_, 0);
lean_inc(v_instName_4564_);
v_auxFunNames_4565_ = lean_ctor_get(v_a_4558_, 2);
lean_inc_ref(v_auxFunNames_4565_);
lean_dec(v_a_4558_);
v___x_4566_ = lean_unsigned_to_nat(0u);
v___x_4567_ = lean_array_get(v___x_4542_, v_auxFunNames_4565_, v___x_4566_);
lean_dec_ref(v_auxFunNames_4565_);
lean_inc(v_currNamespace_4560_);
v___x_4568_ = l_Lean_Name_append(v_currNamespace_4560_, v___x_4567_);
v___x_4758_ = lean_box(v_addHypotheses_4544_);
lean_inc(v_inductiveTypeName_4540_);
v___x_4759_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4759_, 0, v_inductiveTypeName_4540_);
lean_closure_set(v___x_4759_, 1, v_ctorName_4543_);
lean_closure_set(v___x_4759_, 2, v___x_4758_);
lean_closure_set(v___x_4759_, 3, v_a_4563_);
lean_inc(v___x_4568_);
v___x_4760_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4568_, v___x_4759_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; 
lean_dec_ref(v___f_4545_);
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref(v___x_4760_);
v_a_4668_ = v_a_4761_;
goto v___jp_4667_;
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4794_; 
v_a_4762_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4764_ = v___x_4760_;
v_isShared_4765_ = v_isSharedCheck_4794_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4760_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4794_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
uint8_t v___y_4770_; uint8_t v___x_4792_; 
v___x_4792_ = l_Lean_Exception_isInterrupt(v_a_4762_);
if (v___x_4792_ == 0)
{
uint8_t v___x_4793_; 
lean_inc(v_a_4762_);
v___x_4793_ = l_Lean_Exception_isRuntime(v_a_4762_);
v___y_4770_ = v___x_4793_;
goto v___jp_4769_;
}
else
{
v___y_4770_ = v___x_4792_;
goto v___jp_4769_;
}
v___jp_4766_:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = lean_box(0);
lean_inc(v___y_4551_);
lean_inc_ref(v___y_4550_);
lean_inc(v___y_4549_);
lean_inc_ref(v___y_4548_);
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4546_);
v___x_4768_ = lean_apply_8(v___f_4545_, v___x_4767_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, lean_box(0));
v___y_4739_ = v___x_4768_;
goto v___jp_4738_;
}
v___jp_4769_:
{
if (v___y_4770_ == 0)
{
uint8_t v_hasTrace_4771_; 
lean_del_object(v___x_4764_);
v_hasTrace_4771_ = lean_ctor_get_uint8(v_options_4559_, sizeof(void*)*1);
if (v_hasTrace_4771_ == 0)
{
lean_dec(v_a_4762_);
goto v___jp_4766_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; 
v___x_4772_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4773_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4561_, v_options_4559_, v___x_4773_);
if (v___x_4774_ == 0)
{
lean_dec(v_a_4762_);
goto v___jp_4766_;
}
else
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4775_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
v___x_4776_ = l_Lean_Exception_toMessageData(v_a_4762_);
v___x_4777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4775_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
v___x_4778_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4772_, v___x_4777_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; lean_object* v___x_4780_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref(v___x_4778_);
lean_inc(v___y_4551_);
lean_inc_ref(v___y_4550_);
lean_inc(v___y_4549_);
lean_inc_ref(v___y_4548_);
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4546_);
v___x_4780_ = lean_apply_8(v___f_4545_, v_a_4779_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, lean_box(0));
v___y_4739_ = v___x_4780_;
goto v___jp_4738_;
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4788_; 
lean_dec(v___x_4568_);
lean_dec(v_instName_4564_);
lean_dec(v_a_4563_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec_ref(v___f_4545_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4781_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4783_ = v___x_4778_;
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4778_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
}
else
{
lean_object* v___x_4790_; 
lean_dec(v___x_4568_);
lean_dec(v_instName_4564_);
lean_dec(v_a_4563_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec_ref(v___f_4545_);
lean_dec(v_inductiveTypeName_4540_);
if (v_isShared_4765_ == 0)
{
v___x_4790_ = v___x_4764_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4762_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
}
v___jp_4569_:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4578_ = lean_mk_syntax_ident(v_instName_4564_);
v___x_4579_ = l_Lean_mkCIdent(v___x_4568_);
v___x_4580_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4540_, v___x_4578_, v___y_4571_, v___x_4579_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_options_4581_; uint8_t v_hasTrace_4582_; 
v_options_4581_ = lean_ctor_get(v___y_4576_, 2);
v_hasTrace_4582_ = lean_ctor_get_uint8(v_options_4581_, sizeof(void*)*1);
if (v_hasTrace_4582_ == 0)
{
lean_object* v_a_4583_; 
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4570_);
v_a_4583_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4583_);
lean_dec_ref(v___x_4580_);
v___y_4554_ = v_a_4583_;
goto v___jp_4553_;
}
else
{
lean_object* v_a_4584_; lean_object* v_inheritedTraceOptions_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; uint8_t v___x_4588_; 
v_a_4584_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4584_);
lean_dec_ref(v___x_4580_);
v_inheritedTraceOptions_4585_ = lean_ctor_get(v___y_4576_, 13);
v___x_4586_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4570_);
v___x_4587_ = l_Lean_Name_append(v___x_4586_, v___y_4570_);
v___x_4588_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4585_, v_options_4581_, v___x_4587_);
lean_dec(v___x_4587_);
if (v___x_4588_ == 0)
{
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4570_);
v___y_4554_ = v_a_4584_;
goto v___jp_4553_;
}
else
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4589_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4584_);
v___x_4590_ = l_Lean_MessageData_ofSyntax(v_a_4584_);
v___x_4591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4589_);
lean_ctor_set(v___x_4591_, 1, v___x_4590_);
v___x_4592_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4570_, v___x_4591_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_dec_ref(v___x_4592_);
v___y_4554_ = v_a_4584_;
goto v___jp_4553_;
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec(v_a_4584_);
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4592_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4592_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
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
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4570_);
v_a_4601_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4580_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4580_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
v___jp_4609_:
{
lean_object* v___x_4618_; 
lean_inc(v___x_4568_);
v___x_4618_ = l_Lean_enableRealizationsForConst(v___x_4568_, v___y_4616_, v___y_4617_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_options_4619_; lean_object* v_inheritedTraceOptions_4620_; uint8_t v_hasTrace_4621_; lean_object* v___x_4622_; 
lean_dec_ref(v___x_4618_);
v_options_4619_ = lean_ctor_get(v___y_4616_, 2);
v_inheritedTraceOptions_4620_ = lean_ctor_get(v___y_4616_, 13);
v_hasTrace_4621_ = lean_ctor_get_uint8(v_options_4619_, sizeof(void*)*1);
v___x_4622_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4621_ == 0)
{
v___y_4570_ = v___x_4622_;
v___y_4571_ = v___y_4611_;
v___y_4572_ = v___y_4612_;
v___y_4573_ = v___y_4613_;
v___y_4574_ = v___y_4614_;
v___y_4575_ = v___y_4615_;
v___y_4576_ = v___y_4616_;
v___y_4577_ = v___y_4617_;
goto v___jp_4569_;
}
else
{
lean_object* v___x_4623_; uint8_t v___x_4624_; 
v___x_4623_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4624_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4620_, v_options_4619_, v___x_4623_);
if (v___x_4624_ == 0)
{
v___y_4570_ = v___x_4622_;
v___y_4571_ = v___y_4611_;
v___y_4572_ = v___y_4612_;
v___y_4573_ = v___y_4613_;
v___y_4574_ = v___y_4614_;
v___y_4575_ = v___y_4615_;
v___y_4576_ = v___y_4616_;
v___y_4577_ = v___y_4617_;
goto v___jp_4569_;
}
else
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4625_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4568_);
v___x_4626_ = l_Lean_MessageData_ofConstName(v___x_4568_, v___y_4610_);
v___x_4627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4625_);
lean_ctor_set(v___x_4627_, 1, v___x_4626_);
v___x_4628_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4622_, v___x_4627_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_dec_ref(v___x_4628_);
v___y_4570_ = v___x_4622_;
v___y_4571_ = v___y_4611_;
v___y_4572_ = v___y_4612_;
v___y_4573_ = v___y_4613_;
v___y_4574_ = v___y_4614_;
v___y_4575_ = v___y_4615_;
v___y_4576_ = v___y_4616_;
v___y_4577_ = v___y_4617_;
goto v___jp_4569_;
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec(v___x_4568_);
lean_dec(v_instName_4564_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4628_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4628_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec(v___x_4568_);
lean_dec(v_instName_4564_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4637_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4618_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4618_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
v___jp_4645_:
{
uint8_t v_isNoncomputableSection_4654_; 
v_isNoncomputableSection_4654_ = lean_ctor_get_uint8(v___y_4648_, sizeof(void*)*8 + 4);
if (v_isNoncomputableSection_4654_ == 0)
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4655_ = lean_unsigned_to_nat(1u);
v___x_4656_ = lean_mk_empty_array_with_capacity(v___x_4655_);
lean_inc(v___x_4568_);
v___x_4657_ = lean_array_push(v___x_4656_, v___x_4568_);
v___x_4658_ = l_Lean_compileDecls(v___x_4657_, v___x_4541_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_dec_ref(v___x_4658_);
v___y_4610_ = v___y_4647_;
v___y_4611_ = v___y_4646_;
v___y_4612_ = v___y_4648_;
v___y_4613_ = v___y_4649_;
v___y_4614_ = v___y_4650_;
v___y_4615_ = v___y_4651_;
v___y_4616_ = v___y_4652_;
v___y_4617_ = v___y_4653_;
goto v___jp_4609_;
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec(v___y_4646_);
lean_dec(v___x_4568_);
lean_dec(v_instName_4564_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
else
{
v___y_4610_ = v___y_4647_;
v___y_4611_ = v___y_4646_;
v___y_4612_ = v___y_4648_;
v___y_4613_ = v___y_4649_;
v___y_4614_ = v___y_4650_;
v___y_4615_ = v___y_4651_;
v___y_4616_ = v___y_4652_;
v___y_4617_ = v___y_4653_;
goto v___jp_4609_;
}
}
v___jp_4667_:
{
lean_object* v_snd_4669_; lean_object* v_fst_4670_; lean_object* v_fst_4671_; lean_object* v_snd_4672_; lean_object* v___x_4673_; lean_object* v_toConstantVal_4674_; lean_object* v_env_4675_; lean_object* v_levelParams_4676_; uint32_t v___x_4677_; uint32_t v___x_4678_; uint32_t v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4737_; 
v_snd_4669_ = lean_ctor_get(v_a_4668_, 1);
lean_inc(v_snd_4669_);
v_fst_4670_ = lean_ctor_get(v_a_4668_, 0);
lean_inc(v_fst_4670_);
lean_dec_ref(v_a_4668_);
v_fst_4671_ = lean_ctor_get(v_snd_4669_, 0);
lean_inc_n(v_fst_4671_, 2);
v_snd_4672_ = lean_ctor_get(v_snd_4669_, 1);
lean_inc(v_snd_4672_);
lean_dec(v_snd_4669_);
v___x_4673_ = lean_st_ref_get(v___y_4551_);
v_toConstantVal_4674_ = lean_ctor_get(v_a_4563_, 0);
lean_inc_ref(v_toConstantVal_4674_);
lean_dec(v_a_4563_);
v_env_4675_ = lean_ctor_get(v___x_4673_, 0);
lean_inc_ref(v_env_4675_);
lean_dec(v___x_4673_);
v_levelParams_4676_ = lean_ctor_get(v_toConstantVal_4674_, 1);
lean_inc(v_levelParams_4676_);
lean_dec_ref(v_toConstantVal_4674_);
v___x_4677_ = l_Lean_getMaxHeight(v_env_4675_, v_fst_4671_);
v___x_4678_ = 1;
v___x_4679_ = lean_uint32_add(v___x_4677_, v___x_4678_);
v___x_4680_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4680_, 0, v___x_4679_);
lean_inc(v___x_4568_);
v___x_4681_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4568_, v_levelParams_4676_, v_fst_4670_, v_fst_4671_, v___x_4680_, v___y_4551_);
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4737_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4737_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
lean_ctor_set_tag(v___x_4684_, 1);
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
uint8_t v___x_4688_; lean_object* v___x_4689_; 
v___x_4688_ = 0;
v___x_4689_ = l_Lean_addDecl(v___x_4687_, v___x_4688_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v___x_4690_; lean_object* v_env_4691_; uint8_t v___x_4692_; 
lean_dec_ref(v___x_4689_);
v___x_4690_ = lean_st_ref_get(v___y_4551_);
v_env_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc_ref(v_env_4691_);
lean_dec(v___x_4690_);
lean_inc(v_inductiveTypeName_4540_);
v___x_4692_ = l_Lean_isMarkedMeta(v_env_4691_, v_inductiveTypeName_4540_);
if (v___x_4692_ == 0)
{
v___y_4646_ = v_snd_4672_;
v___y_4647_ = v___x_4688_;
v___y_4648_ = v___y_4546_;
v___y_4649_ = v___y_4547_;
v___y_4650_ = v___y_4548_;
v___y_4651_ = v___y_4549_;
v___y_4652_ = v___y_4550_;
v___y_4653_ = v___y_4551_;
goto v___jp_4645_;
}
else
{
lean_object* v___x_4693_; lean_object* v_env_4694_; lean_object* v_nextMacroScope_4695_; lean_object* v_ngen_4696_; lean_object* v_auxDeclNGen_4697_; lean_object* v_traceState_4698_; lean_object* v_messages_4699_; lean_object* v_infoState_4700_; lean_object* v_snapshotTasks_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4726_; 
v___x_4693_ = lean_st_ref_take(v___y_4551_);
v_env_4694_ = lean_ctor_get(v___x_4693_, 0);
v_nextMacroScope_4695_ = lean_ctor_get(v___x_4693_, 1);
v_ngen_4696_ = lean_ctor_get(v___x_4693_, 2);
v_auxDeclNGen_4697_ = lean_ctor_get(v___x_4693_, 3);
v_traceState_4698_ = lean_ctor_get(v___x_4693_, 4);
v_messages_4699_ = lean_ctor_get(v___x_4693_, 6);
v_infoState_4700_ = lean_ctor_get(v___x_4693_, 7);
v_snapshotTasks_4701_ = lean_ctor_get(v___x_4693_, 8);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4726_ == 0)
{
lean_object* v_unused_4727_; 
v_unused_4727_ = lean_ctor_get(v___x_4693_, 5);
lean_dec(v_unused_4727_);
v___x_4703_ = v___x_4693_;
v_isShared_4704_ = v_isSharedCheck_4726_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_snapshotTasks_4701_);
lean_inc(v_infoState_4700_);
lean_inc(v_messages_4699_);
lean_inc(v_traceState_4698_);
lean_inc(v_auxDeclNGen_4697_);
lean_inc(v_ngen_4696_);
lean_inc(v_nextMacroScope_4695_);
lean_inc(v_env_4694_);
lean_dec(v___x_4693_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4726_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4708_; 
lean_inc(v___x_4568_);
v___x_4705_ = l_Lean_markMeta(v_env_4694_, v___x_4568_);
v___x_4706_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 5, v___x_4706_);
lean_ctor_set(v___x_4703_, 0, v___x_4705_);
v___x_4708_ = v___x_4703_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4705_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_nextMacroScope_4695_);
lean_ctor_set(v_reuseFailAlloc_4725_, 2, v_ngen_4696_);
lean_ctor_set(v_reuseFailAlloc_4725_, 3, v_auxDeclNGen_4697_);
lean_ctor_set(v_reuseFailAlloc_4725_, 4, v_traceState_4698_);
lean_ctor_set(v_reuseFailAlloc_4725_, 5, v___x_4706_);
lean_ctor_set(v_reuseFailAlloc_4725_, 6, v_messages_4699_);
lean_ctor_set(v_reuseFailAlloc_4725_, 7, v_infoState_4700_);
lean_ctor_set(v_reuseFailAlloc_4725_, 8, v_snapshotTasks_4701_);
v___x_4708_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v_mctx_4711_; lean_object* v_zetaDeltaFVarIds_4712_; lean_object* v_postponed_4713_; lean_object* v_diag_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4723_; 
v___x_4709_ = lean_st_ref_set(v___y_4551_, v___x_4708_);
v___x_4710_ = lean_st_ref_take(v___y_4549_);
v_mctx_4711_ = lean_ctor_get(v___x_4710_, 0);
v_zetaDeltaFVarIds_4712_ = lean_ctor_get(v___x_4710_, 2);
v_postponed_4713_ = lean_ctor_get(v___x_4710_, 3);
v_diag_4714_ = lean_ctor_get(v___x_4710_, 4);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4723_ == 0)
{
lean_object* v_unused_4724_; 
v_unused_4724_ = lean_ctor_get(v___x_4710_, 1);
lean_dec(v_unused_4724_);
v___x_4716_ = v___x_4710_;
v_isShared_4717_ = v_isSharedCheck_4723_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_diag_4714_);
lean_inc(v_postponed_4713_);
lean_inc(v_zetaDeltaFVarIds_4712_);
lean_inc(v_mctx_4711_);
lean_dec(v___x_4710_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4723_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4718_; lean_object* v___x_4720_; 
v___x_4718_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 1, v___x_4718_);
v___x_4720_ = v___x_4716_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_mctx_4711_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4722_, 2, v_zetaDeltaFVarIds_4712_);
lean_ctor_set(v_reuseFailAlloc_4722_, 3, v_postponed_4713_);
lean_ctor_set(v_reuseFailAlloc_4722_, 4, v_diag_4714_);
v___x_4720_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4721_; 
v___x_4721_ = lean_st_ref_set(v___y_4549_, v___x_4720_);
v___y_4646_ = v_snd_4672_;
v___y_4647_ = v___x_4688_;
v___y_4648_ = v___y_4546_;
v___y_4649_ = v___y_4547_;
v___y_4650_ = v___y_4548_;
v___y_4651_ = v___y_4549_;
v___y_4652_ = v___y_4550_;
v___y_4653_ = v___y_4551_;
goto v___jp_4645_;
}
}
}
}
}
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
lean_dec(v_snd_4672_);
lean_dec(v___x_4568_);
lean_dec(v_instName_4564_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4728_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4689_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4689_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
}
}
}
v___jp_4738_:
{
if (lean_obj_tag(v___y_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4749_; 
v_a_4740_ = lean_ctor_get(v___y_4739_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___y_4739_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4742_ = v___y_4739_;
v_isShared_4743_ = v_isSharedCheck_4749_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___y_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4749_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
if (lean_obj_tag(v_a_4740_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4746_; 
lean_dec(v___x_4568_);
lean_dec(v_instName_4564_);
lean_dec(v_a_4563_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4744_ = lean_ctor_get(v_a_4740_, 0);
lean_inc(v_a_4744_);
lean_dec_ref(v_a_4740_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_a_4744_);
v___x_4746_ = v___x_4742_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4744_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
else
{
lean_object* v_a_4748_; 
lean_del_object(v___x_4742_);
v_a_4748_ = lean_ctor_get(v_a_4740_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v_a_4740_);
v_a_4668_ = v_a_4748_;
goto v___jp_4667_;
}
}
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec(v___x_4568_);
lean_dec(v_instName_4564_);
lean_dec(v_a_4563_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4750_ = lean_ctor_get(v___y_4739_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___y_4739_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___y_4739_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___y_4739_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec(v_a_4558_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec_ref(v___f_4545_);
lean_dec(v_ctorName_4543_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4795_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4562_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4562_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec_ref(v___f_4545_);
lean_dec(v_ctorName_4543_);
lean_dec(v_inductiveTypeName_4540_);
v_a_4803_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4557_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4557_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
v___jp_4553_:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___y_4554_);
v___x_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
return v___x_4556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4811_, lean_object* v___x_4812_, lean_object* v_inductiveTypeName_4813_, lean_object* v___x_4814_, lean_object* v___x_4815_, lean_object* v_ctorName_4816_, lean_object* v_addHypotheses_4817_, lean_object* v___f_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_){
_start:
{
uint8_t v___x_17162__boxed_4826_; uint8_t v_addHypotheses_boxed_4827_; lean_object* v_res_4828_; 
v___x_17162__boxed_4826_ = lean_unbox(v___x_4814_);
v_addHypotheses_boxed_4827_ = lean_unbox(v_addHypotheses_4817_);
v_res_4828_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4811_, v___x_4812_, v_inductiveTypeName_4813_, v___x_17162__boxed_4826_, v___x_4815_, v_ctorName_4816_, v_addHypotheses_boxed_4827_, v___f_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
lean_dec(v___x_4815_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4831_, lean_object* v_ctorName_4832_, uint8_t v_addHypotheses_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v___f_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; uint8_t v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___f_4848_; uint8_t v___x_4849_; 
v___f_4841_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4842_ = lean_box(0);
v___x_4843_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4844_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4845_ = 1;
v___x_4846_ = lean_box(v___x_4845_);
v___x_4847_ = lean_box(v_addHypotheses_4833_);
lean_inc(v_ctorName_4832_);
v___f_4848_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4848_, 0, v___x_4843_);
lean_closure_set(v___f_4848_, 1, v___x_4844_);
lean_closure_set(v___f_4848_, 2, v_inductiveTypeName_4831_);
lean_closure_set(v___f_4848_, 3, v___x_4846_);
lean_closure_set(v___f_4848_, 4, v___x_4842_);
lean_closure_set(v___f_4848_, 5, v_ctorName_4832_);
lean_closure_set(v___f_4848_, 6, v___x_4847_);
lean_closure_set(v___f_4848_, 7, v___f_4841_);
v___x_4849_ = l_Lean_isPrivateName(v_ctorName_4832_);
lean_dec(v_ctorName_4832_);
if (v___x_4849_ == 0)
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4848_, v___x_4845_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
return v___x_4850_;
}
else
{
uint8_t v___x_4851_; lean_object* v___x_4852_; 
v___x_4851_ = 0;
v___x_4852_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4848_, v___x_4851_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
return v___x_4852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4853_, lean_object* v_ctorName_4854_, lean_object* v_addHypotheses_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_){
_start:
{
uint8_t v_addHypotheses_boxed_4863_; lean_object* v_res_4864_; 
v_addHypotheses_boxed_4863_ = lean_unbox(v_addHypotheses_4855_);
v_res_4864_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4853_, v_ctorName_4854_, v_addHypotheses_boxed_4863_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_);
lean_dec(v_a_4861_);
lean_dec_ref(v_a_4860_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4865_, lean_object* v_ctorName_4866_, uint8_t v_addHypotheses_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4871_ = lean_box(v_addHypotheses_4867_);
v___x_4872_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4872_, 0, v_inductiveTypeName_4865_);
lean_closure_set(v___x_4872_, 1, v_ctorName_4866_);
lean_closure_set(v___x_4872_, 2, v___x_4871_);
v___x_4873_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4872_, v_a_4868_, v_a_4869_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4903_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4903_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4903_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
if (lean_obj_tag(v_a_4874_) == 0)
{
uint8_t v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4878_ = 0;
v___x_4879_ = lean_box(v___x_4878_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v___x_4879_);
v___x_4881_ = v___x_4876_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
else
{
lean_object* v_val_4883_; lean_object* v___x_4884_; 
lean_del_object(v___x_4876_);
v_val_4883_ = lean_ctor_get(v_a_4874_, 0);
lean_inc(v_val_4883_);
lean_dec_ref(v_a_4874_);
v___x_4884_ = l_Lean_Elab_Command_elabCommand(v_val_4883_, v_a_4868_, v_a_4869_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4893_; 
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4893_ == 0)
{
lean_object* v_unused_4894_; 
v_unused_4894_ = lean_ctor_get(v___x_4884_, 0);
lean_dec(v_unused_4894_);
v___x_4886_ = v___x_4884_;
v_isShared_4887_ = v_isSharedCheck_4893_;
goto v_resetjp_4885_;
}
else
{
lean_dec(v___x_4884_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4893_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
uint8_t v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4888_ = 1;
v___x_4889_ = lean_box(v___x_4888_);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 0, v___x_4889_);
v___x_4891_ = v___x_4886_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
v_a_4895_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4884_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4884_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
}
}
else
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4911_; 
v_a_4904_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4911_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4906_ = v___x_4873_;
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4873_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4909_; 
if (v_isShared_4907_ == 0)
{
v___x_4909_ = v___x_4906_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4904_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4912_, lean_object* v_ctorName_4913_, lean_object* v_addHypotheses_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_){
_start:
{
uint8_t v_addHypotheses_boxed_4918_; lean_object* v_res_4919_; 
v_addHypotheses_boxed_4918_ = lean_unbox(v_addHypotheses_4914_);
v_res_4919_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4912_, v_ctorName_4913_, v_addHypotheses_boxed_4918_, v_a_4915_, v_a_4916_);
lean_dec(v_a_4916_);
lean_dec_ref(v_a_4915_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4923_, uint8_t v_addHypotheses_4924_, lean_object* v_as_x27_4925_, lean_object* v_b_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
if (lean_obj_tag(v_as_x27_4925_) == 0)
{
lean_object* v___x_4930_; 
lean_dec(v_declName_4923_);
v___x_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4930_, 0, v_b_4926_);
return v___x_4930_;
}
else
{
lean_object* v_head_4931_; lean_object* v_tail_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4961_; 
lean_dec_ref(v_b_4926_);
v_head_4931_ = lean_ctor_get(v_as_x27_4925_, 0);
v_tail_4932_ = lean_ctor_get(v_as_x27_4925_, 1);
v_isSharedCheck_4961_ = !lean_is_exclusive(v_as_x27_4925_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4934_ = v_as_x27_4925_;
v_isShared_4935_ = v_isSharedCheck_4961_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_tail_4932_);
lean_inc(v_head_4931_);
lean_dec(v_as_x27_4925_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4961_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4936_; 
lean_inc(v_declName_4923_);
v___x_4936_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4923_, v_head_4931_, v_addHypotheses_4924_, v___y_4927_, v___y_4928_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4952_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4939_ = v___x_4936_;
v_isShared_4940_ = v_isSharedCheck_4952_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4936_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4952_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4941_; uint8_t v___x_4942_; 
v___x_4941_ = lean_box(0);
v___x_4942_ = lean_unbox(v_a_4937_);
if (v___x_4942_ == 0)
{
lean_object* v___x_4943_; 
lean_del_object(v___x_4939_);
lean_dec(v_a_4937_);
lean_del_object(v___x_4934_);
v___x_4943_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v_as_x27_4925_ = v_tail_4932_;
v_b_4926_ = v___x_4943_;
goto _start;
}
else
{
lean_object* v___x_4945_; lean_object* v___x_4947_; 
lean_dec(v_tail_4932_);
lean_dec(v_declName_4923_);
v___x_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4945_, 0, v_a_4937_);
if (v_isShared_4935_ == 0)
{
lean_ctor_set_tag(v___x_4934_, 0);
lean_ctor_set(v___x_4934_, 1, v___x_4941_);
lean_ctor_set(v___x_4934_, 0, v___x_4945_);
v___x_4947_ = v___x_4934_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4945_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v___x_4941_);
v___x_4947_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_object* v___x_4949_; 
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v___x_4947_);
v___x_4949_ = v___x_4939_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
}
else
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
lean_del_object(v___x_4934_);
lean_dec(v_tail_4932_);
lean_dec(v_declName_4923_);
v_a_4953_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4936_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4936_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_4962_, lean_object* v_addHypotheses_4963_, lean_object* v_as_x27_4964_, lean_object* v_b_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
uint8_t v_addHypotheses_boxed_4969_; lean_object* v_res_4970_; 
v_addHypotheses_boxed_4969_ = lean_unbox(v_addHypotheses_4963_);
v_res_4970_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4962_, v_addHypotheses_boxed_4969_, v_as_x27_4964_, v_b_4965_, v___y_4966_, v___y_4967_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_4971_, lean_object* v_declName_4972_, uint8_t v_addHypotheses_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v_ctors_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v_ctors_4977_ = lean_ctor_get(v_a_4971_, 4);
lean_inc(v_ctors_4977_);
lean_dec_ref(v_a_4971_);
v___x_4978_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_4979_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4972_, v_addHypotheses_4973_, v_ctors_4977_, v___x_4978_, v___y_4974_, v___y_4975_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4994_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4982_ = v___x_4979_;
v_isShared_4983_ = v_isSharedCheck_4994_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4979_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4994_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v_fst_4984_; 
v_fst_4984_ = lean_ctor_get(v_a_4980_, 0);
lean_inc(v_fst_4984_);
lean_dec(v_a_4980_);
if (lean_obj_tag(v_fst_4984_) == 0)
{
uint8_t v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4988_; 
v___x_4985_ = 0;
v___x_4986_ = lean_box(v___x_4985_);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 0, v___x_4986_);
v___x_4988_ = v___x_4982_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4986_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
else
{
lean_object* v_val_4990_; lean_object* v___x_4992_; 
v_val_4990_ = lean_ctor_get(v_fst_4984_, 0);
lean_inc(v_val_4990_);
lean_dec_ref(v_fst_4984_);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 0, v_val_4990_);
v___x_4992_ = v___x_4982_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_val_4990_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
}
else
{
lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5002_; 
v_a_4995_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4997_ = v___x_4979_;
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4979_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_5000_; 
if (v_isShared_4998_ == 0)
{
v___x_5000_ = v___x_4997_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_5003_, lean_object* v_declName_5004_, lean_object* v_addHypotheses_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
uint8_t v_addHypotheses_boxed_5009_; lean_object* v_res_5010_; 
v_addHypotheses_boxed_5009_ = lean_unbox(v_addHypotheses_5005_);
v_res_5010_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5003_, v_declName_5004_, v_addHypotheses_boxed_5009_, v___y_5006_, v___y_5007_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
return v_res_5010_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_5011_; 
v___x_5011_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5011_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5012_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_5013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5013_, 0, v___x_5012_);
return v___x_5013_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5014_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_5015_ = lean_unsigned_to_nat(0u);
v___x_5016_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5015_);
lean_ctor_set(v___x_5016_, 1, v___x_5015_);
lean_ctor_set(v___x_5016_, 2, v___x_5015_);
lean_ctor_set(v___x_5016_, 3, v___x_5015_);
lean_ctor_set(v___x_5016_, 4, v___x_5014_);
lean_ctor_set(v___x_5016_, 5, v___x_5014_);
lean_ctor_set(v___x_5016_, 6, v___x_5014_);
lean_ctor_set(v___x_5016_, 7, v___x_5014_);
lean_ctor_set(v___x_5016_, 8, v___x_5014_);
lean_ctor_set(v___x_5016_, 9, v___x_5014_);
return v___x_5016_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5017_ = lean_unsigned_to_nat(32u);
v___x_5018_ = lean_mk_empty_array_with_capacity(v___x_5017_);
v___x_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
return v___x_5019_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5020_ = ((size_t)5ULL);
v___x_5021_ = lean_unsigned_to_nat(0u);
v___x_5022_ = lean_unsigned_to_nat(32u);
v___x_5023_ = lean_mk_empty_array_with_capacity(v___x_5022_);
v___x_5024_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_5025_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5025_, 0, v___x_5024_);
lean_ctor_set(v___x_5025_, 1, v___x_5023_);
lean_ctor_set(v___x_5025_, 2, v___x_5021_);
lean_ctor_set(v___x_5025_, 3, v___x_5021_);
lean_ctor_set_usize(v___x_5025_, 4, v___x_5020_);
return v___x_5025_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5026_ = lean_box(1);
v___x_5027_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_5028_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_5029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5029_, 0, v___x_5028_);
lean_ctor_set(v___x_5029_, 1, v___x_5027_);
lean_ctor_set(v___x_5029_, 2, v___x_5026_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v___x_5033_; lean_object* v_env_5034_; lean_object* v___x_5035_; lean_object* v_scopes_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v_opts_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5033_ = lean_st_ref_get(v___y_5031_);
v_env_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc_ref(v_env_5034_);
lean_dec(v___x_5033_);
v___x_5035_ = lean_st_ref_get(v___y_5031_);
v_scopes_5036_ = lean_ctor_get(v___x_5035_, 2);
lean_inc(v_scopes_5036_);
lean_dec(v___x_5035_);
v___x_5037_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5038_ = l_List_head_x21___redArg(v___x_5037_, v_scopes_5036_);
lean_dec(v_scopes_5036_);
v_opts_5039_ = lean_ctor_get(v___x_5038_, 1);
lean_inc_ref(v_opts_5039_);
lean_dec(v___x_5038_);
v___x_5040_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_5041_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5);
v___x_5042_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5042_, 0, v_env_5034_);
lean_ctor_set(v___x_5042_, 1, v___x_5040_);
lean_ctor_set(v___x_5042_, 2, v___x_5041_);
lean_ctor_set(v___x_5042_, 3, v_opts_5039_);
v___x_5043_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5042_);
lean_ctor_set(v___x_5043_, 1, v_msgData_5030_);
v___x_5044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v_res_5048_; 
v_res_5048_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5045_, v___y_5046_);
lean_dec(v___y_5046_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_5049_, lean_object* v_macroStack_5050_, lean_object* v___y_5051_){
_start:
{
lean_object* v___x_5053_; lean_object* v_scopes_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v_opts_5057_; lean_object* v___x_5058_; uint8_t v___x_5059_; 
v___x_5053_ = lean_st_ref_get(v___y_5051_);
v_scopes_5054_ = lean_ctor_get(v___x_5053_, 2);
lean_inc(v_scopes_5054_);
lean_dec(v___x_5053_);
v___x_5055_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5056_ = l_List_head_x21___redArg(v___x_5055_, v_scopes_5054_);
lean_dec(v_scopes_5054_);
v_opts_5057_ = lean_ctor_get(v___x_5056_, 1);
lean_inc_ref(v_opts_5057_);
lean_dec(v___x_5056_);
v___x_5058_ = l_Lean_Elab_pp_macroStack;
v___x_5059_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_5057_, v___x_5058_);
lean_dec_ref(v_opts_5057_);
if (v___x_5059_ == 0)
{
lean_object* v___x_5060_; 
lean_dec(v_macroStack_5050_);
v___x_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5060_, 0, v_msgData_5049_);
return v___x_5060_;
}
else
{
if (lean_obj_tag(v_macroStack_5050_) == 0)
{
lean_object* v___x_5061_; 
v___x_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5061_, 0, v_msgData_5049_);
return v___x_5061_;
}
else
{
lean_object* v_head_5062_; lean_object* v_after_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5078_; 
v_head_5062_ = lean_ctor_get(v_macroStack_5050_, 0);
lean_inc(v_head_5062_);
v_after_5063_ = lean_ctor_get(v_head_5062_, 1);
v_isSharedCheck_5078_ = !lean_is_exclusive(v_head_5062_);
if (v_isSharedCheck_5078_ == 0)
{
lean_object* v_unused_5079_; 
v_unused_5079_ = lean_ctor_get(v_head_5062_, 0);
lean_dec(v_unused_5079_);
v___x_5065_ = v_head_5062_;
v_isShared_5066_ = v_isSharedCheck_5078_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_after_5063_);
lean_dec(v_head_5062_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5078_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5067_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_5066_ == 0)
{
lean_ctor_set_tag(v___x_5065_, 7);
lean_ctor_set(v___x_5065_, 1, v___x_5067_);
lean_ctor_set(v___x_5065_, 0, v_msgData_5049_);
v___x_5069_ = v___x_5065_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_msgData_5049_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v_msgData_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5070_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_5071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5069_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = l_Lean_MessageData_ofSyntax(v_after_5063_);
v___x_5073_ = l_Lean_indentD(v___x_5072_);
v_msgData_5074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5074_, 0, v___x_5071_);
lean_ctor_set(v_msgData_5074_, 1, v___x_5073_);
v___x_5075_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_5074_, v_macroStack_5050_);
v___x_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5075_);
return v___x_5076_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_5080_, lean_object* v_macroStack_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5080_, v_macroStack_5081_, v___y_5082_);
lean_dec(v___y_5082_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l_Lean_Elab_Command_getRef___redArg(v___y_5086_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_object* v_a_5090_; lean_object* v_macroStack_5091_; lean_object* v___x_5092_; lean_object* v_a_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5104_; 
v_a_5090_ = lean_ctor_get(v___x_5089_, 0);
lean_inc(v_a_5090_);
lean_dec_ref(v___x_5089_);
v_macroStack_5091_ = lean_ctor_get(v___y_5086_, 4);
v___x_5092_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_5085_, v___y_5087_);
v_a_5093_ = lean_ctor_get(v___x_5092_, 0);
lean_inc(v_a_5093_);
lean_dec_ref(v___x_5092_);
lean_inc_n(v_macroStack_5091_, 2);
v___x_5094_ = l_Lean_Elab_getBetterRef(v_a_5090_, v_macroStack_5091_);
lean_dec(v_a_5090_);
v___x_5095_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_5093_, v_macroStack_5091_, v___y_5087_);
v_a_5096_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5098_ = v___x_5095_;
v_isShared_5099_ = v_isSharedCheck_5104_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5095_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5104_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5100_; lean_object* v___x_5102_; 
v___x_5100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5094_);
lean_ctor_set(v___x_5100_, 1, v_a_5096_);
if (v_isShared_5099_ == 0)
{
lean_ctor_set_tag(v___x_5098_, 1);
lean_ctor_set(v___x_5098_, 0, v___x_5100_);
v___x_5102_ = v___x_5098_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5100_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
else
{
lean_object* v_a_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5112_; 
lean_dec_ref(v_msg_5085_);
v_a_5105_ = lean_ctor_get(v___x_5089_, 0);
v_isSharedCheck_5112_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5112_ == 0)
{
v___x_5107_ = v___x_5089_;
v_isShared_5108_ = v_isSharedCheck_5112_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_a_5105_);
lean_dec(v___x_5089_);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5113_, v___y_5114_, v___y_5115_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v___x_5122_; lean_object* v_env_5123_; lean_object* v___x_5124_; 
v___x_5122_ = lean_st_ref_get(v___y_5120_);
v_env_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc_ref(v_env_5123_);
lean_dec(v___x_5122_);
lean_inc(v_constName_5118_);
v___x_5124_ = l_Lean_isInductiveCore_x3f(v_env_5123_, v_constName_5118_);
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v___x_5125_; uint8_t v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5125_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5126_ = 0;
v___x_5127_ = l_Lean_MessageData_ofConstName(v_constName_5118_, v___x_5126_);
v___x_5128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5125_);
lean_ctor_set(v___x_5128_, 1, v___x_5127_);
v___x_5129_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5128_);
lean_ctor_set(v___x_5130_, 1, v___x_5129_);
v___x_5131_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5130_, v___y_5119_, v___y_5120_);
return v___x_5131_;
}
else
{
lean_object* v_val_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5139_; 
lean_dec(v_constName_5118_);
v_val_5132_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5139_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5139_ == 0)
{
v___x_5134_ = v___x_5124_;
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_val_5132_);
lean_dec(v___x_5124_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5139_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5137_; 
if (v_isShared_5135_ == 0)
{
lean_ctor_set_tag(v___x_5134_, 0);
v___x_5137_ = v___x_5134_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_val_5132_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
return v___x_5137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5140_, v___y_5141_, v___y_5142_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
return v_res_5144_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5146_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5147_ = l_Lean_stringToMessageData(v___x_5146_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_){
_start:
{
lean_object* v___x_5155_; 
lean_inc(v_declName_5148_);
v___x_5155_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5148_, v___y_5149_, v___y_5150_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; uint8_t v___x_5157_; lean_object* v___x_5158_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
lean_inc_n(v_a_5156_, 2);
lean_dec_ref(v___x_5155_);
v___x_5157_ = 0;
lean_inc(v_declName_5148_);
v___x_5158_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5156_, v_declName_5148_, v___x_5157_, v___y_5149_, v___y_5150_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_object* v_a_5159_; uint8_t v___x_5160_; 
v_a_5159_ = lean_ctor_get(v___x_5158_, 0);
lean_inc(v_a_5159_);
lean_dec_ref(v___x_5158_);
v___x_5160_ = lean_unbox(v_a_5159_);
lean_dec(v_a_5159_);
if (v___x_5160_ == 0)
{
uint8_t v___x_5161_; lean_object* v___x_5162_; 
v___x_5161_ = 1;
lean_inc(v_declName_5148_);
v___x_5162_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5156_, v_declName_5148_, v___x_5161_, v___y_5149_, v___y_5150_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; uint8_t v___x_5164_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_a_5163_);
lean_dec_ref(v___x_5162_);
v___x_5164_ = lean_unbox(v_a_5163_);
lean_dec(v_a_5163_);
if (v___x_5164_ == 0)
{
lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___x_5165_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5166_ = l_Lean_MessageData_ofConstName(v_declName_5148_, v___x_5157_);
v___x_5167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5165_);
lean_ctor_set(v___x_5167_, 1, v___x_5166_);
v___x_5168_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5167_);
lean_ctor_set(v___x_5169_, 1, v___x_5168_);
v___x_5170_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5169_, v___y_5149_, v___y_5150_);
return v___x_5170_;
}
else
{
lean_dec(v_declName_5148_);
goto v___jp_5152_;
}
}
else
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5178_; 
lean_dec(v_declName_5148_);
v_a_5171_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5173_ = v___x_5162_;
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5162_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5176_; 
if (v_isShared_5174_ == 0)
{
v___x_5176_ = v___x_5173_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
}
else
{
lean_dec(v_a_5156_);
lean_dec(v_declName_5148_);
goto v___jp_5152_;
}
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
lean_dec(v_a_5156_);
lean_dec(v_declName_5148_);
v_a_5179_ = lean_ctor_get(v___x_5158_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5158_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5158_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
else
{
lean_object* v_a_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5194_; 
lean_dec(v_declName_5148_);
v_a_5187_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5189_ = v___x_5155_;
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_a_5187_);
lean_dec(v___x_5155_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5192_; 
if (v_isShared_5190_ == 0)
{
v___x_5192_ = v___x_5189_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
v___jp_5152_:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; 
v___x_5153_ = lean_box(0);
v___x_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5154_, 0, v___x_5153_);
return v___x_5154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
lean_object* v_res_5199_; 
v_res_5199_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5195_, v___y_5196_, v___y_5197_);
lean_dec(v___y_5197_);
lean_dec_ref(v___y_5196_);
return v_res_5199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_){
_start:
{
lean_object* v___f_5204_; lean_object* v___x_5205_; 
lean_inc(v_declName_5200_);
v___f_5204_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5204_, 0, v_declName_5200_);
v___x_5205_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5200_, v___f_5204_, v_a_5201_, v_a_5202_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5206_, v_a_5207_, v_a_5208_);
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5207_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5211_, uint8_t v_addHypotheses_5212_, lean_object* v_as_5213_, lean_object* v_as_x27_5214_, lean_object* v_b_5215_, lean_object* v_a_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v___x_5220_; 
v___x_5220_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5211_, v_addHypotheses_5212_, v_as_x27_5214_, v_b_5215_, v___y_5217_, v___y_5218_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5221_, lean_object* v_addHypotheses_5222_, lean_object* v_as_5223_, lean_object* v_as_x27_5224_, lean_object* v_b_5225_, lean_object* v_a_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
uint8_t v_addHypotheses_boxed_5230_; lean_object* v_res_5231_; 
v_addHypotheses_boxed_5230_ = lean_unbox(v_addHypotheses_5222_);
v_res_5231_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5221_, v_addHypotheses_boxed_5230_, v_as_5223_, v_as_x27_5224_, v_b_5225_, v_a_5226_, v___y_5227_, v___y_5228_);
lean_dec(v___y_5228_);
lean_dec_ref(v___y_5227_);
lean_dec(v_as_5223_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v___x_5236_; 
v___x_5236_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5232_, v___y_5234_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5237_, v___y_5238_, v___y_5239_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5242_, lean_object* v_msg_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5243_, v___y_5244_, v___y_5245_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5248_, lean_object* v_msg_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_){
_start:
{
lean_object* v_res_5253_; 
v_res_5253_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5248_, v_msg_5249_, v___y_5250_, v___y_5251_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
return v_res_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5254_, lean_object* v_macroStack_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v___x_5259_; 
v___x_5259_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5254_, v_macroStack_5255_, v___y_5257_);
return v___x_5259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5260_, lean_object* v_macroStack_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5260_, v_macroStack_5261_, v___y_5262_, v___y_5263_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5266_, lean_object* v___y_5267_){
_start:
{
lean_object* v___x_5269_; lean_object* v_env_5270_; uint8_t v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5269_ = lean_st_ref_get(v___y_5267_);
v_env_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc_ref(v_env_5270_);
lean_dec(v___x_5269_);
v___x_5271_ = l_Lean_isInductiveCore(v_env_5270_, v_declName_5266_);
v___x_5272_ = lean_box(v___x_5271_);
v___x_5273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5272_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5274_, v___y_5275_);
lean_dec(v___y_5275_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v___x_5282_; 
v___x_5282_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5278_, v___y_5280_);
return v___x_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5283_, v___y_5284_, v___y_5285_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
if (v_____do__lift_5288_ == 0)
{
uint8_t v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5292_ = 1;
v___x_5293_ = lean_box(v___x_5292_);
v___x_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
return v___x_5294_;
}
else
{
uint8_t v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
v___x_5295_ = 0;
v___x_5296_ = lean_box(v___x_5295_);
v___x_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5296_);
return v___x_5297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_){
_start:
{
uint8_t v_____do__lift_1703__boxed_5302_; lean_object* v_res_5303_; 
v_____do__lift_1703__boxed_5302_ = lean_unbox(v_____do__lift_5298_);
v_res_5303_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1703__boxed_5302_, v___y_5299_, v___y_5300_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5304_, size_t v_i_5305_, size_t v_stop_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_usize_dec_eq(v_i_5305_, v_stop_5306_);
if (v___x_5310_ == 0)
{
uint8_t v___x_5311_; uint8_t v_a_5313_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
v___x_5311_ = 1;
v___x_5319_ = lean_array_uget_borrowed(v_as_5304_, v_i_5305_);
lean_inc(v___x_5319_);
v___x_5320_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5319_, v___y_5308_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5330_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5323_ = v___x_5320_;
v_isShared_5324_ = v_isSharedCheck_5330_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5320_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5330_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
uint8_t v___x_5325_; 
v___x_5325_ = lean_unbox(v_a_5321_);
lean_dec(v_a_5321_);
if (v___x_5325_ == 0)
{
lean_object* v___x_5326_; lean_object* v___x_5328_; 
v___x_5326_ = lean_box(v___x_5311_);
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 0, v___x_5326_);
v___x_5328_ = v___x_5323_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v___x_5326_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
else
{
lean_del_object(v___x_5323_);
v_a_5313_ = v___x_5310_;
goto v___jp_5312_;
}
}
}
else
{
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5331_; uint8_t v___x_5332_; 
v_a_5331_ = lean_ctor_get(v___x_5320_, 0);
lean_inc(v_a_5331_);
lean_dec_ref(v___x_5320_);
v___x_5332_ = lean_unbox(v_a_5331_);
lean_dec(v_a_5331_);
v_a_5313_ = v___x_5332_;
goto v___jp_5312_;
}
else
{
return v___x_5320_;
}
}
v___jp_5312_:
{
if (v_a_5313_ == 0)
{
size_t v___x_5314_; size_t v___x_5315_; 
v___x_5314_ = ((size_t)1ULL);
v___x_5315_ = lean_usize_add(v_i_5305_, v___x_5314_);
v_i_5305_ = v___x_5315_;
goto _start;
}
else
{
lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5317_ = lean_box(v___x_5311_);
v___x_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5317_);
return v___x_5318_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object* v_as_5336_, lean_object* v_i_5337_, lean_object* v_stop_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
size_t v_i_boxed_5342_; size_t v_stop_boxed_5343_; lean_object* v_res_5344_; 
v_i_boxed_5342_ = lean_unbox_usize(v_i_5337_);
lean_dec(v_i_5337_);
v_stop_boxed_5343_ = lean_unbox_usize(v_stop_5338_);
lean_dec(v_stop_5338_);
v_res_5344_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5336_, v_i_boxed_5342_, v_stop_boxed_5343_, v___y_5339_, v___y_5340_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec_ref(v_as_5336_);
return v_res_5344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object* v_as_5345_, size_t v_i_5346_, size_t v_stop_5347_, lean_object* v_b_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_){
_start:
{
uint8_t v___x_5352_; 
v___x_5352_ = lean_usize_dec_eq(v_i_5346_, v_stop_5347_);
if (v___x_5352_ == 0)
{
lean_object* v___x_5353_; lean_object* v___x_5354_; 
v___x_5353_ = lean_array_uget_borrowed(v_as_5345_, v_i_5346_);
lean_inc(v___x_5353_);
v___x_5354_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v___x_5353_, v___y_5349_, v___y_5350_);
if (lean_obj_tag(v___x_5354_) == 0)
{
lean_object* v_a_5355_; size_t v___x_5356_; size_t v___x_5357_; 
v_a_5355_ = lean_ctor_get(v___x_5354_, 0);
lean_inc(v_a_5355_);
lean_dec_ref(v___x_5354_);
v___x_5356_ = ((size_t)1ULL);
v___x_5357_ = lean_usize_add(v_i_5346_, v___x_5356_);
v_i_5346_ = v___x_5357_;
v_b_5348_ = v_a_5355_;
goto _start;
}
else
{
return v___x_5354_;
}
}
else
{
lean_object* v___x_5359_; 
v___x_5359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5359_, 0, v_b_5348_);
return v___x_5359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object* v_as_5360_, lean_object* v_i_5361_, lean_object* v_stop_5362_, lean_object* v_b_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_){
_start:
{
size_t v_i_boxed_5367_; size_t v_stop_boxed_5368_; lean_object* v_res_5369_; 
v_i_boxed_5367_ = lean_unbox_usize(v_i_5361_);
lean_dec(v_i_5361_);
v_stop_boxed_5368_ = lean_unbox_usize(v_stop_5362_);
lean_dec(v_stop_5362_);
v_res_5369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5360_, v_i_boxed_5367_, v_stop_boxed_5368_, v_b_5363_, v___y_5364_, v___y_5365_);
lean_dec(v___y_5365_);
lean_dec_ref(v___y_5364_);
lean_dec_ref(v_as_5360_);
return v_res_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object* v_declNames_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_){
_start:
{
uint8_t v___y_5375_; lean_object* v___y_5376_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___y_5412_; uint8_t v___x_5415_; 
v___x_5394_ = lean_unsigned_to_nat(0u);
v___x_5395_ = lean_array_get_size(v_declNames_5370_);
v___x_5415_ = lean_nat_dec_lt(v___x_5394_, v___x_5395_);
if (v___x_5415_ == 0)
{
lean_object* v___x_5416_; 
v___x_5416_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5415_, v_a_5371_, v_a_5372_);
v___y_5412_ = v___x_5416_;
goto v___jp_5411_;
}
else
{
if (v___x_5415_ == 0)
{
goto v___jp_5396_;
}
else
{
size_t v___x_5417_; size_t v___x_5418_; lean_object* v___x_5419_; 
v___x_5417_ = ((size_t)0ULL);
v___x_5418_ = lean_usize_of_nat(v___x_5395_);
v___x_5419_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5370_, v___x_5417_, v___x_5418_, v_a_5371_, v_a_5372_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; uint8_t v___x_5421_; lean_object* v___x_5422_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_a_5420_);
lean_dec_ref(v___x_5419_);
v___x_5421_ = lean_unbox(v_a_5420_);
lean_dec(v_a_5420_);
v___x_5422_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5421_, v_a_5371_, v_a_5372_);
v___y_5412_ = v___x_5422_;
goto v___jp_5411_;
}
else
{
v___y_5412_ = v___x_5419_;
goto v___jp_5411_;
}
}
}
v___jp_5374_:
{
if (lean_obj_tag(v___y_5376_) == 0)
{
lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5384_; 
v_isSharedCheck_5384_ = !lean_is_exclusive(v___y_5376_);
if (v_isSharedCheck_5384_ == 0)
{
lean_object* v_unused_5385_; 
v_unused_5385_ = lean_ctor_get(v___y_5376_, 0);
lean_dec(v_unused_5385_);
v___x_5378_ = v___y_5376_;
v_isShared_5379_ = v_isSharedCheck_5384_;
goto v_resetjp_5377_;
}
else
{
lean_dec(v___y_5376_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5384_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5380_; lean_object* v___x_5382_; 
v___x_5380_ = lean_box(v___y_5375_);
if (v_isShared_5379_ == 0)
{
lean_ctor_set(v___x_5378_, 0, v___x_5380_);
v___x_5382_ = v___x_5378_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5380_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
else
{
lean_object* v_a_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5393_; 
v_a_5386_ = lean_ctor_get(v___y_5376_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___y_5376_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5388_ = v___y_5376_;
v_isShared_5389_ = v_isSharedCheck_5393_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_a_5386_);
lean_dec(v___y_5376_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5393_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v___x_5391_; 
if (v_isShared_5389_ == 0)
{
v___x_5391_ = v___x_5388_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_a_5386_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
v___jp_5396_:
{
uint8_t v___x_5397_; uint8_t v___x_5398_; 
v___x_5397_ = 1;
v___x_5398_ = lean_nat_dec_lt(v___x_5394_, v___x_5395_);
if (v___x_5398_ == 0)
{
lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5399_ = lean_box(v___x_5397_);
v___x_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5399_);
return v___x_5400_;
}
else
{
lean_object* v___x_5401_; uint8_t v___x_5402_; 
v___x_5401_ = lean_box(0);
v___x_5402_ = lean_nat_dec_le(v___x_5395_, v___x_5395_);
if (v___x_5402_ == 0)
{
if (v___x_5398_ == 0)
{
lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5403_ = lean_box(v___x_5397_);
v___x_5404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5404_, 0, v___x_5403_);
return v___x_5404_;
}
else
{
size_t v___x_5405_; size_t v___x_5406_; lean_object* v___x_5407_; 
v___x_5405_ = ((size_t)0ULL);
v___x_5406_ = lean_usize_of_nat(v___x_5395_);
v___x_5407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5370_, v___x_5405_, v___x_5406_, v___x_5401_, v_a_5371_, v_a_5372_);
v___y_5375_ = v___x_5397_;
v___y_5376_ = v___x_5407_;
goto v___jp_5374_;
}
}
else
{
size_t v___x_5408_; size_t v___x_5409_; lean_object* v___x_5410_; 
v___x_5408_ = ((size_t)0ULL);
v___x_5409_ = lean_usize_of_nat(v___x_5395_);
v___x_5410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5370_, v___x_5408_, v___x_5409_, v___x_5401_, v_a_5371_, v_a_5372_);
v___y_5375_ = v___x_5397_;
v___y_5376_ = v___x_5410_;
goto v___jp_5374_;
}
}
}
v___jp_5411_:
{
if (lean_obj_tag(v___y_5412_) == 0)
{
lean_object* v_a_5413_; uint8_t v___x_5414_; 
v_a_5413_ = lean_ctor_get(v___y_5412_, 0);
v___x_5414_ = lean_unbox(v_a_5413_);
if (v___x_5414_ == 0)
{
return v___y_5412_;
}
else
{
lean_dec_ref(v___y_5412_);
goto v___jp_5396_;
}
}
else
{
return v___y_5412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_){
_start:
{
lean_object* v_res_5427_; 
v_res_5427_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5423_, v_a_5424_, v_a_5425_);
lean_dec(v_a_5425_);
lean_dec_ref(v_a_5424_);
lean_dec_ref(v_declNames_5423_);
return v_res_5427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; 
v___x_5492_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5493_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5494_ = l_Lean_Elab_registerDerivingHandler(v___x_5492_, v___x_5493_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v___x_5495_; uint8_t v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
lean_dec_ref(v___x_5494_);
v___x_5495_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5496_ = 0;
v___x_5497_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5498_ = l_Lean_registerTraceClass(v___x_5495_, v___x_5496_, v___x_5497_);
return v___x_5498_;
}
else
{
return v___x_5494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5499_){
_start:
{
lean_object* v_res_5500_; 
v_res_5500_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5500_;
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
