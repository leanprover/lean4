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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_inlineExprTrailing(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "synthesizing Inhabited instance for"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "using constructor `"};
static const lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_775_ = lean_st_ref_set(v___y_765_, v___y_774_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_a_783_, lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
else
{
lean_object* v_key_786_; lean_object* v_tail_787_; uint8_t v___x_788_; 
v_key_786_ = lean_ctor_get(v_x_784_, 0);
v_tail_787_ = lean_ctor_get(v_x_784_, 2);
v___x_788_ = lean_expr_eqv(v_key_786_, v_a_783_);
if (v___x_788_ == 0)
{
v_x_784_ = v_tail_787_;
goto _start;
}
else
{
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_a_790_, lean_object* v_x_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_790_, v_x_791_);
lean_dec(v_x_791_);
lean_dec_ref(v_a_790_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
if (lean_obj_tag(v_x_795_) == 0)
{
return v_x_794_;
}
else
{
lean_object* v_key_796_; lean_object* v_value_797_; lean_object* v_tail_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_821_; 
v_key_796_ = lean_ctor_get(v_x_795_, 0);
v_value_797_ = lean_ctor_get(v_x_795_, 1);
v_tail_798_ = lean_ctor_get(v_x_795_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_821_ == 0)
{
v___x_800_ = v_x_795_;
v_isShared_801_ = v_isSharedCheck_821_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_tail_798_);
lean_inc(v_value_797_);
lean_inc(v_key_796_);
lean_dec(v_x_795_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_821_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v_fold_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_802_ = lean_array_get_size(v_x_794_);
v___x_803_ = l_Lean_Expr_hash(v_key_796_);
v___x_804_ = 32ULL;
v___x_805_ = lean_uint64_shift_right(v___x_803_, v___x_804_);
v_fold_806_ = lean_uint64_xor(v___x_803_, v___x_805_);
v___x_807_ = 16ULL;
v___x_808_ = lean_uint64_shift_right(v_fold_806_, v___x_807_);
v___x_809_ = lean_uint64_xor(v_fold_806_, v___x_808_);
v___x_810_ = lean_uint64_to_usize(v___x_809_);
v___x_811_ = lean_usize_of_nat(v___x_802_);
v___x_812_ = ((size_t)1ULL);
v___x_813_ = lean_usize_sub(v___x_811_, v___x_812_);
v___x_814_ = lean_usize_land(v___x_810_, v___x_813_);
v___x_815_ = lean_array_uget_borrowed(v_x_794_, v___x_814_);
lean_inc(v___x_815_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 2, v___x_815_);
v___x_817_ = v___x_800_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_key_796_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_value_797_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v___x_815_);
v___x_817_ = v_reuseFailAlloc_820_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; 
v___x_818_ = lean_array_uset(v_x_794_, v___x_814_, v___x_817_);
v_x_794_ = v___x_818_;
v_x_795_ = v_tail_798_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_i_822_, lean_object* v_source_823_, lean_object* v_target_824_){
_start:
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = lean_array_get_size(v_source_823_);
v___x_826_ = lean_nat_dec_lt(v_i_822_, v___x_825_);
if (v___x_826_ == 0)
{
lean_dec_ref(v_source_823_);
lean_dec(v_i_822_);
return v_target_824_;
}
else
{
lean_object* v_es_827_; lean_object* v___x_828_; lean_object* v_source_829_; lean_object* v_target_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_es_827_ = lean_array_fget(v_source_823_, v_i_822_);
v___x_828_ = lean_box(0);
v_source_829_ = lean_array_fset(v_source_823_, v_i_822_, v___x_828_);
v_target_830_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(v_target_824_, v_es_827_);
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_add(v_i_822_, v___x_831_);
lean_dec(v_i_822_);
v_i_822_ = v___x_832_;
v_source_823_ = v_source_829_;
v_target_824_ = v_target_830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_data_834_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v_nbuckets_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_835_ = lean_array_get_size(v_data_834_);
v___x_836_ = lean_unsigned_to_nat(2u);
v_nbuckets_837_ = lean_nat_mul(v___x_835_, v___x_836_);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_box(0);
v___x_840_ = lean_mk_array(v_nbuckets_837_, v___x_839_);
v___x_841_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v___x_838_, v_data_834_, v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(lean_object* v_m_842_, lean_object* v_a_843_, lean_object* v_b_844_){
_start:
{
lean_object* v_size_845_; lean_object* v_buckets_846_; lean_object* v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; uint64_t v_fold_851_; uint64_t v___x_852_; uint64_t v___x_853_; uint64_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; lean_object* v_bkt_860_; uint8_t v___x_861_; 
v_size_845_ = lean_ctor_get(v_m_842_, 0);
v_buckets_846_ = lean_ctor_get(v_m_842_, 1);
v___x_847_ = lean_array_get_size(v_buckets_846_);
v___x_848_ = l_Lean_Expr_hash(v_a_843_);
v___x_849_ = 32ULL;
v___x_850_ = lean_uint64_shift_right(v___x_848_, v___x_849_);
v_fold_851_ = lean_uint64_xor(v___x_848_, v___x_850_);
v___x_852_ = 16ULL;
v___x_853_ = lean_uint64_shift_right(v_fold_851_, v___x_852_);
v___x_854_ = lean_uint64_xor(v_fold_851_, v___x_853_);
v___x_855_ = lean_uint64_to_usize(v___x_854_);
v___x_856_ = lean_usize_of_nat(v___x_847_);
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_sub(v___x_856_, v___x_857_);
v___x_859_ = lean_usize_land(v___x_855_, v___x_858_);
v_bkt_860_ = lean_array_uget_borrowed(v_buckets_846_, v___x_859_);
v___x_861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_843_, v_bkt_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_882_; 
lean_inc_ref(v_buckets_846_);
lean_inc(v_size_845_);
v_isSharedCheck_882_ = !lean_is_exclusive(v_m_842_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; lean_object* v_unused_884_; 
v_unused_883_ = lean_ctor_get(v_m_842_, 1);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_m_842_, 0);
lean_dec(v_unused_884_);
v___x_863_ = v_m_842_;
v_isShared_864_ = v_isSharedCheck_882_;
goto v_resetjp_862_;
}
else
{
lean_dec(v_m_842_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_882_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v_size_x27_866_; lean_object* v___x_867_; lean_object* v_buckets_x27_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_865_ = lean_unsigned_to_nat(1u);
v_size_x27_866_ = lean_nat_add(v_size_845_, v___x_865_);
lean_dec(v_size_845_);
lean_inc(v_bkt_860_);
v___x_867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_867_, 0, v_a_843_);
lean_ctor_set(v___x_867_, 1, v_b_844_);
lean_ctor_set(v___x_867_, 2, v_bkt_860_);
v_buckets_x27_868_ = lean_array_uset(v_buckets_846_, v___x_859_, v___x_867_);
v___x_869_ = lean_unsigned_to_nat(4u);
v___x_870_ = lean_nat_mul(v_size_x27_866_, v___x_869_);
v___x_871_ = lean_unsigned_to_nat(3u);
v___x_872_ = lean_nat_div(v___x_870_, v___x_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_array_get_size(v_buckets_x27_868_);
v___x_874_ = lean_nat_dec_le(v___x_872_, v___x_873_);
lean_dec(v___x_872_);
if (v___x_874_ == 0)
{
lean_object* v_val_875_; lean_object* v___x_877_; 
v_val_875_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_buckets_x27_868_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_val_875_);
lean_ctor_set(v___x_863_, 0, v_size_x27_866_);
v___x_877_ = v___x_863_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_size_x27_866_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_val_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
else
{
lean_object* v___x_880_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_buckets_x27_868_);
lean_ctor_set(v___x_863_, 0, v_size_x27_866_);
v___x_880_ = v___x_863_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_size_x27_866_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_buckets_x27_868_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_dec(v_b_844_);
lean_dec_ref(v_a_843_);
return v_m_842_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(lean_object* v_m_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_buckets_887_; lean_object* v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v_fold_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v___x_895_; size_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_buckets_887_ = lean_ctor_get(v_m_885_, 1);
v___x_888_ = lean_array_get_size(v_buckets_887_);
v___x_889_ = l_Lean_Expr_hash(v_a_886_);
v___x_890_ = 32ULL;
v___x_891_ = lean_uint64_shift_right(v___x_889_, v___x_890_);
v_fold_892_ = lean_uint64_xor(v___x_889_, v___x_891_);
v___x_893_ = 16ULL;
v___x_894_ = lean_uint64_shift_right(v_fold_892_, v___x_893_);
v___x_895_ = lean_uint64_xor(v_fold_892_, v___x_894_);
v___x_896_ = lean_uint64_to_usize(v___x_895_);
v___x_897_ = lean_usize_of_nat(v___x_888_);
v___x_898_ = ((size_t)1ULL);
v___x_899_ = lean_usize_sub(v___x_897_, v___x_898_);
v___x_900_ = lean_usize_land(v___x_896_, v___x_899_);
v___x_901_ = lean_array_uget_borrowed(v_buckets_887_, v___x_900_);
v___x_902_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_886_, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_m_903_, lean_object* v_a_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_903_, v_a_904_);
lean_dec_ref(v_a_904_);
lean_dec_ref(v_m_903_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(lean_object* v_e_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; lean_object* v_checked_911_; uint8_t v___x_912_; 
v___x_910_ = lean_st_ref_get(v_a_908_);
v_checked_911_ = lean_ctor_get(v___x_910_, 1);
lean_inc_ref(v_checked_911_);
lean_dec(v___x_910_);
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_checked_911_, v_e_907_);
lean_dec_ref(v_checked_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v_visited_914_; lean_object* v_checked_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_925_; 
v___x_913_ = lean_st_ref_take(v_a_908_);
v_visited_914_ = lean_ctor_get(v___x_913_, 0);
v_checked_915_ = lean_ctor_get(v___x_913_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_925_ == 0)
{
v___x_917_ = v___x_913_;
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_checked_915_);
lean_inc(v_visited_914_);
lean_dec(v___x_913_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_919_ = lean_box(0);
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_checked_915_, v_e_907_, v___x_919_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v___x_920_);
v___x_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_visited_914_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_920_);
v___x_922_ = v_reuseFailAlloc_924_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = lean_st_ref_set(v_a_908_, v___x_922_);
return v___x_912_;
}
}
}
else
{
lean_dec_ref(v_e_907_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_e_926_, lean_object* v_a_927_, lean_object* v___y_928_){
_start:
{
uint8_t v_res_929_; lean_object* v_r_930_; 
v_res_929_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_926_, v_a_927_);
lean_dec(v_a_927_);
v_r_930_ = lean_box(v_res_929_);
return v_r_930_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(lean_object* v_e_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_934_; lean_object* v_visited_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; lean_object* v___x_939_; size_t v___x_940_; uint8_t v___x_941_; 
v___x_934_ = lean_st_ref_get(v_a_932_);
v_visited_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc_ref(v_visited_935_);
lean_dec(v___x_934_);
v___x_936_ = lean_ptr_addr(v_e_931_);
v___x_937_ = ((size_t)8191ULL);
v___x_938_ = lean_usize_mod(v___x_936_, v___x_937_);
v___x_939_ = lean_array_uget(v_visited_935_, v___x_938_);
lean_dec_ref(v_visited_935_);
v___x_940_ = lean_ptr_addr(v___x_939_);
lean_dec(v___x_939_);
v___x_941_ = lean_usize_dec_eq(v___x_940_, v___x_936_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v_visited_943_; lean_object* v_checked_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_953_; 
v___x_942_ = lean_st_ref_take(v_a_932_);
v_visited_943_ = lean_ctor_get(v___x_942_, 0);
v_checked_944_ = lean_ctor_get(v___x_942_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_953_ == 0)
{
v___x_946_ = v___x_942_;
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_checked_944_);
lean_inc(v_visited_943_);
lean_dec(v___x_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lean_array_uset(v_visited_943_, v___x_938_, v_e_931_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_checked_944_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = lean_st_ref_set(v_a_932_, v___x_950_);
return v___x_941_;
}
}
}
else
{
lean_dec_ref(v_e_931_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_e_954_, lean_object* v_a_955_, lean_object* v___y_956_){
_start:
{
uint8_t v_res_957_; lean_object* v_r_958_; 
v_res_957_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_954_, v_a_955_);
lean_dec(v_a_955_);
v_r_958_ = lean_box(v_res_957_);
return v_r_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(lean_object* v_p_959_, lean_object* v_f_960_, uint8_t v_stopWhenVisited_961_, lean_object* v_e_962_, lean_object* v_a_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___y_967_; lean_object* v_d_968_; lean_object* v_b_969_; lean_object* v___y_970_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v___x_995_; 
lean_inc_ref(v_e_962_);
v___x_995_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_962_, v_a_963_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; uint8_t v___x_997_; 
lean_inc_ref(v_p_959_);
lean_inc_ref(v_e_962_);
v___x_996_ = lean_apply_1(v_p_959_, v_e_962_);
v___x_997_ = lean_unbox(v___x_996_);
if (v___x_997_ == 0)
{
v___y_974_ = v_a_963_;
v___y_975_ = v___y_964_;
goto v___jp_973_;
}
else
{
uint8_t v___x_998_; 
lean_inc_ref(v_e_962_);
v___x_998_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_962_, v_a_963_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; 
lean_inc_ref(v_f_960_);
lean_inc(v___y_964_);
lean_inc_ref(v_e_962_);
v___x_999_ = lean_apply_3(v_f_960_, v_e_962_, v___y_964_, lean_box(0));
if (v_stopWhenVisited_961_ == 0)
{
v___y_974_ = v_a_963_;
v___y_975_ = v___y_964_;
goto v___jp_973_;
}
else
{
lean_object* v___x_1000_; 
lean_dec_ref(v_e_962_);
lean_dec_ref(v_f_960_);
lean_dec_ref(v_p_959_);
v___x_1000_ = lean_box(0);
return v___x_1000_;
}
}
else
{
v___y_974_ = v_a_963_;
v___y_975_ = v___y_964_;
goto v___jp_973_;
}
}
}
else
{
lean_object* v___x_1001_; 
lean_dec_ref(v_e_962_);
lean_dec_ref(v_f_960_);
lean_dec_ref(v_p_959_);
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
v___jp_966_:
{
lean_object* v___x_971_; 
lean_inc_ref(v_f_960_);
lean_inc_ref(v_p_959_);
v___x_971_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_959_, v_f_960_, v_stopWhenVisited_961_, v_d_968_, v___y_970_, v___y_967_);
v_e_962_ = v_b_969_;
v_a_963_ = v___y_970_;
v___y_964_ = v___y_967_;
goto _start;
}
v___jp_973_:
{
switch(lean_obj_tag(v_e_962_))
{
case 7:
{
lean_object* v_binderType_976_; lean_object* v_body_977_; 
v_binderType_976_ = lean_ctor_get(v_e_962_, 1);
lean_inc_ref(v_binderType_976_);
v_body_977_ = lean_ctor_get(v_e_962_, 2);
lean_inc_ref(v_body_977_);
lean_dec_ref_known(v_e_962_, 3);
v___y_967_ = v___y_975_;
v_d_968_ = v_binderType_976_;
v_b_969_ = v_body_977_;
v___y_970_ = v___y_974_;
goto v___jp_966_;
}
case 6:
{
lean_object* v_binderType_978_; lean_object* v_body_979_; 
v_binderType_978_ = lean_ctor_get(v_e_962_, 1);
lean_inc_ref(v_binderType_978_);
v_body_979_ = lean_ctor_get(v_e_962_, 2);
lean_inc_ref(v_body_979_);
lean_dec_ref_known(v_e_962_, 3);
v___y_967_ = v___y_975_;
v_d_968_ = v_binderType_978_;
v_b_969_ = v_body_979_;
v___y_970_ = v___y_974_;
goto v___jp_966_;
}
case 8:
{
lean_object* v_type_980_; lean_object* v_value_981_; lean_object* v_body_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_type_980_ = lean_ctor_get(v_e_962_, 1);
lean_inc_ref(v_type_980_);
v_value_981_ = lean_ctor_get(v_e_962_, 2);
lean_inc_ref(v_value_981_);
v_body_982_ = lean_ctor_get(v_e_962_, 3);
lean_inc_ref(v_body_982_);
lean_dec_ref_known(v_e_962_, 4);
lean_inc_ref_n(v_f_960_, 2);
lean_inc_ref_n(v_p_959_, 2);
v___x_983_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_959_, v_f_960_, v_stopWhenVisited_961_, v_type_980_, v___y_974_, v___y_975_);
v___x_984_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_959_, v_f_960_, v_stopWhenVisited_961_, v_value_981_, v___y_974_, v___y_975_);
v_e_962_ = v_body_982_;
v_a_963_ = v___y_974_;
v___y_964_ = v___y_975_;
goto _start;
}
case 5:
{
lean_object* v_fn_986_; lean_object* v_arg_987_; lean_object* v___x_988_; 
v_fn_986_ = lean_ctor_get(v_e_962_, 0);
lean_inc_ref(v_fn_986_);
v_arg_987_ = lean_ctor_get(v_e_962_, 1);
lean_inc_ref(v_arg_987_);
lean_dec_ref_known(v_e_962_, 2);
lean_inc_ref(v_f_960_);
lean_inc_ref(v_p_959_);
v___x_988_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_959_, v_f_960_, v_stopWhenVisited_961_, v_fn_986_, v___y_974_, v___y_975_);
v_e_962_ = v_arg_987_;
v_a_963_ = v___y_974_;
v___y_964_ = v___y_975_;
goto _start;
}
case 10:
{
lean_object* v_expr_990_; 
v_expr_990_ = lean_ctor_get(v_e_962_, 1);
lean_inc_ref(v_expr_990_);
lean_dec_ref_known(v_e_962_, 2);
v_e_962_ = v_expr_990_;
v_a_963_ = v___y_974_;
v___y_964_ = v___y_975_;
goto _start;
}
case 11:
{
lean_object* v_struct_992_; 
v_struct_992_ = lean_ctor_get(v_e_962_, 2);
lean_inc_ref(v_struct_992_);
lean_dec_ref_known(v_e_962_, 3);
v_e_962_ = v_struct_992_;
v_a_963_ = v___y_974_;
v___y_964_ = v___y_975_;
goto _start;
}
default: 
{
lean_object* v___x_994_; 
lean_dec_ref(v_e_962_);
lean_dec_ref(v_f_960_);
lean_dec_ref(v_p_959_);
v___x_994_ = lean_box(0);
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg___boxed(lean_object* v_p_1002_, lean_object* v_f_1003_, lean_object* v_stopWhenVisited_1004_, lean_object* v_e_1005_, lean_object* v_a_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1009_; lean_object* v_res_1010_; 
v_stopWhenVisited_boxed_1009_ = lean_unbox(v_stopWhenVisited_1004_);
v_res_1010_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1002_, v_f_1003_, v_stopWhenVisited_boxed_1009_, v_e_1005_, v_a_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec(v_a_1006_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(lean_object* v_p_1011_, lean_object* v_f_1012_, lean_object* v_e_1013_, uint8_t v_stopWhenVisited_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1017_ = l_Lean_ForEachExprWhere_initCache;
v___x_1018_ = lean_st_mk_ref(v___x_1017_);
v___x_1019_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1011_, v_f_1012_, v_stopWhenVisited_1014_, v_e_1013_, v___x_1018_, v___y_1015_);
v___x_1020_ = lean_st_ref_get(v___x_1018_);
lean_dec(v___x_1018_);
lean_dec(v___x_1020_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg___boxed(lean_object* v_p_1021_, lean_object* v_f_1022_, lean_object* v_e_1023_, lean_object* v_stopWhenVisited_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1027_; lean_object* v_res_1028_; 
v_stopWhenVisited_boxed_1027_ = lean_unbox(v_stopWhenVisited_1024_);
v_res_1028_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1021_, v_f_1022_, v_e_1023_, v_stopWhenVisited_boxed_1027_, v___y_1025_);
lean_dec(v___y_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(lean_object* v_usedInstIdxs_1030_, lean_object* v___f_1031_, lean_object* v_e_1032_, uint8_t v___x_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1036_ = lean_st_mk_ref(v_usedInstIdxs_1030_);
v___x_1037_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___closed__0));
v___x_1038_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v___x_1037_, v___f_1031_, v_e_1032_, v___x_1033_, v___x_1036_);
v___x_1039_ = lean_st_ref_get(v___x_1036_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed(lean_object* v_usedInstIdxs_1041_, lean_object* v___f_1042_, lean_object* v_e_1043_, lean_object* v___x_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___x_6985__boxed_1047_; lean_object* v_res_1048_; 
v___x_6985__boxed_1047_ = lean_unbox(v___x_1044_);
v_res_1048_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(v_usedInstIdxs_1041_, v___f_1042_, v_e_1043_, v___x_6985__boxed_1047_, v_x_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(lean_object* v_usedInstIdxs_1049_, lean_object* v_localInst2Index_1050_, lean_object* v_e_1051_){
_start:
{
if (lean_obj_tag(v_localInst2Index_1050_) == 0)
{
lean_object* v___f_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v_snd_1057_; 
v___f_1052_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1052_, 0, v_localInst2Index_1050_);
v___x_1053_ = 0;
v___x_1054_ = lean_box(v___x_1053_);
v___f_1055_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1___boxed), 6, 4);
lean_closure_set(v___f_1055_, 0, v_usedInstIdxs_1049_);
lean_closure_set(v___f_1055_, 1, v___f_1052_);
lean_closure_set(v___f_1055_, 2, v_e_1051_);
lean_closure_set(v___f_1055_, 3, v___x_1054_);
v___x_1056_ = l_runST___redArg(v___f_1055_);
v_snd_1057_ = lean_ctor_get(v___x_1056_, 1);
lean_inc(v_snd_1057_);
lean_dec(v___x_1056_);
return v_snd_1057_;
}
else
{
lean_dec_ref(v_e_1051_);
return v_usedInstIdxs_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(lean_object* v_00_u03b4_1058_, lean_object* v_t_1059_, lean_object* v_k_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___redArg(v_t_1059_, v_k_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0___boxed(lean_object* v_00_u03b4_1062_, lean_object* v_t_1063_, lean_object* v_k_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__0(v_00_u03b4_1062_, v_t_1063_, v_k_1064_);
lean_dec(v_k_1064_);
lean_dec(v_t_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(lean_object* v_00_u03b2_1066_, lean_object* v_k_1067_, lean_object* v_t_1068_){
_start:
{
uint8_t v___x_1069_; 
v___x_1069_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_k_1067_, v_t_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___boxed(lean_object* v_00_u03b2_1070_, lean_object* v_k_1071_, lean_object* v_t_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1(v_00_u03b2_1070_, v_k_1071_, v_t_1072_);
lean_dec(v_t_1072_);
lean_dec(v_k_1071_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2(lean_object* v_00_u03b2_1075_, lean_object* v_k_1076_, lean_object* v_v_1077_, lean_object* v_t_1078_, lean_object* v_hl_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__2___redArg(v_k_1076_, v_v_1077_, v_t_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(lean_object* v_x_1081_, lean_object* v_p_1082_, lean_object* v_f_1083_, lean_object* v_e_1084_, uint8_t v_stopWhenVisited_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___redArg(v_p_1082_, v_f_1083_, v_e_1084_, v_stopWhenVisited_1085_, v___y_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3___boxed(lean_object* v_x_1089_, lean_object* v_p_1090_, lean_object* v_f_1091_, lean_object* v_e_1092_, lean_object* v_stopWhenVisited_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1096_; lean_object* v_res_1097_; 
v_stopWhenVisited_boxed_1096_ = lean_unbox(v_stopWhenVisited_1093_);
v_res_1097_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3(v_x_1089_, v_p_1090_, v_f_1091_, v_e_1092_, v_stopWhenVisited_boxed_1096_, v___y_1094_);
lean_dec(v___y_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(lean_object* v_x_1098_, lean_object* v_e_1099_, lean_object* v_a_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___redArg(v_e_1099_, v_a_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4___boxed(lean_object* v_x_1104_, lean_object* v_e_1105_, lean_object* v_a_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__4(v_x_1104_, v_e_1105_, v_a_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec(v_a_1106_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(lean_object* v_x_1111_, lean_object* v_p_1112_, lean_object* v_f_1113_, uint8_t v_stopWhenVisited_1114_, lean_object* v_e_1115_, lean_object* v_a_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___redArg(v_p_1112_, v_f_1113_, v_stopWhenVisited_1114_, v_e_1115_, v_a_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3___boxed(lean_object* v_x_1120_, lean_object* v_p_1121_, lean_object* v_f_1122_, lean_object* v_stopWhenVisited_1123_, lean_object* v_e_1124_, lean_object* v_a_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1128_; lean_object* v_res_1129_; 
v_stopWhenVisited_boxed_1128_ = lean_unbox(v_stopWhenVisited_1123_);
v_res_1129_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3(v_x_1120_, v_p_1121_, v_f_1122_, v_stopWhenVisited_boxed_1128_, v_e_1124_, v_a_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec(v_a_1125_);
return v_res_1129_;
}
}
LEAN_EXPORT uint8_t l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(lean_object* v_x_1130_, lean_object* v_e_1131_, lean_object* v_a_1132_, lean_object* v___y_1133_){
_start:
{
uint8_t v___x_1135_; 
v___x_1135_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___redArg(v_e_1131_, v_a_1132_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5___boxed(lean_object* v_x_1136_, lean_object* v_e_1137_, lean_object* v_a_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5(v_x_1136_, v_e_1137_, v_a_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec(v_a_1138_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1143_, lean_object* v_m_1144_, lean_object* v_a_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v_m_1144_, v_a_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_m_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v_res_1150_; lean_object* v_r_1151_; 
v_res_1150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6(v_00_u03b2_1147_, v_m_1148_, v_a_1149_);
lean_dec_ref(v_a_1149_);
lean_dec_ref(v_m_1148_);
v_r_1151_ = lean_box(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1152_, lean_object* v_m_1153_, lean_object* v_a_1154_, lean_object* v_b_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7___redArg(v_m_1153_, v_a_1154_, v_b_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1157_, lean_object* v_a_1158_, lean_object* v_x_1159_){
_start:
{
uint8_t v___x_1160_; 
v___x_1160_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___redArg(v_a_1158_, v_x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1161_, lean_object* v_a_1162_, lean_object* v_x_1163_){
_start:
{
uint8_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6_spec__7(v_00_u03b2_1161_, v_a_1162_, v_x_1163_);
lean_dec(v_x_1163_);
lean_dec_ref(v_a_1162_);
v_r_1165_ = lean_box(v_res_1164_);
return v_r_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_1166_, lean_object* v_data_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9___redArg(v_data_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1169_, lean_object* v_i_1170_, lean_object* v_source_1171_, lean_object* v_target_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_i_1170_, v_source_1171_, v_target_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11(lean_object* v_00_u03b2_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__7_spec__9_spec__10_spec__11___redArg(v_x_1175_, v_x_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10(void){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Array_mkArray0(lean_box(0));
return v___x_1194_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__0));
v___x_1210_ = l_String_toRawSubstring_x27(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(lean_object* v_upperBound_1223_, lean_object* v_usedInstIdxs_1224_, lean_object* v_a_1225_, lean_object* v_b_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_a_1231_; uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_lt(v_a_1225_, v_upperBound_1223_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec(v_a_1225_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_b_1226_);
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__1));
v___x_1238_ = l_Lean_Core_mkFreshUserName(v___x_1237_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1284_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v_fst_1240_ = lean_ctor_get(v_b_1226_, 0);
v_snd_1241_ = lean_ctor_get(v_b_1226_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_b_1226_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1243_ = v_b_1226_;
v_isShared_1244_ = v_isSharedCheck_1284_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
lean_dec(v_b_1226_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1284_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_ref_1245_; lean_object* v_quotContext_1246_; lean_object* v_currMacroScope_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_ref_1245_ = lean_ctor_get(v___y_1227_, 5);
v_quotContext_1246_ = lean_ctor_get(v___y_1227_, 10);
v_currMacroScope_1247_ = lean_ctor_get(v___y_1227_, 11);
v___x_1248_ = l_Lean_mkIdent(v_a_1239_);
lean_inc(v___x_1248_);
v___x_1249_ = lean_array_push(v_fst_1240_, v___x_1248_);
v___x_1250_ = 0;
v___x_1251_ = l_Lean_SourceInfo_fromRef(v_ref_1245_, v___x_1250_);
v___x_1252_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__6));
v___x_1253_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__7));
lean_inc_n(v___x_1251_, 5);
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1251_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1256_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1255_, v___x_1248_);
v___x_1257_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1251_);
lean_ctor_set(v___x_1258_, 1, v___x_1255_);
lean_ctor_set(v___x_1258_, 2, v___x_1257_);
v___x_1259_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__11));
v___x_1260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1251_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
lean_inc_ref(v___x_1258_);
lean_inc(v___x_1256_);
v___x_1261_ = l_Lean_Syntax_node4(v___x_1251_, v___x_1252_, v___x_1254_, v___x_1256_, v___x_1258_, v___x_1260_);
v___x_1262_ = lean_array_push(v_snd_1241_, v___x_1261_);
v___x_1263_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__1___redArg(v_a_1225_, v_usedInstIdxs_1224_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref_known(v___x_1258_, 3);
lean_dec(v___x_1256_);
lean_dec(v___x_1251_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1262_);
lean_ctor_set(v___x_1243_, 0, v___x_1249_);
v___x_1265_ = v___x_1243_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1262_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
v_a_1231_ = v___x_1265_;
goto v___jp_1230_;
}
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1267_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__13));
v___x_1268_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__14));
lean_inc_n(v___x_1251_, 4);
v___x_1269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1251_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1271_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1272_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1247_);
lean_inc(v_quotContext_1246_);
v___x_1273_ = l_Lean_addMacroScope(v_quotContext_1246_, v___x_1272_, v_currMacroScope_1247_);
v___x_1274_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1275_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1251_);
lean_ctor_set(v___x_1275_, 1, v___x_1271_);
lean_ctor_set(v___x_1275_, 2, v___x_1273_);
lean_ctor_set(v___x_1275_, 3, v___x_1274_);
v___x_1276_ = l_Lean_Syntax_node2(v___x_1251_, v___x_1270_, v___x_1275_, v___x_1256_);
v___x_1277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__22));
v___x_1278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1251_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_Syntax_node4(v___x_1251_, v___x_1267_, v___x_1269_, v___x_1258_, v___x_1276_, v___x_1278_);
v___x_1280_ = lean_array_push(v___x_1262_, v___x_1279_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1280_);
lean_ctor_set(v___x_1243_, 0, v___x_1249_);
v___x_1282_ = v___x_1243_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
v_a_1231_ = v___x_1282_;
goto v___jp_1230_;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_b_1226_);
lean_dec(v_a_1225_);
v_a_1285_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1238_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1238_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
v___jp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_add(v_a_1225_, v___x_1232_);
lean_dec(v_a_1225_);
v_a_1225_ = v___x_1233_;
v_b_1226_ = v_a_1231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___boxed(lean_object* v_upperBound_1293_, lean_object* v_usedInstIdxs_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1293_, v_usedInstIdxs_1294_, v_a_1295_, v_b_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v_usedInstIdxs_1294_);
lean_dec(v_upperBound_1293_);
return v_res_1300_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_box(1);
v___x_1302_ = l_Lean_MessageData_ofFormat(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__2));
v___x_1307_ = l_Lean_MessageData_ofFormat(v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
return v_x_1308_;
}
else
{
lean_object* v_head_1310_; lean_object* v_tail_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1333_; 
v_head_1310_ = lean_ctor_get(v_x_1309_, 0);
v_tail_1311_ = lean_ctor_get(v_x_1309_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1313_ = v_x_1309_;
v_isShared_1314_ = v_isSharedCheck_1333_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_tail_1311_);
lean_inc(v_head_1310_);
lean_dec(v_x_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1333_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_before_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1331_; 
v_before_1315_ = lean_ctor_get(v_head_1310_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_head_1310_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v_head_1310_, 1);
lean_dec(v_unused_1332_);
v___x_1317_ = v_head_1310_;
v_isShared_1318_ = v_isSharedCheck_1331_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_before_1315_);
lean_dec(v_head_1310_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1331_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 7);
lean_ctor_set(v___x_1317_, 1, v___x_1319_);
lean_ctor_set(v___x_1317_, 0, v_x_1308_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_x_1308_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__3);
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 7);
lean_ctor_set(v___x_1313_, 1, v___x_1322_);
lean_ctor_set(v___x_1313_, 0, v___x_1321_);
v___x_1324_ = v___x_1313_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = l_Lean_MessageData_ofSyntax(v_before_1315_);
v___x_1326_ = l_Lean_indentD(v___x_1325_);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1324_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v_x_1308_ = v___x_1327_;
v_x_1309_ = v_tail_1311_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(lean_object* v_opts_1334_, lean_object* v_opt_1335_){
_start:
{
lean_object* v_name_1336_; lean_object* v_defValue_1337_; lean_object* v_map_1338_; lean_object* v___x_1339_; 
v_name_1336_ = lean_ctor_get(v_opt_1335_, 0);
v_defValue_1337_ = lean_ctor_get(v_opt_1335_, 1);
v_map_1338_ = lean_ctor_get(v_opts_1334_, 0);
v___x_1339_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1338_, v_name_1336_);
if (lean_obj_tag(v___x_1339_) == 0)
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_unbox(v_defValue_1337_);
return v___x_1340_;
}
else
{
lean_object* v_val_1341_; 
v_val_1341_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_val_1341_);
lean_dec_ref_known(v___x_1339_, 1);
if (lean_obj_tag(v_val_1341_) == 1)
{
uint8_t v_v_1342_; 
v_v_1342_ = lean_ctor_get_uint8(v_val_1341_, 0);
lean_dec_ref_known(v_val_1341_, 0);
return v_v_1342_;
}
else
{
uint8_t v___x_1343_; 
lean_dec(v_val_1341_);
v___x_1343_ = lean_unbox(v_defValue_1337_);
return v___x_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_opts_1344_, lean_object* v_opt_1345_){
_start:
{
uint8_t v_res_1346_; lean_object* v_r_1347_; 
v_res_1346_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_1344_, v_opt_1345_);
lean_dec_ref(v_opt_1345_);
lean_dec_ref(v_opts_1344_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__1));
v___x_1352_ = l_Lean_MessageData_ofFormat(v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_1353_, lean_object* v_macroStack_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_options_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; 
v_options_1357_ = lean_ctor_get(v___y_1355_, 2);
v___x_1358_ = l_Lean_Elab_pp_macroStack;
v___x_1359_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_1357_, v___x_1358_);
v___x_1360_ = lean_bool_not(v___x_1359_);
if (v___x_1360_ == 0)
{
if (lean_obj_tag(v_macroStack_1354_) == 0)
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_msgData_1353_);
return v___x_1361_;
}
else
{
lean_object* v_head_1362_; lean_object* v_after_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1378_; 
v_head_1362_ = lean_ctor_get(v_macroStack_1354_, 0);
lean_inc(v_head_1362_);
v_after_1363_ = lean_ctor_get(v_head_1362_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_head_1362_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v_head_1362_, 0);
lean_dec(v_unused_1379_);
v___x_1365_ = v_head_1362_;
v_isShared_1366_ = v_isSharedCheck_1378_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_after_1363_);
lean_dec(v_head_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1378_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_1366_ == 0)
{
lean_ctor_set_tag(v___x_1365_, 7);
lean_ctor_set(v___x_1365_, 1, v___x_1367_);
lean_ctor_set(v___x_1365_, 0, v_msgData_1353_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_msgData_1353_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_msgData_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1370_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = l_Lean_MessageData_ofSyntax(v_after_1363_);
v___x_1373_ = l_Lean_indentD(v___x_1372_);
v_msgData_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1374_, 0, v___x_1371_);
lean_ctor_set(v_msgData_1374_, 1, v___x_1373_);
v___x_1375_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_1374_, v_macroStack_1354_);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
}
}
else
{
lean_object* v___x_1380_; 
lean_dec(v_macroStack_1354_);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_msgData_1353_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1381_, lean_object* v_macroStack_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1381_, v_macroStack_1382_, v___y_1383_);
lean_dec_ref(v___y_1383_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(lean_object* v_msg_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_ref_1394_; lean_object* v___x_1395_; lean_object* v_a_1396_; lean_object* v_macroStack_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
v_ref_1394_ = lean_ctor_get(v___y_1391_, 5);
v___x_1395_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1386_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref(v___x_1395_);
v_macroStack_1397_ = lean_ctor_get(v___y_1387_, 1);
v___x_1398_ = l_Lean_Elab_getBetterRef(v_ref_1394_, v_macroStack_1397_);
lean_inc(v_macroStack_1397_);
v___x_1399_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_a_1396_, v_macroStack_1397_, v___y_1391_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1398_);
lean_ctor_set(v___x_1404_, 1, v_a_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 1);
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1417_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0));
v___x_1420_ = l_Lean_stringToMessageData(v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2));
v___x_1423_ = l_Lean_stringToMessageData(v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(lean_object* v_constName_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; lean_object* v_env_1433_; lean_object* v___x_1434_; 
v___x_1432_ = lean_st_ref_get(v___y_1430_);
v_env_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc_ref(v_env_1433_);
lean_dec(v___x_1432_);
lean_inc(v_constName_1424_);
v___x_1434_ = l_Lean_isInductiveCore_x3f(v_env_1433_, v_constName_1424_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1435_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_1436_ = 0;
v___x_1437_ = l_Lean_MessageData_ofConstName(v_constName_1424_, v___x_1436_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1435_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_1440_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1441_;
}
else
{
lean_object* v_val_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_constName_1424_);
v_val_1442_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1434_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_val_1442_);
lean_dec(v___x_1434_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 0);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_val_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___boxed(lean_object* v_constName_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_constName_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(size_t v_sz_1459_, size_t v_i_1460_, lean_object* v_bs_1461_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_lt(v_i_1460_, v_sz_1459_);
if (v___x_1462_ == 0)
{
return v_bs_1461_;
}
else
{
lean_object* v_v_1463_; lean_object* v___x_1464_; lean_object* v_bs_x27_1465_; size_t v___x_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v_v_1463_ = lean_array_uget(v_bs_1461_, v_i_1460_);
v___x_1464_ = lean_unsigned_to_nat(0u);
v_bs_x27_1465_ = lean_array_uset(v_bs_1461_, v_i_1460_, v___x_1464_);
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_add(v_i_1460_, v___x_1466_);
v___x_1468_ = lean_array_uset(v_bs_x27_1465_, v_i_1460_, v_v_1463_);
v_i_1460_ = v___x_1467_;
v_bs_1461_ = v___x_1468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0___boxed(lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_bs_1472_){
_start:
{
size_t v_sz_boxed_1473_; size_t v_i_boxed_1474_; lean_object* v_res_1475_; 
v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1474_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_boxed_1473_, v_i_boxed_1474_, v_bs_1472_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(lean_object* v_inductiveTypeName_1553_, lean_object* v_instId_1554_, lean_object* v_usedInstIdxs_1555_, lean_object* v_auxFunId_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1564_; 
lean_inc(v_inductiveTypeName_1553_);
v___x_1564_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_1553_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v_numParams_1566_; lean_object* v_numIndices_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v_numParams_1566_ = lean_ctor_get(v_a_1565_, 1);
lean_inc(v_numParams_1566_);
v_numIndices_1567_ = lean_ctor_get(v_a_1565_, 2);
lean_inc(v_numIndices_1567_);
lean_dec(v_a_1565_);
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = lean_nat_add(v_numParams_1566_, v_numIndices_1567_);
lean_dec(v_numIndices_1567_);
lean_dec(v_numParams_1566_);
v___x_1570_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1));
v___x_1571_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v___x_1569_, v_usedInstIdxs_1555_, v___x_1568_, v___x_1570_, v_a_1561_, v_a_1562_);
lean_dec(v___x_1569_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1648_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1648_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1648_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1647_; 
v_fst_1576_ = lean_ctor_get(v_a_1572_, 0);
v_snd_1577_ = lean_ctor_get(v_a_1572_, 1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_a_1572_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1579_ = v_a_1572_;
v_isShared_1580_ = v_isSharedCheck_1647_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_snd_1577_);
lean_inc(v_fst_1576_);
lean_dec(v_a_1572_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1647_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_ref_1581_; lean_object* v_quotContext_1582_; lean_object* v_currMacroScope_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v_ref_1581_ = lean_ctor_get(v_a_1561_, 5);
v_quotContext_1582_ = lean_ctor_get(v_a_1561_, 10);
v_currMacroScope_1583_ = lean_ctor_get(v_a_1561_, 11);
v___x_1584_ = 0;
v___x_1585_ = l_Lean_SourceInfo_fromRef(v_ref_1581_, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1587_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3));
v___x_1588_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4));
lean_inc(v___x_1585_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 2);
lean_ctor_set(v___x_1579_, 1, v___x_1588_);
lean_ctor_set(v___x_1579_, 0, v___x_1585_);
v___x_1590_ = v___x_1579_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; size_t v_sz_1611_; size_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1591_ = l_Lean_mkCIdent(v_inductiveTypeName_1553_);
lean_inc_n(v___x_1585_, 24);
v___x_1592_ = l_Lean_Syntax_node2(v___x_1585_, v___x_1587_, v___x_1590_, v___x_1591_);
v___x_1593_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1594_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1595_ = l_Array_append___redArg(v___x_1594_, v_fst_1576_);
lean_dec(v_fst_1576_);
v___x_1596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1585_);
lean_ctor_set(v___x_1596_, 1, v___x_1593_);
lean_ctor_set(v___x_1596_, 2, v___x_1595_);
v___x_1597_ = l_Lean_Syntax_node2(v___x_1585_, v___x_1586_, v___x_1592_, v___x_1596_);
v___x_1598_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7));
v___x_1599_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9));
v___x_1600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1585_);
lean_ctor_set(v___x_1600_, 1, v___x_1593_);
lean_ctor_set(v___x_1600_, 2, v___x_1594_);
lean_inc_ref_n(v___x_1600_, 12);
v___x_1601_ = l_Lean_Syntax_node7(v___x_1585_, v___x_1599_, v___x_1600_, v___x_1600_, v___x_1600_, v___x_1600_, v___x_1600_, v___x_1600_, v___x_1600_);
v___x_1602_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10));
v___x_1603_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11));
v___x_1604_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13));
v___x_1605_ = l_Lean_Syntax_node1(v___x_1585_, v___x_1604_, v___x_1600_);
v___x_1606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1585_);
lean_ctor_set(v___x_1606_, 1, v___x_1602_);
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15));
v___x_1608_ = l_Lean_Syntax_node2(v___x_1585_, v___x_1607_, v_instId_1554_, v___x_1600_);
v___x_1609_ = l_Lean_Syntax_node1(v___x_1585_, v___x_1593_, v___x_1608_);
v___x_1610_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17));
v_sz_1611_ = lean_array_size(v_snd_1577_);
v___x_1612_ = ((size_t)0ULL);
v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_1611_, v___x_1612_, v_snd_1577_);
v___x_1614_ = l_Array_append___redArg(v___x_1594_, v___x_1613_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1585_);
lean_ctor_set(v___x_1615_, 1, v___x_1593_);
lean_ctor_set(v___x_1615_, 2, v___x_1614_);
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19));
v___x_1617_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20));
v___x_1618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1585_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1620_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1583_);
lean_inc(v_quotContext_1582_);
v___x_1621_ = l_Lean_addMacroScope(v_quotContext_1582_, v___x_1620_, v_currMacroScope_1583_);
v___x_1622_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1623_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1585_);
lean_ctor_set(v___x_1623_, 1, v___x_1619_);
lean_ctor_set(v___x_1623_, 2, v___x_1621_);
lean_ctor_set(v___x_1623_, 3, v___x_1622_);
v___x_1624_ = l_Lean_Syntax_node1(v___x_1585_, v___x_1593_, v___x_1597_);
v___x_1625_ = l_Lean_Syntax_node2(v___x_1585_, v___x_1586_, v___x_1623_, v___x_1624_);
v___x_1626_ = l_Lean_Syntax_node2(v___x_1585_, v___x_1616_, v___x_1618_, v___x_1625_);
v___x_1627_ = l_Lean_Syntax_node2(v___x_1585_, v___x_1610_, v___x_1615_, v___x_1626_);
v___x_1628_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22));
v___x_1629_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23));
v___x_1630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1585_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25));
v___x_1632_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26));
v___x_1633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1585_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_Syntax_node1(v___x_1585_, v___x_1593_, v_auxFunId_1556_);
v___x_1635_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27));
v___x_1636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1585_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_Syntax_node3(v___x_1585_, v___x_1631_, v___x_1633_, v___x_1634_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30));
v___x_1639_ = l_Lean_Syntax_node2(v___x_1585_, v___x_1638_, v___x_1600_, v___x_1600_);
v___x_1640_ = l_Lean_Syntax_node4(v___x_1585_, v___x_1628_, v___x_1630_, v___x_1637_, v___x_1639_, v___x_1600_);
v___x_1641_ = l_Lean_Syntax_node6(v___x_1585_, v___x_1603_, v___x_1605_, v___x_1606_, v___x_1600_, v___x_1609_, v___x_1627_, v___x_1640_);
v___x_1642_ = l_Lean_Syntax_node2(v___x_1585_, v___x_1598_, v___x_1601_, v___x_1641_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1642_);
v___x_1644_ = v___x_1574_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_auxFunId_1556_);
lean_dec(v_instId_1554_);
lean_dec(v_inductiveTypeName_1553_);
v_a_1649_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1571_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1571_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_auxFunId_1556_);
lean_dec(v_instId_1554_);
lean_dec(v_inductiveTypeName_1553_);
v_a_1657_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1564_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1564_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___boxed(lean_object* v_inductiveTypeName_1665_, lean_object* v_instId_1666_, lean_object* v_usedInstIdxs_1667_, lean_object* v_auxFunId_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_1665_, v_instId_1666_, v_usedInstIdxs_1667_, v_auxFunId_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_usedInstIdxs_1667_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(lean_object* v_upperBound_1677_, lean_object* v_usedInstIdxs_1678_, lean_object* v_inst_1679_, lean_object* v_R_1680_, lean_object* v_a_1681_, lean_object* v_b_1682_, lean_object* v_c_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1677_, v_usedInstIdxs_1678_, v_a_1681_, v_b_1682_, v___y_1688_, v___y_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___boxed(lean_object* v_upperBound_1692_, lean_object* v_usedInstIdxs_1693_, lean_object* v_inst_1694_, lean_object* v_R_1695_, lean_object* v_a_1696_, lean_object* v_b_1697_, lean_object* v_c_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(v_upperBound_1692_, v_usedInstIdxs_1693_, v_inst_1694_, v_R_1695_, v_a_1696_, v_b_1697_, v_c_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v_usedInstIdxs_1693_);
lean_dec(v_upperBound_1692_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(lean_object* v_00_u03b1_1707_, lean_object* v_msg_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1717_, lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(v_00_u03b1_1717_, v_msg_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(lean_object* v_msgData_1727_, lean_object* v_macroStack_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1727_, v_macroStack_1728_, v___y_1733_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1737_, lean_object* v_macroStack_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(v_msgData_1737_, v_macroStack_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1746_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = lean_unsigned_to_nat(32u);
v___x_1748_ = lean_mk_empty_array_with_capacity(v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1750_ = ((size_t)5ULL);
v___x_1751_ = lean_unsigned_to_nat(0u);
v___x_1752_ = lean_unsigned_to_nat(32u);
v___x_1753_ = lean_mk_empty_array_with_capacity(v___x_1752_);
v___x_1754_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__0);
v___x_1755_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___x_1753_);
lean_ctor_set(v___x_1755_, 2, v___x_1751_);
lean_ctor_set(v___x_1755_, 3, v___x_1751_);
lean_ctor_set_usize(v___x_1755_, 4, v___x_1750_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; lean_object* v_traceState_1759_; lean_object* v_traces_1760_; lean_object* v___x_1761_; lean_object* v_traceState_1762_; lean_object* v_env_1763_; lean_object* v_nextMacroScope_1764_; lean_object* v_ngen_1765_; lean_object* v_auxDeclNGen_1766_; lean_object* v_cache_1767_; lean_object* v_messages_1768_; lean_object* v_infoState_1769_; lean_object* v_snapshotTasks_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1789_; 
v___x_1758_ = lean_st_ref_get(v___y_1756_);
v_traceState_1759_ = lean_ctor_get(v___x_1758_, 4);
lean_inc_ref(v_traceState_1759_);
lean_dec(v___x_1758_);
v_traces_1760_ = lean_ctor_get(v_traceState_1759_, 0);
lean_inc_ref(v_traces_1760_);
lean_dec_ref(v_traceState_1759_);
v___x_1761_ = lean_st_ref_take(v___y_1756_);
v_traceState_1762_ = lean_ctor_get(v___x_1761_, 4);
v_env_1763_ = lean_ctor_get(v___x_1761_, 0);
v_nextMacroScope_1764_ = lean_ctor_get(v___x_1761_, 1);
v_ngen_1765_ = lean_ctor_get(v___x_1761_, 2);
v_auxDeclNGen_1766_ = lean_ctor_get(v___x_1761_, 3);
v_cache_1767_ = lean_ctor_get(v___x_1761_, 5);
v_messages_1768_ = lean_ctor_get(v___x_1761_, 6);
v_infoState_1769_ = lean_ctor_get(v___x_1761_, 7);
v_snapshotTasks_1770_ = lean_ctor_get(v___x_1761_, 8);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1772_ = v___x_1761_;
v_isShared_1773_ = v_isSharedCheck_1789_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_snapshotTasks_1770_);
lean_inc(v_infoState_1769_);
lean_inc(v_messages_1768_);
lean_inc(v_cache_1767_);
lean_inc(v_traceState_1762_);
lean_inc(v_auxDeclNGen_1766_);
lean_inc(v_ngen_1765_);
lean_inc(v_nextMacroScope_1764_);
lean_inc(v_env_1763_);
lean_dec(v___x_1761_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1789_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
uint64_t v_tid_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1787_; 
v_tid_1774_ = lean_ctor_get_uint64(v_traceState_1762_, sizeof(void*)*1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_traceState_1762_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; 
v_unused_1788_ = lean_ctor_get(v_traceState_1762_, 0);
lean_dec(v_unused_1788_);
v___x_1776_ = v_traceState_1762_;
v_isShared_1777_ = v_isSharedCheck_1787_;
goto v_resetjp_1775_;
}
else
{
lean_dec(v_traceState_1762_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1787_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___closed__1);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1778_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1778_);
lean_ctor_set_uint64(v_reuseFailAlloc_1786_, sizeof(void*)*1, v_tid_1774_);
v___x_1780_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 4, v___x_1780_);
v___x_1782_ = v___x_1772_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_env_1763_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_nextMacroScope_1764_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_ngen_1765_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_auxDeclNGen_1766_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_cache_1767_);
lean_ctor_set(v_reuseFailAlloc_1785_, 6, v_messages_1768_);
lean_ctor_set(v_reuseFailAlloc_1785_, 7, v_infoState_1769_);
lean_ctor_set(v_reuseFailAlloc_1785_, 8, v_snapshotTasks_1770_);
v___x_1782_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_st_ref_set(v___y_1756_, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v_traces_1760_);
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___y_1790_);
lean_dec(v___y_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___y_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(lean_object* v_x_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
v___x_1817_ = lean_apply_7(v_x_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, lean_box(0));
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed(lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(v_x_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(lean_object* v_mvarId_1827_, lean_object* v_x_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___f_1836_; lean_object* v___x_1837_; 
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___f_1836_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1836_, 0, v_x_1828_);
lean_closure_set(v___f_1836_, 1, v___y_1829_);
lean_closure_set(v___f_1836_, 2, v___y_1830_);
v___x_1837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1827_, v___f_1836_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1837_) == 0)
{
return v___x_1837_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___boxed(lean_object* v_mvarId_1846_, lean_object* v_x_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1846_, v_x_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_object* v_00_u03b1_1856_, lean_object* v_mvarId_1857_, lean_object* v_x_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1857_, v_x_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_mvarId_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(v_00_u03b1_1867_, v_mvarId_1868_, v_x_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1877_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__5(lean_object* v_e_1878_){
_start:
{
if (lean_obj_tag(v_e_1878_) == 0)
{
uint8_t v___x_1879_; 
v___x_1879_ = 2;
return v___x_1879_;
}
else
{
uint8_t v___x_1880_; 
v___x_1880_ = 0;
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__5___boxed(lean_object* v_e_1881_){
_start:
{
uint8_t v_res_1882_; lean_object* v_r_1883_; 
v_res_1882_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__5(v_e_1881_);
lean_dec_ref(v_e_1881_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3_spec__6(size_t v_sz_1884_, size_t v_i_1885_, lean_object* v_bs_1886_){
_start:
{
uint8_t v___x_1887_; 
v___x_1887_ = lean_usize_dec_lt(v_i_1885_, v_sz_1884_);
if (v___x_1887_ == 0)
{
return v_bs_1886_;
}
else
{
lean_object* v_v_1888_; lean_object* v_msg_1889_; lean_object* v___x_1890_; lean_object* v_bs_x27_1891_; size_t v___x_1892_; size_t v___x_1893_; lean_object* v___x_1894_; 
v_v_1888_ = lean_array_uget_borrowed(v_bs_1886_, v_i_1885_);
v_msg_1889_ = lean_ctor_get(v_v_1888_, 1);
lean_inc_ref(v_msg_1889_);
v___x_1890_ = lean_unsigned_to_nat(0u);
v_bs_x27_1891_ = lean_array_uset(v_bs_1886_, v_i_1885_, v___x_1890_);
v___x_1892_ = ((size_t)1ULL);
v___x_1893_ = lean_usize_add(v_i_1885_, v___x_1892_);
v___x_1894_ = lean_array_uset(v_bs_x27_1891_, v_i_1885_, v_msg_1889_);
v_i_1885_ = v___x_1893_;
v_bs_1886_ = v___x_1894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3_spec__6___boxed(lean_object* v_sz_1896_, lean_object* v_i_1897_, lean_object* v_bs_1898_){
_start:
{
size_t v_sz_boxed_1899_; size_t v_i_boxed_1900_; lean_object* v_res_1901_; 
v_sz_boxed_1899_ = lean_unbox_usize(v_sz_1896_);
lean_dec(v_sz_1896_);
v_i_boxed_1900_ = lean_unbox_usize(v_i_1897_);
lean_dec(v_i_1897_);
v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3_spec__6(v_sz_boxed_1899_, v_i_boxed_1900_, v_bs_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___redArg(lean_object* v_oldTraces_1902_, lean_object* v_data_1903_, lean_object* v_ref_1904_, lean_object* v_msg_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_fileName_1911_; lean_object* v_fileMap_1912_; lean_object* v_options_1913_; lean_object* v_currRecDepth_1914_; lean_object* v_maxRecDepth_1915_; lean_object* v_ref_1916_; lean_object* v_currNamespace_1917_; lean_object* v_openDecls_1918_; lean_object* v_initHeartbeats_1919_; lean_object* v_maxHeartbeats_1920_; lean_object* v_quotContext_1921_; lean_object* v_currMacroScope_1922_; uint8_t v_diag_1923_; lean_object* v_cancelTk_x3f_1924_; uint8_t v_suppressElabErrors_1925_; lean_object* v_inheritedTraceOptions_1926_; lean_object* v___x_1927_; lean_object* v_traceState_1928_; lean_object* v_traces_1929_; lean_object* v_ref_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; size_t v_sz_1933_; size_t v___x_1934_; lean_object* v___x_1935_; lean_object* v_msg_1936_; lean_object* v___x_1937_; lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1975_; 
v_fileName_1911_ = lean_ctor_get(v___y_1908_, 0);
v_fileMap_1912_ = lean_ctor_get(v___y_1908_, 1);
v_options_1913_ = lean_ctor_get(v___y_1908_, 2);
v_currRecDepth_1914_ = lean_ctor_get(v___y_1908_, 3);
v_maxRecDepth_1915_ = lean_ctor_get(v___y_1908_, 4);
v_ref_1916_ = lean_ctor_get(v___y_1908_, 5);
v_currNamespace_1917_ = lean_ctor_get(v___y_1908_, 6);
v_openDecls_1918_ = lean_ctor_get(v___y_1908_, 7);
v_initHeartbeats_1919_ = lean_ctor_get(v___y_1908_, 8);
v_maxHeartbeats_1920_ = lean_ctor_get(v___y_1908_, 9);
v_quotContext_1921_ = lean_ctor_get(v___y_1908_, 10);
v_currMacroScope_1922_ = lean_ctor_get(v___y_1908_, 11);
v_diag_1923_ = lean_ctor_get_uint8(v___y_1908_, sizeof(void*)*14);
v_cancelTk_x3f_1924_ = lean_ctor_get(v___y_1908_, 12);
v_suppressElabErrors_1925_ = lean_ctor_get_uint8(v___y_1908_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1926_ = lean_ctor_get(v___y_1908_, 13);
v___x_1927_ = lean_st_ref_get(v___y_1909_);
v_traceState_1928_ = lean_ctor_get(v___x_1927_, 4);
lean_inc_ref(v_traceState_1928_);
lean_dec(v___x_1927_);
v_traces_1929_ = lean_ctor_get(v_traceState_1928_, 0);
lean_inc_ref(v_traces_1929_);
lean_dec_ref(v_traceState_1928_);
v_ref_1930_ = l_Lean_replaceRef(v_ref_1904_, v_ref_1916_);
lean_inc_ref(v_inheritedTraceOptions_1926_);
lean_inc(v_cancelTk_x3f_1924_);
lean_inc(v_currMacroScope_1922_);
lean_inc(v_quotContext_1921_);
lean_inc(v_maxHeartbeats_1920_);
lean_inc(v_initHeartbeats_1919_);
lean_inc(v_openDecls_1918_);
lean_inc(v_currNamespace_1917_);
lean_inc(v_maxRecDepth_1915_);
lean_inc(v_currRecDepth_1914_);
lean_inc_ref(v_options_1913_);
lean_inc_ref(v_fileMap_1912_);
lean_inc_ref(v_fileName_1911_);
v___x_1931_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1931_, 0, v_fileName_1911_);
lean_ctor_set(v___x_1931_, 1, v_fileMap_1912_);
lean_ctor_set(v___x_1931_, 2, v_options_1913_);
lean_ctor_set(v___x_1931_, 3, v_currRecDepth_1914_);
lean_ctor_set(v___x_1931_, 4, v_maxRecDepth_1915_);
lean_ctor_set(v___x_1931_, 5, v_ref_1930_);
lean_ctor_set(v___x_1931_, 6, v_currNamespace_1917_);
lean_ctor_set(v___x_1931_, 7, v_openDecls_1918_);
lean_ctor_set(v___x_1931_, 8, v_initHeartbeats_1919_);
lean_ctor_set(v___x_1931_, 9, v_maxHeartbeats_1920_);
lean_ctor_set(v___x_1931_, 10, v_quotContext_1921_);
lean_ctor_set(v___x_1931_, 11, v_currMacroScope_1922_);
lean_ctor_set(v___x_1931_, 12, v_cancelTk_x3f_1924_);
lean_ctor_set(v___x_1931_, 13, v_inheritedTraceOptions_1926_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*14, v_diag_1923_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*14 + 1, v_suppressElabErrors_1925_);
v___x_1932_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1929_);
lean_dec_ref(v_traces_1929_);
v_sz_1933_ = lean_array_size(v___x_1932_);
v___x_1934_ = ((size_t)0ULL);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3_spec__6(v_sz_1933_, v___x_1934_, v___x_1932_);
v_msg_1936_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1936_, 0, v_data_1903_);
lean_ctor_set(v_msg_1936_, 1, v_msg_1905_);
lean_ctor_set(v_msg_1936_, 2, v___x_1935_);
v___x_1937_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1936_, v___y_1906_, v___y_1907_, v___x_1931_, v___y_1909_);
lean_dec_ref_known(v___x_1931_, 14);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1975_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1975_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v_traceState_1943_; lean_object* v_env_1944_; lean_object* v_nextMacroScope_1945_; lean_object* v_ngen_1946_; lean_object* v_auxDeclNGen_1947_; lean_object* v_cache_1948_; lean_object* v_messages_1949_; lean_object* v_infoState_1950_; lean_object* v_snapshotTasks_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1974_; 
v___x_1942_ = lean_st_ref_take(v___y_1909_);
v_traceState_1943_ = lean_ctor_get(v___x_1942_, 4);
v_env_1944_ = lean_ctor_get(v___x_1942_, 0);
v_nextMacroScope_1945_ = lean_ctor_get(v___x_1942_, 1);
v_ngen_1946_ = lean_ctor_get(v___x_1942_, 2);
v_auxDeclNGen_1947_ = lean_ctor_get(v___x_1942_, 3);
v_cache_1948_ = lean_ctor_get(v___x_1942_, 5);
v_messages_1949_ = lean_ctor_get(v___x_1942_, 6);
v_infoState_1950_ = lean_ctor_get(v___x_1942_, 7);
v_snapshotTasks_1951_ = lean_ctor_get(v___x_1942_, 8);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1953_ = v___x_1942_;
v_isShared_1954_ = v_isSharedCheck_1974_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_snapshotTasks_1951_);
lean_inc(v_infoState_1950_);
lean_inc(v_messages_1949_);
lean_inc(v_cache_1948_);
lean_inc(v_traceState_1943_);
lean_inc(v_auxDeclNGen_1947_);
lean_inc(v_ngen_1946_);
lean_inc(v_nextMacroScope_1945_);
lean_inc(v_env_1944_);
lean_dec(v___x_1942_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1974_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
uint64_t v_tid_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1972_; 
v_tid_1955_ = lean_ctor_get_uint64(v_traceState_1943_, sizeof(void*)*1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_traceState_1943_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_traceState_1943_, 0);
lean_dec(v_unused_1973_);
v___x_1957_ = v_traceState_1943_;
v_isShared_1958_ = v_isSharedCheck_1972_;
goto v_resetjp_1956_;
}
else
{
lean_dec(v_traceState_1943_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1972_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v_ref_1904_);
lean_ctor_set(v___x_1959_, 1, v_a_1938_);
v___x_1960_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1902_, v___x_1959_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1960_);
lean_ctor_set_uint64(v_reuseFailAlloc_1971_, sizeof(void*)*1, v_tid_1955_);
v___x_1962_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1964_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 4, v___x_1962_);
v___x_1964_ = v___x_1953_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_env_1944_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_nextMacroScope_1945_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v_ngen_1946_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_auxDeclNGen_1947_);
lean_ctor_set(v_reuseFailAlloc_1970_, 4, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1970_, 5, v_cache_1948_);
lean_ctor_set(v_reuseFailAlloc_1970_, 6, v_messages_1949_);
lean_ctor_set(v_reuseFailAlloc_1970_, 7, v_infoState_1950_);
lean_ctor_set(v_reuseFailAlloc_1970_, 8, v_snapshotTasks_1951_);
v___x_1964_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1965_ = lean_st_ref_set(v___y_1909_, v___x_1964_);
v___x_1966_ = lean_box(0);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1966_);
v___x_1968_ = v___x_1940_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_1976_, lean_object* v_data_1977_, lean_object* v_ref_1978_, lean_object* v_msg_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___redArg(v_oldTraces_1976_, v_data_1977_, v_ref_1978_, v_msg_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6(lean_object* v_opts_1986_, lean_object* v_opt_1987_){
_start:
{
lean_object* v_name_1988_; lean_object* v_defValue_1989_; lean_object* v_map_1990_; lean_object* v___x_1991_; 
v_name_1988_ = lean_ctor_get(v_opt_1987_, 0);
v_defValue_1989_ = lean_ctor_get(v_opt_1987_, 1);
v_map_1990_ = lean_ctor_get(v_opts_1986_, 0);
v___x_1991_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1990_, v_name_1988_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_inc(v_defValue_1989_);
return v_defValue_1989_;
}
else
{
lean_object* v_val_1992_; 
v_val_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v___x_1991_, 1);
if (lean_obj_tag(v_val_1992_) == 3)
{
lean_object* v_v_1993_; 
v_v_1993_ = lean_ctor_get(v_val_1992_, 0);
lean_inc(v_v_1993_);
lean_dec_ref_known(v_val_1992_, 1);
return v_v_1993_;
}
else
{
lean_dec(v_val_1992_);
lean_inc(v_defValue_1989_);
return v_defValue_1989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6___boxed(lean_object* v_opts_1994_, lean_object* v_opt_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6(v_opts_1994_, v_opt_1995_);
lean_dec_ref(v_opt_1995_);
lean_dec_ref(v_opts_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg(lean_object* v_x_1997_){
_start:
{
if (lean_obj_tag(v_x_1997_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_a_1999_ = lean_ctor_get(v_x_1997_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_x_1997_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v_x_1997_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v_x_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set_tag(v___x_2001_, 1);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_a_2007_ = lean_ctor_get(v_x_1997_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_x_1997_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v_x_1997_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v_x_1997_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 0);
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg___boxed(lean_object* v_x_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg(v_x_2015_);
return v_res_2017_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__0));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2021_; double v___x_2022_; 
v___x_2021_ = lean_unsigned_to_nat(1000u);
v___x_2022_ = lean_float_of_nat(v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(lean_object* v_cls_2023_, uint8_t v_collapsed_2024_, lean_object* v_tag_2025_, lean_object* v_opts_2026_, uint8_t v_clsEnabled_2027_, lean_object* v_oldTraces_2028_, lean_object* v_msg_2029_, lean_object* v_resStartStop_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_fst_2038_; lean_object* v_snd_2039_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v_data_2043_; lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; lean_object* v___y_2051_; lean_object* v_a_2052_; uint8_t v___y_2067_; double v___y_2098_; 
v_fst_2038_ = lean_ctor_get(v_resStartStop_2030_, 0);
lean_inc(v_fst_2038_);
v_snd_2039_ = lean_ctor_get(v_resStartStop_2030_, 1);
lean_inc(v_snd_2039_);
lean_dec_ref(v_resStartStop_2030_);
v_fst_2046_ = lean_ctor_get(v_snd_2039_, 0);
lean_inc(v_fst_2046_);
v_snd_2047_ = lean_ctor_get(v_snd_2039_, 1);
lean_inc(v_snd_2047_);
lean_dec(v_snd_2039_);
v___x_2048_ = l_Lean_trace_profiler;
v___x_2049_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2026_, v___x_2048_);
if (v___x_2049_ == 0)
{
v___y_2067_ = v___x_2049_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2104_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2026_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; double v___x_2107_; double v___x_2108_; double v___x_2109_; 
v___x_2105_ = l_Lean_trace_profiler_threshold;
v___x_2106_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6(v_opts_2026_, v___x_2105_);
v___x_2107_ = lean_float_of_nat(v___x_2106_);
v___x_2108_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2);
v___x_2109_ = lean_float_div(v___x_2107_, v___x_2108_);
v___y_2098_ = v___x_2109_;
goto v___jp_2097_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; double v___x_2112_; 
v___x_2110_ = l_Lean_trace_profiler_threshold;
v___x_2111_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6(v_opts_2026_, v___x_2110_);
v___x_2112_ = lean_float_of_nat(v___x_2111_);
v___y_2098_ = v___x_2112_;
goto v___jp_2097_;
}
}
v___jp_2040_:
{
lean_object* v___x_2044_; 
lean_inc(v___y_2041_);
v___x_2044_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___redArg(v_oldTraces_2028_, v_data_2043_, v___y_2041_, v___y_2042_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2045_; 
lean_dec_ref_known(v___x_2044_, 1);
v___x_2045_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg(v_fst_2038_);
return v___x_2045_;
}
else
{
lean_dec(v_fst_2038_);
return v___x_2044_;
}
}
v___jp_2050_:
{
uint8_t v_result_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; double v___x_2056_; lean_object* v_data_2057_; 
v_result_2053_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__5(v_fst_2038_);
v___x_2054_ = lean_box(v_result_2053_);
v___x_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
v___x_2056_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2025_);
lean_inc_ref(v___x_2055_);
lean_inc(v_cls_2023_);
v_data_2057_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2057_, 0, v_cls_2023_);
lean_ctor_set(v_data_2057_, 1, v___x_2055_);
lean_ctor_set(v_data_2057_, 2, v_tag_2025_);
lean_ctor_set_float(v_data_2057_, sizeof(void*)*3, v___x_2056_);
lean_ctor_set_float(v_data_2057_, sizeof(void*)*3 + 8, v___x_2056_);
lean_ctor_set_uint8(v_data_2057_, sizeof(void*)*3 + 16, v_collapsed_2024_);
if (v___x_2049_ == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
lean_dec(v_snd_2047_);
lean_dec(v_fst_2046_);
lean_dec_ref(v_tag_2025_);
lean_dec(v_cls_2023_);
v___y_2041_ = v___y_2051_;
v___y_2042_ = v_a_2052_;
v_data_2043_ = v_data_2057_;
goto v___jp_2040_;
}
else
{
lean_object* v_data_2058_; double v___x_2059_; double v___x_2060_; 
lean_dec_ref_known(v_data_2057_, 3);
v_data_2058_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2058_, 0, v_cls_2023_);
lean_ctor_set(v_data_2058_, 1, v___x_2055_);
lean_ctor_set(v_data_2058_, 2, v_tag_2025_);
v___x_2059_ = lean_unbox_float(v_fst_2046_);
lean_dec(v_fst_2046_);
lean_ctor_set_float(v_data_2058_, sizeof(void*)*3, v___x_2059_);
v___x_2060_ = lean_unbox_float(v_snd_2047_);
lean_dec(v_snd_2047_);
lean_ctor_set_float(v_data_2058_, sizeof(void*)*3 + 8, v___x_2060_);
lean_ctor_set_uint8(v_data_2058_, sizeof(void*)*3 + 16, v_collapsed_2024_);
v___y_2041_ = v___y_2051_;
v___y_2042_ = v_a_2052_;
v_data_2043_ = v_data_2058_;
goto v___jp_2040_;
}
}
v___jp_2061_:
{
lean_object* v_ref_2062_; lean_object* v___x_2063_; 
v_ref_2062_ = lean_ctor_get(v___y_2035_, 5);
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2031_);
lean_inc(v_fst_2038_);
v___x_2063_ = lean_apply_8(v_msg_2029_, v_fst_2038_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, lean_box(0));
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___y_2051_ = v_ref_2062_;
v_a_2052_ = v_a_2064_;
goto v___jp_2050_;
}
else
{
lean_object* v___x_2065_; 
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1);
v___y_2051_ = v_ref_2062_;
v_a_2052_ = v___x_2065_;
goto v___jp_2050_;
}
}
v___jp_2066_:
{
if (v_clsEnabled_2027_ == 0)
{
if (v___y_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v_traceState_2069_; lean_object* v_env_2070_; lean_object* v_nextMacroScope_2071_; lean_object* v_ngen_2072_; lean_object* v_auxDeclNGen_2073_; lean_object* v_cache_2074_; lean_object* v_messages_2075_; lean_object* v_infoState_2076_; lean_object* v_snapshotTasks_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_snd_2047_);
lean_dec(v_fst_2046_);
lean_dec_ref(v_msg_2029_);
lean_dec_ref(v_tag_2025_);
lean_dec(v_cls_2023_);
v___x_2068_ = lean_st_ref_take(v___y_2036_);
v_traceState_2069_ = lean_ctor_get(v___x_2068_, 4);
v_env_2070_ = lean_ctor_get(v___x_2068_, 0);
v_nextMacroScope_2071_ = lean_ctor_get(v___x_2068_, 1);
v_ngen_2072_ = lean_ctor_get(v___x_2068_, 2);
v_auxDeclNGen_2073_ = lean_ctor_get(v___x_2068_, 3);
v_cache_2074_ = lean_ctor_get(v___x_2068_, 5);
v_messages_2075_ = lean_ctor_get(v___x_2068_, 6);
v_infoState_2076_ = lean_ctor_get(v___x_2068_, 7);
v_snapshotTasks_2077_ = lean_ctor_get(v___x_2068_, 8);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2079_ = v___x_2068_;
v_isShared_2080_ = v_isSharedCheck_2096_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_snapshotTasks_2077_);
lean_inc(v_infoState_2076_);
lean_inc(v_messages_2075_);
lean_inc(v_cache_2074_);
lean_inc(v_traceState_2069_);
lean_inc(v_auxDeclNGen_2073_);
lean_inc(v_ngen_2072_);
lean_inc(v_nextMacroScope_2071_);
lean_inc(v_env_2070_);
lean_dec(v___x_2068_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2096_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
uint64_t v_tid_2081_; lean_object* v_traces_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2095_; 
v_tid_2081_ = lean_ctor_get_uint64(v_traceState_2069_, sizeof(void*)*1);
v_traces_2082_ = lean_ctor_get(v_traceState_2069_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_traceState_2069_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2084_ = v_traceState_2069_;
v_isShared_2085_ = v_isSharedCheck_2095_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_traces_2082_);
lean_dec(v_traceState_2069_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2095_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2028_, v_traces_2082_);
lean_dec_ref(v_traces_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2086_);
lean_ctor_set_uint64(v_reuseFailAlloc_2094_, sizeof(void*)*1, v_tid_2081_);
v___x_2088_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2090_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 4, v___x_2088_);
v___x_2090_ = v___x_2079_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_env_2070_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_nextMacroScope_2071_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_ngen_2072_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v_auxDeclNGen_2073_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2093_, 5, v_cache_2074_);
lean_ctor_set(v_reuseFailAlloc_2093_, 6, v_messages_2075_);
lean_ctor_set(v_reuseFailAlloc_2093_, 7, v_infoState_2076_);
lean_ctor_set(v_reuseFailAlloc_2093_, 8, v_snapshotTasks_2077_);
v___x_2090_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_st_ref_set(v___y_2036_, v___x_2090_);
v___x_2092_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg(v_fst_2038_);
return v___x_2092_;
}
}
}
}
}
else
{
goto v___jp_2061_;
}
}
else
{
goto v___jp_2061_;
}
}
v___jp_2097_:
{
double v___x_2099_; double v___x_2100_; double v___x_2101_; uint8_t v___x_2102_; 
v___x_2099_ = lean_unbox_float(v_snd_2047_);
v___x_2100_ = lean_unbox_float(v_fst_2046_);
v___x_2101_ = lean_float_sub(v___x_2099_, v___x_2100_);
v___x_2102_ = lean_float_decLt(v___y_2098_, v___x_2101_);
v___y_2067_ = v___x_2102_;
goto v___jp_2066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___boxed(lean_object* v_cls_2113_, lean_object* v_collapsed_2114_, lean_object* v_tag_2115_, lean_object* v_opts_2116_, lean_object* v_clsEnabled_2117_, lean_object* v_oldTraces_2118_, lean_object* v_msg_2119_, lean_object* v_resStartStop_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
uint8_t v_collapsed_boxed_2128_; uint8_t v_clsEnabled_boxed_2129_; lean_object* v_res_2130_; 
v_collapsed_boxed_2128_ = lean_unbox(v_collapsed_2114_);
v_clsEnabled_boxed_2129_ = lean_unbox(v_clsEnabled_2117_);
v_res_2130_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v_cls_2113_, v_collapsed_boxed_2128_, v_tag_2115_, v_opts_2116_, v_clsEnabled_boxed_2129_, v_oldTraces_2118_, v_msg_2119_, v_resStartStop_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec_ref(v_opts_2116_);
return v_res_2130_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(lean_object* v_a_2134_, lean_object* v_x_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1);
v___x_2144_ = lean_unsigned_to_nat(30u);
v___x_2145_ = l_Lean_inlineExprTrailing(v_a_2134_, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2143_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed(lean_object* v_a_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(v_a_2148_, v_x_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec_ref(v_x_2149_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15_spec__16___redArg(lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_){
_start:
{
lean_object* v_ks_2162_; lean_object* v_vs_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2187_; 
v_ks_2162_ = lean_ctor_get(v_x_2158_, 0);
v_vs_2163_ = lean_ctor_get(v_x_2158_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_x_2158_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2165_ = v_x_2158_;
v_isShared_2166_ = v_isSharedCheck_2187_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_vs_2163_);
lean_inc(v_ks_2162_);
lean_dec(v_x_2158_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2187_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = lean_array_get_size(v_ks_2162_);
v___x_2168_ = lean_nat_dec_lt(v_x_2159_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
lean_dec(v_x_2159_);
v___x_2169_ = lean_array_push(v_ks_2162_, v_x_2160_);
v___x_2170_ = lean_array_push(v_vs_2163_, v_x_2161_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 1, v___x_2170_);
lean_ctor_set(v___x_2165_, 0, v___x_2169_);
v___x_2172_ = v___x_2165_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
else
{
lean_object* v_k_x27_2174_; uint8_t v___x_2175_; 
v_k_x27_2174_ = lean_array_fget_borrowed(v_ks_2162_, v_x_2159_);
v___x_2175_ = l_Lean_instBEqMVarId_beq(v_x_2160_, v_k_x27_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2177_; 
if (v_isShared_2166_ == 0)
{
v___x_2177_ = v___x_2165_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_ks_2162_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_vs_2163_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_x_2159_, v___x_2178_);
lean_dec(v_x_2159_);
v_x_2158_ = v___x_2177_;
v_x_2159_ = v___x_2179_;
goto _start;
}
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2182_ = lean_array_fset(v_ks_2162_, v_x_2159_, v_x_2160_);
v___x_2183_ = lean_array_fset(v_vs_2163_, v_x_2159_, v_x_2161_);
lean_dec(v_x_2159_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 1, v___x_2183_);
lean_ctor_set(v___x_2165_, 0, v___x_2182_);
v___x_2185_ = v___x_2165_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15___redArg(lean_object* v_n_2188_, lean_object* v_k_2189_, lean_object* v_v_2190_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15_spec__16___redArg(v_n_2188_, v___x_2191_, v_k_2189_, v_v_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg(lean_object* v_x_2194_, size_t v_x_2195_, size_t v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 0)
{
lean_object* v_es_2199_; size_t v___x_2200_; size_t v___x_2201_; lean_object* v_j_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_es_2199_ = lean_ctor_get(v_x_2194_, 0);
v___x_2200_ = ((size_t)31ULL);
v___x_2201_ = lean_usize_land(v_x_2195_, v___x_2200_);
v_j_2202_ = lean_usize_to_nat(v___x_2201_);
v___x_2203_ = lean_array_get_size(v_es_2199_);
v___x_2204_ = lean_nat_dec_lt(v_j_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_dec(v_j_2202_);
lean_dec(v_x_2198_);
lean_dec(v_x_2197_);
return v_x_2194_;
}
else
{
lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2243_; 
lean_inc_ref(v_es_2199_);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_x_2194_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v_x_2194_, 0);
lean_dec(v_unused_2244_);
v___x_2206_ = v_x_2194_;
v_isShared_2207_ = v_isSharedCheck_2243_;
goto v_resetjp_2205_;
}
else
{
lean_dec(v_x_2194_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2243_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_v_2208_; lean_object* v___x_2209_; lean_object* v_xs_x27_2210_; lean_object* v___y_2212_; 
v_v_2208_ = lean_array_fget(v_es_2199_, v_j_2202_);
v___x_2209_ = lean_box(0);
v_xs_x27_2210_ = lean_array_fset(v_es_2199_, v_j_2202_, v___x_2209_);
switch(lean_obj_tag(v_v_2208_))
{
case 0:
{
lean_object* v_key_2217_; lean_object* v_val_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2228_; 
v_key_2217_ = lean_ctor_get(v_v_2208_, 0);
v_val_2218_ = lean_ctor_get(v_v_2208_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_v_2208_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2220_ = v_v_2208_;
v_isShared_2221_ = v_isSharedCheck_2228_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_val_2218_);
lean_inc(v_key_2217_);
lean_dec(v_v_2208_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2228_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
uint8_t v___x_2222_; 
v___x_2222_ = l_Lean_instBEqMVarId_beq(v_x_2197_, v_key_2217_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_del_object(v___x_2220_);
v___x_2223_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2217_, v_val_2218_, v_x_2197_, v_x_2198_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
v___y_2212_ = v___x_2224_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2226_; 
lean_dec(v_val_2218_);
lean_dec(v_key_2217_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v_x_2198_);
lean_ctor_set(v___x_2220_, 0, v_x_2197_);
v___x_2226_ = v___x_2220_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_x_2197_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_x_2198_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
v___y_2212_ = v___x_2226_;
goto v___jp_2211_;
}
}
}
}
case 1:
{
lean_object* v_node_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2241_; 
v_node_2229_ = lean_ctor_get(v_v_2208_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_v_2208_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2231_ = v_v_2208_;
v_isShared_2232_ = v_isSharedCheck_2241_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_node_2229_);
lean_dec(v_v_2208_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2241_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
size_t v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2233_ = ((size_t)5ULL);
v___x_2234_ = lean_usize_shift_right(v_x_2195_, v___x_2233_);
v___x_2235_ = ((size_t)1ULL);
v___x_2236_ = lean_usize_add(v_x_2196_, v___x_2235_);
v___x_2237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg(v_node_2229_, v___x_2234_, v___x_2236_, v_x_2197_, v_x_2198_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2237_);
v___x_2239_ = v___x_2231_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v___y_2212_ = v___x_2239_;
goto v___jp_2211_;
}
}
}
default: 
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_x_2197_);
lean_ctor_set(v___x_2242_, 1, v_x_2198_);
v___y_2212_ = v___x_2242_;
goto v___jp_2211_;
}
}
v___jp_2211_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = lean_array_fset(v_xs_x27_2210_, v_j_2202_, v___y_2212_);
lean_dec(v_j_2202_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2213_);
v___x_2215_ = v___x_2206_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
}
else
{
lean_object* v_ks_2245_; lean_object* v_vs_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2266_; 
v_ks_2245_ = lean_ctor_get(v_x_2194_, 0);
v_vs_2246_ = lean_ctor_get(v_x_2194_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_x_2194_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2248_ = v_x_2194_;
v_isShared_2249_ = v_isSharedCheck_2266_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_vs_2246_);
lean_inc(v_ks_2245_);
lean_dec(v_x_2194_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2266_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_ks_2245_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_vs_2246_);
v___x_2251_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v_newNode_2252_; uint8_t v___y_2254_; size_t v___x_2260_; uint8_t v___x_2261_; 
v_newNode_2252_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15___redArg(v___x_2251_, v_x_2197_, v_x_2198_);
v___x_2260_ = ((size_t)7ULL);
v___x_2261_ = lean_usize_dec_le(v___x_2260_, v_x_2196_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2262_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2252_);
v___x_2263_ = lean_unsigned_to_nat(4u);
v___x_2264_ = lean_nat_dec_lt(v___x_2262_, v___x_2263_);
lean_dec(v___x_2262_);
v___y_2254_ = v___x_2264_;
goto v___jp_2253_;
}
else
{
v___y_2254_ = v___x_2261_;
goto v___jp_2253_;
}
v___jp_2253_:
{
if (v___y_2254_ == 0)
{
lean_object* v_ks_2255_; lean_object* v_vs_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_ks_2255_ = lean_ctor_get(v_newNode_2252_, 0);
lean_inc_ref(v_ks_2255_);
v_vs_2256_ = lean_ctor_get(v_newNode_2252_, 1);
lean_inc_ref(v_vs_2256_);
lean_dec_ref(v_newNode_2252_);
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg___closed__0);
v___x_2259_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___redArg(v_x_2196_, v_ks_2255_, v_vs_2256_, v___x_2257_, v___x_2258_);
lean_dec_ref(v_vs_2256_);
lean_dec_ref(v_ks_2255_);
return v___x_2259_;
}
else
{
return v_newNode_2252_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___redArg(size_t v_depth_2267_, lean_object* v_keys_2268_, lean_object* v_vals_2269_, lean_object* v_i_2270_, lean_object* v_entries_2271_){
_start:
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = lean_array_get_size(v_keys_2268_);
v___x_2273_ = lean_nat_dec_lt(v_i_2270_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_dec(v_i_2270_);
return v_entries_2271_;
}
else
{
lean_object* v_k_2274_; lean_object* v_v_2275_; uint64_t v___x_2276_; size_t v_h_2277_; size_t v___x_2278_; lean_object* v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; size_t v___x_2282_; size_t v_h_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_k_2274_ = lean_array_fget_borrowed(v_keys_2268_, v_i_2270_);
v_v_2275_ = lean_array_fget_borrowed(v_vals_2269_, v_i_2270_);
v___x_2276_ = l_Lean_instHashableMVarId_hash(v_k_2274_);
v_h_2277_ = lean_uint64_to_usize(v___x_2276_);
v___x_2278_ = ((size_t)5ULL);
v___x_2279_ = lean_unsigned_to_nat(1u);
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_sub(v_depth_2267_, v___x_2280_);
v___x_2282_ = lean_usize_mul(v___x_2278_, v___x_2281_);
v_h_2283_ = lean_usize_shift_right(v_h_2277_, v___x_2282_);
v___x_2284_ = lean_nat_add(v_i_2270_, v___x_2279_);
lean_dec(v_i_2270_);
lean_inc(v_v_2275_);
lean_inc(v_k_2274_);
v___x_2285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg(v_entries_2271_, v_h_2283_, v_depth_2267_, v_k_2274_, v_v_2275_);
v_i_2270_ = v___x_2284_;
v_entries_2271_ = v___x_2285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___redArg___boxed(lean_object* v_depth_2287_, lean_object* v_keys_2288_, lean_object* v_vals_2289_, lean_object* v_i_2290_, lean_object* v_entries_2291_){
_start:
{
size_t v_depth_boxed_2292_; lean_object* v_res_2293_; 
v_depth_boxed_2292_ = lean_unbox_usize(v_depth_2287_);
lean_dec(v_depth_2287_);
v_res_2293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___redArg(v_depth_boxed_2292_, v_keys_2288_, v_vals_2289_, v_i_2290_, v_entries_2291_);
lean_dec_ref(v_vals_2289_);
lean_dec_ref(v_keys_2288_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_x_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
size_t v_x_18784__boxed_2299_; size_t v_x_18785__boxed_2300_; lean_object* v_res_2301_; 
v_x_18784__boxed_2299_ = lean_unbox_usize(v_x_2295_);
lean_dec(v_x_2295_);
v_x_18785__boxed_2300_ = lean_unbox_usize(v_x_2296_);
lean_dec(v_x_2296_);
v_res_2301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg(v_x_2294_, v_x_18784__boxed_2299_, v_x_18785__boxed_2300_, v_x_2297_, v_x_2298_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___redArg(lean_object* v_x_2302_, lean_object* v_x_2303_, lean_object* v_x_2304_){
_start:
{
uint64_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; lean_object* v___x_2308_; 
v___x_2305_ = l_Lean_instHashableMVarId_hash(v_x_2303_);
v___x_2306_ = lean_uint64_to_usize(v___x_2305_);
v___x_2307_ = ((size_t)1ULL);
v___x_2308_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg(v_x_2302_, v___x_2306_, v___x_2307_, v_x_2303_, v_x_2304_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg(lean_object* v_mvarId_2309_, lean_object* v_val_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; lean_object* v_mctx_2314_; lean_object* v_cache_2315_; lean_object* v_zetaDeltaFVarIds_2316_; lean_object* v_postponed_2317_; lean_object* v_diag_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2346_; 
v___x_2313_ = lean_st_ref_take(v___y_2311_);
v_mctx_2314_ = lean_ctor_get(v___x_2313_, 0);
v_cache_2315_ = lean_ctor_get(v___x_2313_, 1);
v_zetaDeltaFVarIds_2316_ = lean_ctor_get(v___x_2313_, 2);
v_postponed_2317_ = lean_ctor_get(v___x_2313_, 3);
v_diag_2318_ = lean_ctor_get(v___x_2313_, 4);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2320_ = v___x_2313_;
v_isShared_2321_ = v_isSharedCheck_2346_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_diag_2318_);
lean_inc(v_postponed_2317_);
lean_inc(v_zetaDeltaFVarIds_2316_);
lean_inc(v_cache_2315_);
lean_inc(v_mctx_2314_);
lean_dec(v___x_2313_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2346_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_depth_2322_; lean_object* v_levelAssignDepth_2323_; lean_object* v_lmvarCounter_2324_; lean_object* v_mvarCounter_2325_; lean_object* v_lDecls_2326_; lean_object* v_decls_2327_; lean_object* v_userNames_2328_; lean_object* v_lAssignment_2329_; lean_object* v_eAssignment_2330_; lean_object* v_dAssignment_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2345_; 
v_depth_2322_ = lean_ctor_get(v_mctx_2314_, 0);
v_levelAssignDepth_2323_ = lean_ctor_get(v_mctx_2314_, 1);
v_lmvarCounter_2324_ = lean_ctor_get(v_mctx_2314_, 2);
v_mvarCounter_2325_ = lean_ctor_get(v_mctx_2314_, 3);
v_lDecls_2326_ = lean_ctor_get(v_mctx_2314_, 4);
v_decls_2327_ = lean_ctor_get(v_mctx_2314_, 5);
v_userNames_2328_ = lean_ctor_get(v_mctx_2314_, 6);
v_lAssignment_2329_ = lean_ctor_get(v_mctx_2314_, 7);
v_eAssignment_2330_ = lean_ctor_get(v_mctx_2314_, 8);
v_dAssignment_2331_ = lean_ctor_get(v_mctx_2314_, 9);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_mctx_2314_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2333_ = v_mctx_2314_;
v_isShared_2334_ = v_isSharedCheck_2345_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_dAssignment_2331_);
lean_inc(v_eAssignment_2330_);
lean_inc(v_lAssignment_2329_);
lean_inc(v_userNames_2328_);
lean_inc(v_decls_2327_);
lean_inc(v_lDecls_2326_);
lean_inc(v_mvarCounter_2325_);
lean_inc(v_lmvarCounter_2324_);
lean_inc(v_levelAssignDepth_2323_);
lean_inc(v_depth_2322_);
lean_dec(v_mctx_2314_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2345_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2335_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___redArg(v_eAssignment_2330_, v_mvarId_2309_, v_val_2310_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 8, v___x_2335_);
v___x_2337_ = v___x_2333_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_depth_2322_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_levelAssignDepth_2323_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_lmvarCounter_2324_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_mvarCounter_2325_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v_lDecls_2326_);
lean_ctor_set(v_reuseFailAlloc_2344_, 5, v_decls_2327_);
lean_ctor_set(v_reuseFailAlloc_2344_, 6, v_userNames_2328_);
lean_ctor_set(v_reuseFailAlloc_2344_, 7, v_lAssignment_2329_);
lean_ctor_set(v_reuseFailAlloc_2344_, 8, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2344_, 9, v_dAssignment_2331_);
v___x_2337_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2337_);
v___x_2339_ = v___x_2320_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_cache_2315_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_zetaDeltaFVarIds_2316_);
lean_ctor_set(v_reuseFailAlloc_2343_, 3, v_postponed_2317_);
lean_ctor_set(v_reuseFailAlloc_2343_, 4, v_diag_2318_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_st_ref_set(v___y_2311_, v___x_2339_);
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg___boxed(lean_object* v_mvarId_2347_, lean_object* v_val_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg(v_mvarId_2347_, v_val_2348_, v___y_2349_);
lean_dec(v___y_2349_);
return v_res_2351_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(lean_object* v_keys_2352_, lean_object* v_i_2353_, lean_object* v_k_2354_){
_start:
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = lean_array_get_size(v_keys_2352_);
v___x_2356_ = lean_nat_dec_lt(v_i_2353_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_dec(v_i_2353_);
return v___x_2356_;
}
else
{
lean_object* v_k_x27_2357_; uint8_t v___x_2358_; 
v_k_x27_2357_ = lean_array_fget_borrowed(v_keys_2352_, v_i_2353_);
v___x_2358_ = l_Lean_instBEqMVarId_beq(v_k_2354_, v_k_x27_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_nat_add(v_i_2353_, v___x_2359_);
lean_dec(v_i_2353_);
v_i_2353_ = v___x_2360_;
goto _start;
}
else
{
lean_dec(v_i_2353_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_keys_2362_, lean_object* v_i_2363_, lean_object* v_k_2364_){
_start:
{
uint8_t v_res_2365_; lean_object* v_r_2366_; 
v_res_2365_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2362_, v_i_2363_, v_k_2364_);
lean_dec(v_k_2364_);
lean_dec_ref(v_keys_2362_);
v_r_2366_ = lean_box(v_res_2365_);
return v_r_2366_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(lean_object* v_x_2367_, size_t v_x_2368_, lean_object* v_x_2369_){
_start:
{
if (lean_obj_tag(v_x_2367_) == 0)
{
lean_object* v_es_2370_; lean_object* v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; lean_object* v_j_2374_; lean_object* v___x_2375_; 
v_es_2370_ = lean_ctor_get(v_x_2367_, 0);
v___x_2371_ = lean_box(2);
v___x_2372_ = ((size_t)31ULL);
v___x_2373_ = lean_usize_land(v_x_2368_, v___x_2372_);
v_j_2374_ = lean_usize_to_nat(v___x_2373_);
v___x_2375_ = lean_array_get_borrowed(v___x_2371_, v_es_2370_, v_j_2374_);
lean_dec(v_j_2374_);
switch(lean_obj_tag(v___x_2375_))
{
case 0:
{
lean_object* v_key_2376_; uint8_t v___x_2377_; 
v_key_2376_ = lean_ctor_get(v___x_2375_, 0);
v___x_2377_ = l_Lean_instBEqMVarId_beq(v_x_2369_, v_key_2376_);
return v___x_2377_;
}
case 1:
{
lean_object* v_node_2378_; size_t v___x_2379_; size_t v___x_2380_; 
v_node_2378_ = lean_ctor_get(v___x_2375_, 0);
v___x_2379_ = ((size_t)5ULL);
v___x_2380_ = lean_usize_shift_right(v_x_2368_, v___x_2379_);
v_x_2367_ = v_node_2378_;
v_x_2368_ = v___x_2380_;
goto _start;
}
default: 
{
uint8_t v___x_2382_; 
v___x_2382_ = 0;
return v___x_2382_;
}
}
}
else
{
lean_object* v_ks_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v_ks_2383_ = lean_ctor_get(v_x_2367_, 0);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_ks_2383_, v___x_2384_, v_x_2369_);
return v___x_2385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_2386_, lean_object* v_x_2387_, lean_object* v_x_2388_){
_start:
{
size_t v_x_19010__boxed_2389_; uint8_t v_res_2390_; lean_object* v_r_2391_; 
v_x_19010__boxed_2389_ = lean_unbox_usize(v_x_2387_);
lean_dec(v_x_2387_);
v_res_2390_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2386_, v_x_19010__boxed_2389_, v_x_2388_);
lean_dec(v_x_2388_);
lean_dec_ref(v_x_2386_);
v_r_2391_ = lean_box(v_res_2390_);
return v_r_2391_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(lean_object* v_x_2392_, lean_object* v_x_2393_){
_start:
{
uint64_t v___x_2394_; size_t v___x_2395_; uint8_t v___x_2396_; 
v___x_2394_ = l_Lean_instHashableMVarId_hash(v_x_2393_);
v___x_2395_ = lean_uint64_to_usize(v___x_2394_);
v___x_2396_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2392_, v___x_2395_, v_x_2393_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg___boxed(lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
uint8_t v_res_2399_; lean_object* v_r_2400_; 
v_res_2399_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2397_, v_x_2398_);
lean_dec(v_x_2398_);
lean_dec_ref(v_x_2397_);
v_r_2400_ = lean_box(v_res_2399_);
return v_r_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(lean_object* v_mvarId_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v_mctx_2405_; lean_object* v_eAssignment_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2404_ = lean_st_ref_get(v___y_2402_);
v_mctx_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc_ref(v_mctx_2405_);
lean_dec(v___x_2404_);
v_eAssignment_2406_ = lean_ctor_get(v_mctx_2405_, 8);
lean_inc_ref(v_eAssignment_2406_);
lean_dec_ref(v_mctx_2405_);
v___x_2407_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_eAssignment_2406_, v_mvarId_2401_);
lean_dec_ref(v_eAssignment_2406_);
v___x_2408_ = lean_box(v___x_2407_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg___boxed(lean_object* v_mvarId_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec(v_mvarId_2410_);
return v_res_2413_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2414_; double v___x_2415_; 
v___x_2414_ = lean_unsigned_to_nat(1000000000u);
v___x_2415_ = lean_float_of_nat(v___x_2414_);
return v___x_2415_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__1));
v___x_2418_ = l_Lean_stringToMessageData(v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(lean_object* v___x_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v___x_2419_, v___y_2423_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2625_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2625_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2625_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
uint8_t v___x_2435_; 
v___x_2435_ = lean_unbox(v_a_2431_);
lean_dec(v_a_2431_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; 
lean_del_object(v___x_2433_);
lean_inc(v___x_2419_);
v___x_2436_ = l_Lean_MVarId_getType(v___x_2419_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_options_2437_; lean_object* v_a_2438_; lean_object* v_inheritedTraceOptions_2439_; uint8_t v_hasTrace_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v_options_2437_ = lean_ctor_get(v___y_2424_, 2);
v_a_2438_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2436_, 1);
v_inheritedTraceOptions_2439_ = lean_ctor_get(v___y_2424_, 13);
v_hasTrace_2440_ = lean_ctor_get_uint8(v_options_2437_, sizeof(void*)*1);
v___x_2441_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_2442_ = lean_bool_not(v_hasTrace_2440_);
if (v___x_2442_ == 0)
{
lean_object* v___f_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___y_2447_; uint8_t v___y_2448_; lean_object* v___y_2449_; lean_object* v_a_2450_; lean_object* v___y_2463_; uint8_t v___y_2464_; lean_object* v___y_2465_; lean_object* v_a_2466_; lean_object* v___y_2469_; uint8_t v___y_2470_; lean_object* v___y_2471_; lean_object* v_a_2472_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2480_; uint8_t v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2487_; uint8_t v___y_2488_; lean_object* v___y_2489_; lean_object* v_a_2490_; lean_object* v___y_2500_; uint8_t v___y_2501_; lean_object* v___y_2502_; lean_object* v_a_2503_; lean_object* v___y_2506_; uint8_t v___y_2507_; lean_object* v___y_2508_; lean_object* v_a_2509_; lean_object* v___y_2512_; uint8_t v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; uint8_t v___y_2524_; uint8_t v_a_2562_; 
lean_inc(v_a_2438_);
v___f_2443_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2443_, 0, v_a_2438_);
v___x_2444_ = 1;
v___x_2445_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
if (v_hasTrace_2440_ == 0)
{
v_a_2562_ = v_hasTrace_2440_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2584_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2439_, v_options_2437_, v___x_2583_);
if (v___x_2584_ == 0)
{
v_a_2562_ = v___x_2584_;
goto v___jp_2561_;
}
else
{
v___y_2524_ = v___x_2584_;
goto v___jp_2523_;
}
}
v___jp_2446_:
{
lean_object* v___x_2451_; double v___x_2452_; double v___x_2453_; double v___x_2454_; double v___x_2455_; double v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2451_ = lean_io_mono_nanos_now();
v___x_2452_ = lean_float_of_nat(v___y_2447_);
v___x_2453_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_2454_ = lean_float_div(v___x_2452_, v___x_2453_);
v___x_2455_ = lean_float_of_nat(v___x_2451_);
v___x_2456_ = lean_float_div(v___x_2455_, v___x_2453_);
v___x_2457_ = lean_box_float(v___x_2454_);
v___x_2458_ = lean_box_float(v___x_2456_);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v_a_2450_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v___x_2441_, v___x_2444_, v___x_2445_, v_options_2437_, v___y_2448_, v___y_2449_, v___f_2443_, v___x_2460_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2461_;
}
v___jp_2462_:
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2466_);
v___y_2447_ = v___y_2463_;
v___y_2448_ = v___y_2464_;
v___y_2449_ = v___y_2465_;
v_a_2450_ = v___x_2467_;
goto v___jp_2446_;
}
v___jp_2468_:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_a_2472_);
v___y_2447_ = v___y_2469_;
v___y_2448_ = v___y_2470_;
v___y_2449_ = v___y_2471_;
v_a_2450_ = v___x_2473_;
goto v___jp_2446_;
}
v___jp_2474_:
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_box(0);
v___y_2469_ = v___y_2475_;
v___y_2470_ = v___y_2476_;
v___y_2471_ = v___y_2477_;
v_a_2472_ = v___x_2478_;
goto v___jp_2468_;
}
v___jp_2479_:
{
if (lean_obj_tag(v___y_2483_) == 0)
{
lean_object* v_a_2484_; 
v_a_2484_ = lean_ctor_get(v___y_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___y_2483_, 1);
v___y_2469_ = v___y_2480_;
v___y_2470_ = v___y_2481_;
v___y_2471_ = v___y_2482_;
v_a_2472_ = v_a_2484_;
goto v___jp_2468_;
}
else
{
lean_object* v_a_2485_; 
v_a_2485_ = lean_ctor_get(v___y_2483_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___y_2483_, 1);
v___y_2463_ = v___y_2480_;
v___y_2464_ = v___y_2481_;
v___y_2465_ = v___y_2482_;
v_a_2466_ = v_a_2485_;
goto v___jp_2462_;
}
}
v___jp_2486_:
{
lean_object* v___x_2491_; double v___x_2492_; double v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2491_ = lean_io_get_num_heartbeats();
v___x_2492_ = lean_float_of_nat(v___y_2487_);
v___x_2493_ = lean_float_of_nat(v___x_2491_);
v___x_2494_ = lean_box_float(v___x_2492_);
v___x_2495_ = lean_box_float(v___x_2493_);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v_a_2490_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v___x_2441_, v___x_2444_, v___x_2445_, v_options_2437_, v___y_2488_, v___y_2489_, v___f_2443_, v___x_2497_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2498_;
}
v___jp_2499_:
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_a_2503_);
v___y_2487_ = v___y_2500_;
v___y_2488_ = v___y_2501_;
v___y_2489_ = v___y_2502_;
v_a_2490_ = v___x_2504_;
goto v___jp_2486_;
}
v___jp_2505_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_a_2509_);
v___y_2487_ = v___y_2506_;
v___y_2488_ = v___y_2507_;
v___y_2489_ = v___y_2508_;
v_a_2490_ = v___x_2510_;
goto v___jp_2486_;
}
v___jp_2511_:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_box(0);
v___y_2506_ = v___y_2512_;
v___y_2507_ = v___y_2513_;
v___y_2508_ = v___y_2514_;
v_a_2509_ = v___x_2515_;
goto v___jp_2505_;
}
v___jp_2516_:
{
if (lean_obj_tag(v___y_2520_) == 0)
{
lean_object* v_a_2521_; 
v_a_2521_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___y_2520_, 1);
v___y_2506_ = v___y_2517_;
v___y_2507_ = v___y_2518_;
v___y_2508_ = v___y_2519_;
v_a_2509_ = v_a_2521_;
goto v___jp_2505_;
}
else
{
lean_object* v_a_2522_; 
v_a_2522_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___y_2520_, 1);
v___y_2500_ = v___y_2517_;
v___y_2501_ = v___y_2518_;
v___y_2502_ = v___y_2519_;
v_a_2503_ = v_a_2522_;
goto v___jp_2499_;
}
}
v___jp_2523_:
{
lean_object* v___x_2525_; 
v___x_2525_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___y_2425_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2528_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2437_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_io_mono_nanos_now();
v___x_2530_ = l_Lean_Meta_mkDefault(v_a_2438_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc_n(v_a_2531_, 2);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg(v___x_2419_, v_a_2531_, v___y_2423_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_dec_ref_known(v___x_2532_, 1);
if (v_hasTrace_2440_ == 0)
{
lean_dec(v_a_2531_);
v___y_2475_ = v___x_2529_;
v___y_2476_ = v___y_2524_;
v___y_2477_ = v_a_2526_;
goto v___jp_2474_;
}
else
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2533_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2534_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2439_, v_options_2437_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_dec(v_a_2531_);
v___y_2475_ = v___x_2529_;
v___y_2476_ = v___y_2524_;
v___y_2477_ = v_a_2526_;
goto v___jp_2474_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2536_ = lean_unsigned_to_nat(30u);
v___x_2537_ = l_Lean_inlineExprTrailing(v_a_2531_, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2535_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2441_, v___x_2538_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
v___y_2480_ = v___x_2529_;
v___y_2481_ = v___y_2524_;
v___y_2482_ = v_a_2526_;
v___y_2483_ = v___x_2539_;
goto v___jp_2479_;
}
}
}
else
{
lean_dec(v_a_2531_);
v___y_2480_ = v___x_2529_;
v___y_2481_ = v___y_2524_;
v___y_2482_ = v_a_2526_;
v___y_2483_ = v___x_2532_;
goto v___jp_2479_;
}
}
else
{
lean_object* v_a_2540_; 
lean_dec(v___x_2419_);
v_a_2540_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2530_, 1);
v___y_2463_ = v___x_2529_;
v___y_2464_ = v___y_2524_;
v___y_2465_ = v_a_2526_;
v_a_2466_ = v_a_2540_;
goto v___jp_2462_;
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_io_get_num_heartbeats();
v___x_2542_ = l_Lean_Meta_mkDefault(v_a_2438_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_n(v_a_2543_, 2);
lean_dec_ref_known(v___x_2542_, 1);
v___x_2544_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg(v___x_2419_, v_a_2543_, v___y_2423_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_dec_ref_known(v___x_2544_, 1);
if (v_hasTrace_2440_ == 0)
{
lean_dec(v_a_2543_);
v___y_2512_ = v___x_2541_;
v___y_2513_ = v___y_2524_;
v___y_2514_ = v_a_2526_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2545_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2546_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2439_, v_options_2437_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_dec(v_a_2543_);
v___y_2512_ = v___x_2541_;
v___y_2513_ = v___y_2524_;
v___y_2514_ = v_a_2526_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2547_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2548_ = lean_unsigned_to_nat(30u);
v___x_2549_ = l_Lean_inlineExprTrailing(v_a_2543_, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2547_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2441_, v___x_2550_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
v___y_2517_ = v___x_2541_;
v___y_2518_ = v___y_2524_;
v___y_2519_ = v_a_2526_;
v___y_2520_ = v___x_2551_;
goto v___jp_2516_;
}
}
}
else
{
lean_dec(v_a_2543_);
v___y_2517_ = v___x_2541_;
v___y_2518_ = v___y_2524_;
v___y_2519_ = v_a_2526_;
v___y_2520_ = v___x_2544_;
goto v___jp_2516_;
}
}
else
{
lean_object* v_a_2552_; 
lean_dec(v___x_2419_);
v_a_2552_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2542_, 1);
v___y_2500_ = v___x_2541_;
v___y_2501_ = v___y_2524_;
v___y_2502_ = v_a_2526_;
v_a_2503_ = v_a_2552_;
goto v___jp_2499_;
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v___f_2443_);
lean_dec(v_a_2438_);
lean_dec(v___x_2419_);
v_a_2553_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2525_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2525_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
v___jp_2561_:
{
lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = l_Lean_trace_profiler;
v___x_2564_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2437_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref(v___f_2443_);
v___x_2565_ = l_Lean_Meta_mkDefault(v_a_2438_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc_n(v_a_2566_, 2);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg(v___x_2419_, v_a_2566_, v___y_2423_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_dec_ref_known(v___x_2567_, 1);
if (v_hasTrace_2440_ == 0)
{
lean_dec(v_a_2566_);
goto v___jp_2427_;
}
else
{
lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2568_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2569_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2439_, v_options_2437_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_dec(v_a_2566_);
goto v___jp_2427_;
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2570_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2571_ = lean_unsigned_to_nat(30u);
v___x_2572_ = l_Lean_inlineExprTrailing(v_a_2566_, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2570_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2441_, v___x_2573_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2574_;
}
}
}
else
{
lean_dec(v_a_2566_);
return v___x_2567_;
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec(v___x_2419_);
v_a_2575_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2565_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2565_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
v___y_2524_ = v_a_2562_;
goto v___jp_2523_;
}
}
}
else
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Meta_mkDefault(v_a_2438_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc_n(v_a_2586_, 2);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg(v___x_2419_, v_a_2586_, v___y_2423_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2603_; 
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v___x_2587_, 0);
lean_dec(v_unused_2604_);
v___x_2589_ = v___x_2587_;
v_isShared_2590_ = v_isSharedCheck_2603_;
goto v_resetjp_2588_;
}
else
{
lean_dec(v___x_2587_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2603_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
if (v_hasTrace_2440_ == 0)
{
lean_dec(v_a_2586_);
goto v___jp_2591_;
}
else
{
lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2439_, v_options_2437_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_dec(v_a_2586_);
goto v___jp_2591_;
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_del_object(v___x_2589_);
v___x_2598_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2599_ = lean_unsigned_to_nat(30u);
v___x_2600_ = l_Lean_inlineExprTrailing(v_a_2586_, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2598_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2441_, v___x_2601_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2602_;
}
}
v___jp_2591_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = lean_box(0);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2592_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_dec(v_a_2586_);
return v___x_2587_;
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v___x_2419_);
v_a_2605_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2585_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2585_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v___x_2419_);
v_a_2613_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2436_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2436_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_dec(v___x_2419_);
v___x_2621_ = lean_box(0);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2621_);
v___x_2623_ = v___x_2433_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v___x_2419_);
v_a_2626_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2430_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2430_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
v___jp_2427_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_box(0);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object* v___x_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object* v_as_2643_, size_t v_i_2644_, size_t v_stop_2645_, lean_object* v_b_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v___x_2654_; 
v___x_2654_ = lean_usize_dec_eq(v_i_2644_, v_stop_2645_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; lean_object* v___f_2656_; lean_object* v___x_2657_; 
v___x_2655_ = lean_array_uget_borrowed(v_as_2643_, v_i_2644_);
lean_inc_n(v___x_2655_, 2);
v___f_2656_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed), 8, 1);
lean_closure_set(v___f_2656_, 0, v___x_2655_);
v___x_2657_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v___x_2655_, v___f_2656_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; size_t v___x_2659_; size_t v___x_2660_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = ((size_t)1ULL);
v___x_2660_ = lean_usize_add(v_i_2644_, v___x_2659_);
v_i_2644_ = v___x_2660_;
v_b_2646_ = v_a_2658_;
goto _start;
}
else
{
return v___x_2657_;
}
}
else
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_b_2646_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object* v_as_2663_, lean_object* v_i_2664_, lean_object* v_stop_2665_, lean_object* v_b_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
size_t v_i_boxed_2674_; size_t v_stop_boxed_2675_; lean_object* v_res_2676_; 
v_i_boxed_2674_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_stop_boxed_2675_ = lean_unbox_usize(v_stop_2665_);
lean_dec(v_stop_2665_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2663_, v_i_boxed_2674_, v_stop_boxed_2675_, v_b_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec_ref(v_as_2663_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object* v_e_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_Meta_getMVarsNoDelayed(v_e_2677_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2707_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2707_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2707_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2690_ = lean_unsigned_to_nat(0u);
v___x_2691_ = lean_array_get_size(v_a_2686_);
v___x_2692_ = lean_box(0);
v___x_2693_ = lean_nat_dec_lt(v___x_2690_, v___x_2691_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2695_; 
lean_dec(v_a_2686_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2692_);
v___x_2695_ = v___x_2688_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2692_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
else
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_nat_dec_le(v___x_2691_, v___x_2691_);
if (v___x_2697_ == 0)
{
if (v___x_2693_ == 0)
{
lean_object* v___x_2699_; 
lean_dec(v_a_2686_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2692_);
v___x_2699_ = v___x_2688_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2692_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
else
{
size_t v___x_2701_; size_t v___x_2702_; lean_object* v___x_2703_; 
lean_del_object(v___x_2688_);
v___x_2701_ = ((size_t)0ULL);
v___x_2702_ = lean_usize_of_nat(v___x_2691_);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2686_, v___x_2701_, v___x_2702_, v___x_2692_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2686_);
return v___x_2703_;
}
}
else
{
size_t v___x_2704_; size_t v___x_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2688_);
v___x_2704_ = ((size_t)0ULL);
v___x_2705_ = lean_usize_of_nat(v___x_2691_);
v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2686_, v___x_2704_, v___x_2705_, v___x_2692_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2686_);
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_a_2708_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2685_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2685_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object* v_e_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object* v_mvarId_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2725_, v___y_2729_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object* v_mvarId_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v_mvarId_2734_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4(lean_object* v_00_u03b1_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg(v_x_2744_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2753_, lean_object* v_x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4(v_00_u03b1_2753_, v_x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object* v_mvarId_2763_, lean_object* v_val_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___redArg(v_mvarId_2763_, v_val_2764_, v___y_2768_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object* v_mvarId_2773_, lean_object* v_val_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v_mvarId_2773_, v_val_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
return v_res_2782_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object* v_00_u03b2_2783_, lean_object* v_x_2784_, lean_object* v_x_2785_){
_start:
{
uint8_t v___x_2786_; 
v___x_2786_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2784_, v_x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2787_, lean_object* v_x_2788_, lean_object* v_x_2789_){
_start:
{
uint8_t v_res_2790_; lean_object* v_r_2791_; 
v_res_2790_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(v_00_u03b2_2787_, v_x_2788_, v_x_2789_);
lean_dec(v_x_2789_);
lean_dec_ref(v_x_2788_);
v_r_2791_ = lean_box(v_res_2790_);
return v_r_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3(lean_object* v_oldTraces_2792_, lean_object* v_data_2793_, lean_object* v_ref_2794_, lean_object* v_msg_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___redArg(v_oldTraces_2792_, v_data_2793_, v_ref_2794_, v_msg_2795_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___boxed(lean_object* v_oldTraces_2804_, lean_object* v_data_2805_, lean_object* v_ref_2806_, lean_object* v_msg_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3(v_oldTraces_2804_, v_data_2805_, v_ref_2806_, v_msg_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object* v_00_u03b2_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___redArg(v_x_2817_, v_x_2818_, v_x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2821_, lean_object* v_x_2822_, size_t v_x_2823_, lean_object* v_x_2824_){
_start:
{
uint8_t v___x_2825_; 
v___x_2825_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2822_, v_x_2823_, v_x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_, lean_object* v_x_2829_){
_start:
{
size_t v_x_19792__boxed_2830_; uint8_t v_res_2831_; lean_object* v_r_2832_; 
v_x_19792__boxed_2830_ = lean_unbox_usize(v_x_2828_);
lean_dec(v_x_2828_);
v_res_2831_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(v_00_u03b2_2826_, v_x_2827_, v_x_19792__boxed_2830_, v_x_2829_);
lean_dec(v_x_2829_);
lean_dec_ref(v_x_2827_);
v_r_2832_ = lean_box(v_res_2831_);
return v_r_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_2833_, lean_object* v_x_2834_, size_t v_x_2835_, size_t v_x_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___redArg(v_x_2834_, v_x_2835_, v_x_2836_, v_x_2837_, v_x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2840_, lean_object* v_x_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_){
_start:
{
size_t v_x_19803__boxed_2846_; size_t v_x_19804__boxed_2847_; lean_object* v_res_2848_; 
v_x_19803__boxed_2846_ = lean_unbox_usize(v_x_2842_);
lean_dec(v_x_2842_);
v_x_19804__boxed_2847_ = lean_unbox_usize(v_x_2843_);
lean_dec(v_x_2843_);
v_res_2848_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12(v_00_u03b2_2840_, v_x_2841_, v_x_19803__boxed_2846_, v_x_19804__boxed_2847_, v_x_2844_, v_x_2845_);
return v_res_2848_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_2849_, lean_object* v_keys_2850_, lean_object* v_vals_2851_, lean_object* v_heq_2852_, lean_object* v_i_2853_, lean_object* v_k_2854_){
_start:
{
uint8_t v___x_2855_; 
v___x_2855_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2850_, v_i_2853_, v_k_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_2856_, lean_object* v_keys_2857_, lean_object* v_vals_2858_, lean_object* v_heq_2859_, lean_object* v_i_2860_, lean_object* v_k_2861_){
_start:
{
uint8_t v_res_2862_; lean_object* v_r_2863_; 
v_res_2862_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2856_, v_keys_2857_, v_vals_2858_, v_heq_2859_, v_i_2860_, v_k_2861_);
lean_dec(v_k_2861_);
lean_dec_ref(v_vals_2858_);
lean_dec_ref(v_keys_2857_);
v_r_2863_ = lean_box(v_res_2862_);
return v_r_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15(lean_object* v_00_u03b2_2864_, lean_object* v_n_2865_, lean_object* v_k_2866_, lean_object* v_v_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15___redArg(v_n_2865_, v_k_2866_, v_v_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16(lean_object* v_00_u03b2_2869_, size_t v_depth_2870_, lean_object* v_keys_2871_, lean_object* v_vals_2872_, lean_object* v_heq_2873_, lean_object* v_i_2874_, lean_object* v_entries_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___redArg(v_depth_2870_, v_keys_2871_, v_vals_2872_, v_i_2874_, v_entries_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16___boxed(lean_object* v_00_u03b2_2877_, lean_object* v_depth_2878_, lean_object* v_keys_2879_, lean_object* v_vals_2880_, lean_object* v_heq_2881_, lean_object* v_i_2882_, lean_object* v_entries_2883_){
_start:
{
size_t v_depth_boxed_2884_; lean_object* v_res_2885_; 
v_depth_boxed_2884_ = lean_unbox_usize(v_depth_2878_);
lean_dec(v_depth_2878_);
v_res_2885_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__16(v_00_u03b2_2877_, v_depth_boxed_2884_, v_keys_2879_, v_vals_2880_, v_heq_2881_, v_i_2882_, v_entries_2883_);
lean_dec_ref(v_vals_2880_);
lean_dec_ref(v_keys_2879_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15_spec__16(lean_object* v_00_u03b2_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8_spec__12_spec__15_spec__16___redArg(v_x_2887_, v_x_2888_, v_x_2889_, v_x_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object* v_e_2892_, lean_object* v___y_2893_){
_start:
{
uint8_t v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = l_Lean_Expr_hasMVar(v_e_2892_);
v___x_2896_ = lean_bool_not(v___x_2895_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; lean_object* v_mctx_2898_; lean_object* v___x_2899_; lean_object* v_fst_2900_; lean_object* v_snd_2901_; lean_object* v___x_2902_; lean_object* v_cache_2903_; lean_object* v_zetaDeltaFVarIds_2904_; lean_object* v_postponed_2905_; lean_object* v_diag_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2915_; 
v___x_2897_ = lean_st_ref_get(v___y_2893_);
v_mctx_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc_ref(v_mctx_2898_);
lean_dec(v___x_2897_);
v___x_2899_ = l_Lean_instantiateMVarsCore(v_mctx_2898_, v_e_2892_);
v_fst_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_fst_2900_);
v_snd_2901_ = lean_ctor_get(v___x_2899_, 1);
lean_inc(v_snd_2901_);
lean_dec_ref(v___x_2899_);
v___x_2902_ = lean_st_ref_take(v___y_2893_);
v_cache_2903_ = lean_ctor_get(v___x_2902_, 1);
v_zetaDeltaFVarIds_2904_ = lean_ctor_get(v___x_2902_, 2);
v_postponed_2905_ = lean_ctor_get(v___x_2902_, 3);
v_diag_2906_ = lean_ctor_get(v___x_2902_, 4);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2915_ == 0)
{
lean_object* v_unused_2916_; 
v_unused_2916_ = lean_ctor_get(v___x_2902_, 0);
lean_dec(v_unused_2916_);
v___x_2908_ = v___x_2902_;
v_isShared_2909_ = v_isSharedCheck_2915_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_diag_2906_);
lean_inc(v_postponed_2905_);
lean_inc(v_zetaDeltaFVarIds_2904_);
lean_inc(v_cache_2903_);
lean_dec(v___x_2902_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2915_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v_snd_2901_);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_snd_2901_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_cache_2903_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_zetaDeltaFVarIds_2904_);
lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_postponed_2905_);
lean_ctor_set(v_reuseFailAlloc_2914_, 4, v_diag_2906_);
v___x_2911_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_st_ref_set(v___y_2893_, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v_fst_2900_);
return v___x_2913_;
}
}
}
else
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_e_2892_);
return v___x_2917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object* v_e_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2918_, v___y_2919_);
lean_dec(v___y_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object* v_e_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2922_, v___y_2926_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object* v_e_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2939_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object* v_msg_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_24931__overap_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_24931__overap_2950_ = lean_panic_fn_borrowed(v___x_2949_, v_msg_2941_);
lean_inc(v___y_2947_);
lean_inc_ref(v___y_2946_);
lean_inc(v___y_2945_);
lean_inc_ref(v___y_2944_);
lean_inc(v___y_2943_);
lean_inc_ref(v___y_2942_);
v___x_2951_ = lean_apply_7(v___x_24931__overap_2950_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, lean_box(0));
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object* v_msg_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(lean_object* v_a_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg___boxed(lean_object* v_a_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(v_a_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object* v_00_u03b1_2979_, lean_object* v_a_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object* v_00_u03b1_2989_, lean_object* v_a_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v_00_u03b1_2989_, v_a_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(lean_object* v_k_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v_b_3002_, lean_object* v_c_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; 
lean_inc(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
v___x_3009_ = lean_apply_9(v_k_2999_, v_b_3002_, v_c_3003_, v___y_3000_, v___y_3001_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, lean_box(0));
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed(lean_object* v_k_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v_b_3013_, lean_object* v_c_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(v_k_3010_, v___y_3011_, v___y_3012_, v_b_3013_, v_c_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object* v_type_3021_, lean_object* v_k_3022_, uint8_t v_cleanupAnnotations_3023_, uint8_t v_whnfType_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___f_3032_; lean_object* v___x_3033_; 
lean_inc(v___y_3026_);
lean_inc_ref(v___y_3025_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3032_, 0, v_k_3022_);
lean_closure_set(v___f_3032_, 1, v___y_3025_);
lean_closure_set(v___f_3032_, 2, v___y_3026_);
v___x_3033_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_3021_, v___f_3032_, v_cleanupAnnotations_3023_, v_whnfType_3024_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
if (lean_obj_tag(v___x_3033_) == 0)
{
return v___x_3033_;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object* v_type_3042_, lean_object* v_k_3043_, lean_object* v_cleanupAnnotations_3044_, lean_object* v_whnfType_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3053_; uint8_t v_whnfType_boxed_3054_; lean_object* v_res_3055_; 
v_cleanupAnnotations_boxed_3053_ = lean_unbox(v_cleanupAnnotations_3044_);
v_whnfType_boxed_3054_ = lean_unbox(v_whnfType_3045_);
v_res_3055_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3042_, v_k_3043_, v_cleanupAnnotations_boxed_3053_, v_whnfType_boxed_3054_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object* v_00_u03b1_3056_, lean_object* v_type_3057_, lean_object* v_k_3058_, uint8_t v_cleanupAnnotations_3059_, uint8_t v_whnfType_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3057_, v_k_3058_, v_cleanupAnnotations_3059_, v_whnfType_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object* v_00_u03b1_3069_, lean_object* v_type_3070_, lean_object* v_k_3071_, lean_object* v_cleanupAnnotations_3072_, lean_object* v_whnfType_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3081_; uint8_t v_whnfType_boxed_3082_; lean_object* v_res_3083_; 
v_cleanupAnnotations_boxed_3081_ = lean_unbox(v_cleanupAnnotations_3072_);
v_whnfType_boxed_3082_ = lean_unbox(v_whnfType_3073_);
v_res_3083_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(v_00_u03b1_3069_, v_type_3070_, v_k_3071_, v_cleanupAnnotations_boxed_3081_, v_whnfType_boxed_3082_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3083_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0));
v___x_3086_ = l_Lean_stringToMessageData(v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object* v_x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1);
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object* v_x_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec_ref(v_x_3097_);
return v_res_3105_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__0));
v___x_3108_ = l_Lean_stringToMessageData(v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object* v_ctorName_3109_, uint8_t v___x_3110_, lean_object* v_x_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3119_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___closed__1);
v___x_3120_ = l_Lean_MessageData_ofConstName(v_ctorName_3109_, v___x_3110_);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object* v_ctorName_3125_, lean_object* v___x_3126_, lean_object* v_x_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
uint8_t v___x_29576__boxed_3135_; lean_object* v_res_3136_; 
v___x_29576__boxed_3135_ = lean_unbox(v___x_3126_);
v_res_3136_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v_ctorName_3125_, v___x_29576__boxed_3135_, v_x_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec_ref(v_x_3127_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object* v___x_3137_, lean_object* v_fst_3138_, lean_object* v_____r_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = l_Lean_mkAppN(v___x_3137_, v_fst_3138_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object* v___x_3149_, lean_object* v_fst_3150_, lean_object* v_____r_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v___x_3149_, v_fst_3150_, v_____r_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v_fst_3150_);
return v_res_3159_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object* v_e_3160_){
_start:
{
if (lean_obj_tag(v_e_3160_) == 0)
{
uint8_t v___x_3161_; 
v___x_3161_ = 2;
return v___x_3161_;
}
else
{
lean_object* v_a_3162_; uint8_t v___x_3163_; 
v_a_3162_ = lean_ctor_get(v_e_3160_, 0);
v___x_3163_ = l_Lean_Expr_hasSyntheticSorry(v_a_3162_);
if (v___x_3163_ == 0)
{
uint8_t v___x_3164_; 
v___x_3164_ = 0;
return v___x_3164_;
}
else
{
uint8_t v___x_3165_; 
v___x_3165_ = 1;
return v___x_3165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object* v_e_3166_){
_start:
{
uint8_t v_res_3167_; lean_object* v_r_3168_; 
v_res_3167_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_e_3166_);
lean_dec_ref(v_e_3166_);
v_r_3168_ = lean_box(v_res_3167_);
return v_r_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object* v_cls_3169_, uint8_t v_collapsed_3170_, lean_object* v_tag_3171_, lean_object* v_opts_3172_, uint8_t v_clsEnabled_3173_, lean_object* v_oldTraces_3174_, lean_object* v_msg_3175_, lean_object* v_resStartStop_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_fst_3184_; lean_object* v_snd_3185_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v_data_3189_; lean_object* v_fst_3200_; lean_object* v_snd_3201_; lean_object* v___x_3202_; uint8_t v___x_3203_; lean_object* v___y_3205_; lean_object* v_a_3206_; uint8_t v___y_3221_; double v___y_3252_; 
v_fst_3184_ = lean_ctor_get(v_resStartStop_3176_, 0);
lean_inc(v_fst_3184_);
v_snd_3185_ = lean_ctor_get(v_resStartStop_3176_, 1);
lean_inc(v_snd_3185_);
lean_dec_ref(v_resStartStop_3176_);
v_fst_3200_ = lean_ctor_get(v_snd_3185_, 0);
lean_inc(v_fst_3200_);
v_snd_3201_ = lean_ctor_get(v_snd_3185_, 1);
lean_inc(v_snd_3201_);
lean_dec(v_snd_3185_);
v___x_3202_ = l_Lean_trace_profiler;
v___x_3203_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3172_, v___x_3202_);
if (v___x_3203_ == 0)
{
v___y_3221_ = v___x_3203_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3258_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3172_, v___x_3257_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; double v___x_3261_; double v___x_3262_; double v___x_3263_; 
v___x_3259_ = l_Lean_trace_profiler_threshold;
v___x_3260_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6(v_opts_3172_, v___x_3259_);
v___x_3261_ = lean_float_of_nat(v___x_3260_);
v___x_3262_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__2);
v___x_3263_ = lean_float_div(v___x_3261_, v___x_3262_);
v___y_3252_ = v___x_3263_;
goto v___jp_3251_;
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; double v___x_3266_; 
v___x_3264_ = l_Lean_trace_profiler_threshold;
v___x_3265_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__6(v_opts_3172_, v___x_3264_);
v___x_3266_ = lean_float_of_nat(v___x_3265_);
v___y_3252_ = v___x_3266_;
goto v___jp_3251_;
}
}
v___jp_3186_:
{
lean_object* v___x_3190_; 
lean_inc(v___y_3187_);
v___x_3190_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__3___redArg(v_oldTraces_3174_, v_data_3189_, v___y_3187_, v___y_3188_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v___x_3191_; 
lean_dec_ref_known(v___x_3190_, 1);
v___x_3191_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg(v_fst_3184_);
return v___x_3191_;
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec(v_fst_3184_);
v_a_3192_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3190_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3190_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
v___jp_3204_:
{
uint8_t v_result_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; double v___x_3210_; lean_object* v_data_3211_; 
v_result_3207_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_fst_3184_);
v___x_3208_ = lean_box(v_result_3207_);
v___x_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
v___x_3210_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3171_);
lean_inc_ref(v___x_3209_);
lean_inc(v_cls_3169_);
v_data_3211_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3211_, 0, v_cls_3169_);
lean_ctor_set(v_data_3211_, 1, v___x_3209_);
lean_ctor_set(v_data_3211_, 2, v_tag_3171_);
lean_ctor_set_float(v_data_3211_, sizeof(void*)*3, v___x_3210_);
lean_ctor_set_float(v_data_3211_, sizeof(void*)*3 + 8, v___x_3210_);
lean_ctor_set_uint8(v_data_3211_, sizeof(void*)*3 + 16, v_collapsed_3170_);
if (v___x_3203_ == 0)
{
lean_dec_ref_known(v___x_3209_, 1);
lean_dec(v_snd_3201_);
lean_dec(v_fst_3200_);
lean_dec_ref(v_tag_3171_);
lean_dec(v_cls_3169_);
v___y_3187_ = v___y_3205_;
v___y_3188_ = v_a_3206_;
v_data_3189_ = v_data_3211_;
goto v___jp_3186_;
}
else
{
lean_object* v_data_3212_; double v___x_3213_; double v___x_3214_; 
lean_dec_ref_known(v_data_3211_, 3);
v_data_3212_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3212_, 0, v_cls_3169_);
lean_ctor_set(v_data_3212_, 1, v___x_3209_);
lean_ctor_set(v_data_3212_, 2, v_tag_3171_);
v___x_3213_ = lean_unbox_float(v_fst_3200_);
lean_dec(v_fst_3200_);
lean_ctor_set_float(v_data_3212_, sizeof(void*)*3, v___x_3213_);
v___x_3214_ = lean_unbox_float(v_snd_3201_);
lean_dec(v_snd_3201_);
lean_ctor_set_float(v_data_3212_, sizeof(void*)*3 + 8, v___x_3214_);
lean_ctor_set_uint8(v_data_3212_, sizeof(void*)*3 + 16, v_collapsed_3170_);
v___y_3187_ = v___y_3205_;
v___y_3188_ = v_a_3206_;
v_data_3189_ = v_data_3212_;
goto v___jp_3186_;
}
}
v___jp_3215_:
{
lean_object* v_ref_3216_; lean_object* v___x_3217_; 
v_ref_3216_ = lean_ctor_get(v___y_3181_, 5);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v_fst_3184_);
v___x_3217_ = lean_apply_8(v_msg_3175_, v_fst_3184_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, lean_box(0));
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___y_3205_ = v_ref_3216_;
v_a_3206_ = v_a_3218_;
goto v___jp_3204_;
}
else
{
lean_object* v___x_3219_; 
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___closed__1);
v___y_3205_ = v_ref_3216_;
v_a_3206_ = v___x_3219_;
goto v___jp_3204_;
}
}
v___jp_3220_:
{
if (v_clsEnabled_3173_ == 0)
{
if (v___y_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v_traceState_3223_; lean_object* v_env_3224_; lean_object* v_nextMacroScope_3225_; lean_object* v_ngen_3226_; lean_object* v_auxDeclNGen_3227_; lean_object* v_cache_3228_; lean_object* v_messages_3229_; lean_object* v_infoState_3230_; lean_object* v_snapshotTasks_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v_snd_3201_);
lean_dec(v_fst_3200_);
lean_dec_ref(v_msg_3175_);
lean_dec_ref(v_tag_3171_);
lean_dec(v_cls_3169_);
v___x_3222_ = lean_st_ref_take(v___y_3182_);
v_traceState_3223_ = lean_ctor_get(v___x_3222_, 4);
v_env_3224_ = lean_ctor_get(v___x_3222_, 0);
v_nextMacroScope_3225_ = lean_ctor_get(v___x_3222_, 1);
v_ngen_3226_ = lean_ctor_get(v___x_3222_, 2);
v_auxDeclNGen_3227_ = lean_ctor_get(v___x_3222_, 3);
v_cache_3228_ = lean_ctor_get(v___x_3222_, 5);
v_messages_3229_ = lean_ctor_get(v___x_3222_, 6);
v_infoState_3230_ = lean_ctor_get(v___x_3222_, 7);
v_snapshotTasks_3231_ = lean_ctor_get(v___x_3222_, 8);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3233_ = v___x_3222_;
v_isShared_3234_ = v_isSharedCheck_3250_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_snapshotTasks_3231_);
lean_inc(v_infoState_3230_);
lean_inc(v_messages_3229_);
lean_inc(v_cache_3228_);
lean_inc(v_traceState_3223_);
lean_inc(v_auxDeclNGen_3227_);
lean_inc(v_ngen_3226_);
lean_inc(v_nextMacroScope_3225_);
lean_inc(v_env_3224_);
lean_dec(v___x_3222_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3250_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
uint64_t v_tid_3235_; lean_object* v_traces_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3249_; 
v_tid_3235_ = lean_ctor_get_uint64(v_traceState_3223_, sizeof(void*)*1);
v_traces_3236_ = lean_ctor_get(v_traceState_3223_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_traceState_3223_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3238_ = v_traceState_3223_;
v_isShared_3239_ = v_isSharedCheck_3249_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_traces_3236_);
lean_dec(v_traceState_3223_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3249_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3240_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3174_, v_traces_3236_);
lean_dec_ref(v_traces_3236_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3240_);
v___x_3242_ = v___x_3238_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3240_);
lean_ctor_set_uint64(v_reuseFailAlloc_3248_, sizeof(void*)*1, v_tid_3235_);
v___x_3242_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 4, v___x_3242_);
v___x_3244_ = v___x_3233_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_env_3224_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_nextMacroScope_3225_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_ngen_3226_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_auxDeclNGen_3227_);
lean_ctor_set(v_reuseFailAlloc_3247_, 4, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3247_, 5, v_cache_3228_);
lean_ctor_set(v_reuseFailAlloc_3247_, 6, v_messages_3229_);
lean_ctor_set(v_reuseFailAlloc_3247_, 7, v_infoState_3230_);
lean_ctor_set(v_reuseFailAlloc_3247_, 8, v_snapshotTasks_3231_);
v___x_3244_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_st_ref_set(v___y_3182_, v___x_3244_);
v___x_3246_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2_spec__4___redArg(v_fst_3184_);
return v___x_3246_;
}
}
}
}
}
else
{
goto v___jp_3215_;
}
}
else
{
goto v___jp_3215_;
}
}
v___jp_3251_:
{
double v___x_3253_; double v___x_3254_; double v___x_3255_; uint8_t v___x_3256_; 
v___x_3253_ = lean_unbox_float(v_snd_3201_);
v___x_3254_ = lean_unbox_float(v_fst_3200_);
v___x_3255_ = lean_float_sub(v___x_3253_, v___x_3254_);
v___x_3256_ = lean_float_decLt(v___y_3252_, v___x_3255_);
v___y_3221_ = v___x_3256_;
goto v___jp_3220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object* v_cls_3267_, lean_object* v_collapsed_3268_, lean_object* v_tag_3269_, lean_object* v_opts_3270_, lean_object* v_clsEnabled_3271_, lean_object* v_oldTraces_3272_, lean_object* v_msg_3273_, lean_object* v_resStartStop_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
uint8_t v_collapsed_boxed_3282_; uint8_t v_clsEnabled_boxed_3283_; lean_object* v_res_3284_; 
v_collapsed_boxed_3282_ = lean_unbox(v_collapsed_3268_);
v_clsEnabled_boxed_3283_ = lean_unbox(v_clsEnabled_3271_);
v_res_3284_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v_cls_3267_, v_collapsed_boxed_3282_, v_tag_3269_, v_opts_3270_, v_clsEnabled_boxed_3283_, v_oldTraces_3272_, v_msg_3273_, v_resStartStop_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v_opts_3270_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object* v___x_3285_, lean_object* v_as_3286_, size_t v_i_3287_, size_t v_stop_3288_, lean_object* v_b_3289_){
_start:
{
lean_object* v___y_3291_; uint8_t v___x_3295_; 
v___x_3295_ = lean_usize_dec_eq(v_i_3287_, v_stop_3288_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; uint8_t v___x_3297_; 
v___x_3296_ = lean_array_uget_borrowed(v_as_3286_, v_i_3287_);
v___x_3297_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v___x_3285_, v___x_3296_);
if (v___x_3297_ == 0)
{
v___y_3291_ = v_b_3289_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3298_; 
lean_inc(v___x_3296_);
v___x_3298_ = lean_array_push(v_b_3289_, v___x_3296_);
v___y_3291_ = v___x_3298_;
goto v___jp_3290_;
}
}
else
{
return v_b_3289_;
}
v___jp_3290_:
{
size_t v___x_3292_; size_t v___x_3293_; 
v___x_3292_ = ((size_t)1ULL);
v___x_3293_ = lean_usize_add(v_i_3287_, v___x_3292_);
v_i_3287_ = v___x_3293_;
v_b_3289_ = v___y_3291_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object* v___x_3299_, lean_object* v_as_3300_, lean_object* v_i_3301_, lean_object* v_stop_3302_, lean_object* v_b_3303_){
_start:
{
size_t v_i_boxed_3304_; size_t v_stop_boxed_3305_; lean_object* v_res_3306_; 
v_i_boxed_3304_ = lean_unbox_usize(v_i_3301_);
lean_dec(v_i_3301_);
v_stop_boxed_3305_ = lean_unbox_usize(v_stop_3302_);
lean_dec(v_stop_3302_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v___x_3299_, v_as_3300_, v_i_boxed_3304_, v_stop_boxed_3305_, v_b_3303_);
lean_dec_ref(v_as_3300_);
lean_dec_ref(v___x_3299_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
if (lean_obj_tag(v_a_3307_) == 0)
{
lean_object* v___x_3309_; 
v___x_3309_ = l_List_reverse___redArg(v_a_3308_);
return v___x_3309_;
}
else
{
lean_object* v_head_3310_; lean_object* v_tail_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3320_; 
v_head_3310_ = lean_ctor_get(v_a_3307_, 0);
v_tail_3311_ = lean_ctor_get(v_a_3307_, 1);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_a_3307_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3313_ = v_a_3307_;
v_isShared_3314_ = v_isSharedCheck_3320_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_tail_3311_);
lean_inc(v_head_3310_);
lean_dec(v_a_3307_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3320_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3315_ = l_Lean_MessageData_ofExpr(v_head_3310_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v_a_3308_);
lean_ctor_set(v___x_3313_, 0, v___x_3315_);
v___x_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_a_3308_);
v___x_3317_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
v_a_3307_ = v_tail_3311_;
v_a_3308_ = v___x_3317_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2));
v___x_3325_ = lean_unsigned_to_nat(6u);
v___x_3326_ = lean_unsigned_to_nat(108u);
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1));
v___x_3328_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0));
v___x_3329_ = l_mkPanicMessageWithDecl(v___x_3328_, v___x_3327_, v___x_3326_, v___x_3325_, v___x_3324_);
return v___x_3329_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4));
v___x_3332_ = l_Lean_stringToMessageData(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8));
v___x_3338_ = l_Lean_stringToMessageData(v___x_3337_);
return v___x_3338_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10(void){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3340_ = l_Lean_stringToMessageData(v___x_3339_);
return v___x_3340_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_box(0);
v___x_3342_ = lean_unsigned_to_nat(16u);
v___x_3343_ = lean_mk_array(v___x_3342_, v___x_3341_);
return v___x_3343_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12));
v___x_3346_ = l_Lean_stringToMessageData(v___x_3345_);
return v___x_3346_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14));
v___x_3349_ = l_Lean_stringToMessageData(v___x_3348_);
return v___x_3349_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16));
v___x_3352_ = l_Lean_stringToMessageData(v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3360_, lean_object* v_us_3361_, lean_object* v_xs_3362_, lean_object* v___x_3363_, lean_object* v___x_3364_, lean_object* v_ctorName_3365_, lean_object* v___x_3366_, lean_object* v___f_3367_, lean_object* v_insts_3368_, lean_object* v_localInst2Index_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v_env_3378_; lean_object* v___x_3379_; lean_object* v_type_3380_; lean_object* v___y_3382_; lean_object* v___y_3383_; uint8_t v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; uint8_t v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v_val_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3549_; lean_object* v___y_3560_; uint8_t v___x_3570_; uint8_t v___x_3571_; 
v___x_3377_ = lean_st_ref_get(v___y_3375_);
v_env_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc_ref(v_env_3378_);
lean_dec(v___x_3377_);
lean_inc(v_us_3361_);
lean_inc(v_inductiveTypeName_3360_);
v___x_3379_ = l_Lean_Expr_const___override(v_inductiveTypeName_3360_, v_us_3361_);
v_type_3380_ = l_Lean_mkAppN(v___x_3379_, v_xs_3362_);
v___x_3570_ = l_Lean_isStructure(v_env_3378_, v_inductiveTypeName_3360_);
v___x_3571_ = 1;
if (v___x_3570_ == 0)
{
lean_object* v_options_3572_; lean_object* v_inheritedTraceOptions_3573_; uint8_t v_hasTrace_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
lean_dec_ref(v___f_3367_);
v_options_3572_ = lean_ctor_get(v___y_3374_, 2);
v_inheritedTraceOptions_3573_ = lean_ctor_get(v___y_3374_, 13);
v_hasTrace_3574_ = lean_ctor_get_uint8(v_options_3572_, sizeof(void*)*1);
lean_inc(v_ctorName_3365_);
v___x_3575_ = l_Lean_Expr_const___override(v_ctorName_3365_, v_us_3361_);
v___x_3576_ = l_Lean_mkAppN(v___x_3575_, v___x_3366_);
v___x_3577_ = lean_bool_not(v_hasTrace_3574_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___f_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v_a_3586_; uint8_t v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v_a_3602_; uint8_t v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; uint8_t v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v_a_3622_; lean_object* v___y_3632_; uint8_t v___y_3633_; lean_object* v___y_3634_; lean_object* v_a_3635_; lean_object* v___y_3638_; uint8_t v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; uint8_t v___y_3652_; uint8_t v_a_3736_; 
v___x_3578_ = lean_box(v___x_3570_);
v___f_3579_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3579_, 0, v_ctorName_3365_);
lean_closure_set(v___f_3579_, 1, v___x_3578_);
v___x_3580_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3581_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
if (v_hasTrace_3574_ == 0)
{
v_a_3736_ = v_hasTrace_3574_;
goto v___jp_3735_;
}
else
{
lean_object* v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3573_, v_options_3572_, v___x_3798_);
if (v___x_3799_ == 0)
{
v_a_3736_ = v___x_3799_;
goto v___jp_3735_;
}
else
{
v___y_3652_ = v___x_3799_;
goto v___jp_3651_;
}
}
v___jp_3582_:
{
lean_object* v___x_3587_; double v___x_3588_; double v___x_3589_; double v___x_3590_; double v___x_3591_; double v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3587_ = lean_io_mono_nanos_now();
v___x_3588_ = lean_float_of_nat(v___y_3584_);
v___x_3589_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3590_ = lean_float_div(v___x_3588_, v___x_3589_);
v___x_3591_ = lean_float_of_nat(v___x_3587_);
v___x_3592_ = lean_float_div(v___x_3591_, v___x_3589_);
v___x_3593_ = lean_box_float(v___x_3590_);
v___x_3594_ = lean_box_float(v___x_3592_);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3593_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
v___x_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3596_, 0, v_a_3586_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3580_, v___x_3571_, v___x_3581_, v_options_3572_, v___y_3583_, v___y_3585_, v___f_3579_, v___x_3596_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v___y_3560_ = v___x_3597_;
goto v___jp_3559_;
}
v___jp_3598_:
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v_a_3602_);
v___y_3583_ = v___y_3599_;
v___y_3584_ = v___y_3600_;
v___y_3585_ = v___y_3601_;
v_a_3586_ = v___x_3603_;
goto v___jp_3582_;
}
v___jp_3604_:
{
if (lean_obj_tag(v___y_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
v_a_3609_ = lean_ctor_get(v___y_3608_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___y_3608_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___y_3608_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___y_3608_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 1);
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
v___y_3583_ = v___y_3605_;
v___y_3584_ = v___y_3606_;
v___y_3585_ = v___y_3607_;
v_a_3586_ = v___x_3614_;
goto v___jp_3582_;
}
}
}
else
{
lean_object* v_a_3617_; 
v_a_3617_ = lean_ctor_get(v___y_3608_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___y_3608_, 1);
v___y_3599_ = v___y_3605_;
v___y_3600_ = v___y_3606_;
v___y_3601_ = v___y_3607_;
v_a_3602_ = v_a_3617_;
goto v___jp_3598_;
}
}
v___jp_3618_:
{
lean_object* v___x_3623_; double v___x_3624_; double v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3623_ = lean_io_get_num_heartbeats();
v___x_3624_ = lean_float_of_nat(v___y_3620_);
v___x_3625_ = lean_float_of_nat(v___x_3623_);
v___x_3626_ = lean_box_float(v___x_3624_);
v___x_3627_ = lean_box_float(v___x_3625_);
v___x_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v_a_3622_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3580_, v___x_3571_, v___x_3581_, v_options_3572_, v___y_3619_, v___y_3621_, v___f_3579_, v___x_3629_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v___y_3560_ = v___x_3630_;
goto v___jp_3559_;
}
v___jp_3631_:
{
lean_object* v___x_3636_; 
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v_a_3635_);
v___y_3619_ = v___y_3633_;
v___y_3620_ = v___y_3632_;
v___y_3621_ = v___y_3634_;
v_a_3622_ = v___x_3636_;
goto v___jp_3618_;
}
v___jp_3637_:
{
if (lean_obj_tag(v___y_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
v_a_3642_ = lean_ctor_get(v___y_3641_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___y_3641_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___y_3641_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___y_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set_tag(v___x_3644_, 1);
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
v___y_3619_ = v___y_3639_;
v___y_3620_ = v___y_3638_;
v___y_3621_ = v___y_3640_;
v_a_3622_ = v___x_3647_;
goto v___jp_3618_;
}
}
}
else
{
lean_object* v_a_3650_; 
v_a_3650_ = lean_ctor_get(v___y_3641_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___y_3641_, 1);
v___y_3632_ = v___y_3638_;
v___y_3633_ = v___y_3639_;
v___y_3634_ = v___y_3640_;
v_a_3635_ = v_a_3650_;
goto v___jp_3631_;
}
}
v___jp_3651_:
{
lean_object* v___x_3653_; lean_object* v_a_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3653_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___y_3375_);
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref(v___x_3653_);
v___x_3655_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3656_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3572_, v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = lean_io_mono_nanos_now();
lean_inc(v___y_3375_);
lean_inc_ref(v___y_3374_);
lean_inc(v___y_3373_);
lean_inc_ref(v___y_3372_);
lean_inc_ref(v___x_3576_);
v___x_3658_ = lean_infer_type(v___x_3576_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; lean_object* v___x_3662_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v___x_3660_ = lean_box(0);
v___x_3661_ = 0;
v___x_3662_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3659_, v___x_3660_, v___x_3661_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v_snd_3664_; lean_object* v_fst_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3694_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v_snd_3664_ = lean_ctor_get(v_a_3663_, 1);
v_fst_3665_ = lean_ctor_get(v_a_3663_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_a_3663_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3667_ = v_a_3663_;
v_isShared_3668_ = v_isSharedCheck_3694_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_snd_3664_);
lean_inc(v_fst_3665_);
lean_dec(v_a_3663_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3694_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_snd_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3692_; 
v_snd_3669_ = lean_ctor_get(v_snd_3664_, 1);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_snd_3664_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; 
v_unused_3693_ = lean_ctor_get(v_snd_3664_, 0);
lean_dec(v_unused_3693_);
v___x_3671_ = v_snd_3664_;
v_isShared_3672_ = v_isSharedCheck_3692_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_snd_3669_);
lean_dec(v_snd_3664_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3692_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; 
lean_inc(v_snd_3669_);
lean_inc_ref(v_type_3380_);
v___x_3673_ = l_Lean_Meta_isExprDefEq(v_type_3380_, v_snd_3669_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; uint8_t v___x_3675_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3673_, 1);
v___x_3675_ = lean_unbox(v_a_3674_);
lean_dec(v_a_3674_);
if (v___x_3675_ == 0)
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
lean_dec(v_fst_3665_);
lean_dec_ref(v___x_3576_);
v___x_3676_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3380_);
v___x_3677_ = l_Lean_indentExpr(v_type_3380_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set_tag(v___x_3671_, 7);
lean_ctor_set(v___x_3671_, 1, v___x_3677_);
lean_ctor_set(v___x_3671_, 0, v___x_3676_);
v___x_3679_ = v___x_3671_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3680_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 7);
lean_ctor_set(v___x_3667_, 1, v___x_3680_);
lean_ctor_set(v___x_3667_, 0, v___x_3679_);
v___x_3682_ = v___x_3667_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v_a_3686_; 
v___x_3683_ = l_Lean_indentExpr(v_snd_3669_);
v___x_3684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3684_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref(v___x_3685_);
v___y_3599_ = v___y_3652_;
v___y_3600_ = v___x_3657_;
v___y_3601_ = v_a_3654_;
v_a_3602_ = v_a_3686_;
goto v___jp_3598_;
}
}
}
else
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_del_object(v___x_3671_);
lean_dec(v_snd_3669_);
lean_del_object(v___x_3667_);
v___x_3689_ = lean_box(0);
v___x_3690_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v___x_3576_, v_fst_3665_, v___x_3689_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v_fst_3665_);
v___y_3605_ = v___y_3652_;
v___y_3606_ = v___x_3657_;
v___y_3607_ = v_a_3654_;
v___y_3608_ = v___x_3690_;
goto v___jp_3604_;
}
}
else
{
lean_object* v_a_3691_; 
lean_del_object(v___x_3671_);
lean_dec(v_snd_3669_);
lean_del_object(v___x_3667_);
lean_dec(v_fst_3665_);
lean_dec_ref(v___x_3576_);
v_a_3691_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3673_, 1);
v___y_3599_ = v___y_3652_;
v___y_3600_ = v___x_3657_;
v___y_3601_ = v_a_3654_;
v_a_3602_ = v_a_3691_;
goto v___jp_3598_;
}
}
}
}
else
{
lean_object* v_a_3695_; 
lean_dec_ref(v___x_3576_);
v_a_3695_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3662_, 1);
v___y_3599_ = v___y_3652_;
v___y_3600_ = v___x_3657_;
v___y_3601_ = v_a_3654_;
v_a_3602_ = v_a_3695_;
goto v___jp_3598_;
}
}
else
{
lean_dec_ref(v___x_3576_);
v___y_3605_ = v___y_3652_;
v___y_3606_ = v___x_3657_;
v___y_3607_ = v_a_3654_;
v___y_3608_ = v___x_3658_;
goto v___jp_3604_;
}
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3375_);
lean_inc_ref(v___y_3374_);
lean_inc(v___y_3373_);
lean_inc_ref(v___y_3372_);
lean_inc_ref(v___x_3576_);
v___x_3697_ = lean_infer_type(v___x_3576_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; lean_object* v___x_3701_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref_known(v___x_3697_, 1);
v___x_3699_ = lean_box(0);
v___x_3700_ = 0;
v___x_3701_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3698_, v___x_3699_, v___x_3700_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v_snd_3703_; lean_object* v_fst_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3733_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3701_, 1);
v_snd_3703_ = lean_ctor_get(v_a_3702_, 1);
v_fst_3704_ = lean_ctor_get(v_a_3702_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v_a_3702_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3706_ = v_a_3702_;
v_isShared_3707_ = v_isSharedCheck_3733_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_snd_3703_);
lean_inc(v_fst_3704_);
lean_dec(v_a_3702_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3733_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v_snd_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3731_; 
v_snd_3708_ = lean_ctor_get(v_snd_3703_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_snd_3703_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v_snd_3703_, 0);
lean_dec(v_unused_3732_);
v___x_3710_ = v_snd_3703_;
v_isShared_3711_ = v_isSharedCheck_3731_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_snd_3708_);
lean_dec(v_snd_3703_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3731_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3712_; 
lean_inc(v_snd_3708_);
lean_inc_ref(v_type_3380_);
v___x_3712_ = l_Lean_Meta_isExprDefEq(v_type_3380_, v_snd_3708_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; uint8_t v___x_3714_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v___x_3714_ = lean_unbox(v_a_3713_);
lean_dec(v_a_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec(v_fst_3704_);
lean_dec_ref(v___x_3576_);
v___x_3715_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3380_);
v___x_3716_ = l_Lean_indentExpr(v_type_3380_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set_tag(v___x_3710_, 7);
lean_ctor_set(v___x_3710_, 1, v___x_3716_);
lean_ctor_set(v___x_3710_, 0, v___x_3715_);
v___x_3718_ = v___x_3710_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3719_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 7);
lean_ctor_set(v___x_3706_, 1, v___x_3719_);
lean_ctor_set(v___x_3706_, 0, v___x_3718_);
v___x_3721_ = v___x_3706_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v_a_3725_; 
v___x_3722_ = l_Lean_indentExpr(v_snd_3708_);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3723_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
v___y_3632_ = v___x_3696_;
v___y_3633_ = v___y_3652_;
v___y_3634_ = v_a_3654_;
v_a_3635_ = v_a_3725_;
goto v___jp_3631_;
}
}
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_del_object(v___x_3710_);
lean_dec(v_snd_3708_);
lean_del_object(v___x_3706_);
v___x_3728_ = lean_box(0);
v___x_3729_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v___x_3576_, v_fst_3704_, v___x_3728_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v_fst_3704_);
v___y_3638_ = v___x_3696_;
v___y_3639_ = v___y_3652_;
v___y_3640_ = v_a_3654_;
v___y_3641_ = v___x_3729_;
goto v___jp_3637_;
}
}
else
{
lean_object* v_a_3730_; 
lean_del_object(v___x_3710_);
lean_dec(v_snd_3708_);
lean_del_object(v___x_3706_);
lean_dec(v_fst_3704_);
lean_dec_ref(v___x_3576_);
v_a_3730_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3712_, 1);
v___y_3632_ = v___x_3696_;
v___y_3633_ = v___y_3652_;
v___y_3634_ = v_a_3654_;
v_a_3635_ = v_a_3730_;
goto v___jp_3631_;
}
}
}
}
else
{
lean_object* v_a_3734_; 
lean_dec_ref(v___x_3576_);
v_a_3734_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3701_, 1);
v___y_3632_ = v___x_3696_;
v___y_3633_ = v___y_3652_;
v___y_3634_ = v_a_3654_;
v_a_3635_ = v_a_3734_;
goto v___jp_3631_;
}
}
else
{
lean_dec_ref(v___x_3576_);
v___y_3638_ = v___x_3696_;
v___y_3639_ = v___y_3652_;
v___y_3640_ = v_a_3654_;
v___y_3641_ = v___x_3697_;
goto v___jp_3637_;
}
}
}
v___jp_3735_:
{
lean_object* v___x_3737_; uint8_t v___x_3738_; 
v___x_3737_ = l_Lean_trace_profiler;
v___x_3738_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3572_, v___x_3737_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; 
lean_dec_ref(v___f_3579_);
lean_inc(v___y_3375_);
lean_inc_ref(v___y_3374_);
lean_inc(v___y_3373_);
lean_inc_ref(v___y_3372_);
lean_inc_ref(v___x_3576_);
v___x_3739_ = lean_infer_type(v___x_3576_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3741_; uint8_t v___x_3742_; lean_object* v___x_3743_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
v___x_3741_ = lean_box(0);
v___x_3742_ = 0;
v___x_3743_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3740_, v___x_3741_, v___x_3742_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v_snd_3745_; lean_object* v_fst_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3789_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v_snd_3745_ = lean_ctor_get(v_a_3744_, 1);
v_fst_3746_ = lean_ctor_get(v_a_3744_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_a_3744_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3748_ = v_a_3744_;
v_isShared_3749_ = v_isSharedCheck_3789_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_snd_3745_);
lean_inc(v_fst_3746_);
lean_dec(v_a_3744_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3789_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v_snd_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3787_; 
v_snd_3750_ = lean_ctor_get(v_snd_3745_, 1);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_snd_3745_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; 
v_unused_3788_ = lean_ctor_get(v_snd_3745_, 0);
lean_dec(v_unused_3788_);
v___x_3752_ = v_snd_3745_;
v_isShared_3753_ = v_isSharedCheck_3787_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_snd_3750_);
lean_dec(v_snd_3745_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3787_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; 
lean_inc(v_snd_3750_);
lean_inc_ref(v_type_3380_);
v___x_3754_ = l_Lean_Meta_isExprDefEq(v_type_3380_, v_snd_3750_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; uint8_t v___x_3756_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v___x_3756_ = lean_unbox(v_a_3755_);
lean_dec(v_a_3755_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
lean_dec(v_fst_3746_);
lean_dec_ref(v___x_3576_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v___x_3757_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3758_ = l_Lean_indentExpr(v_type_3380_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set_tag(v___x_3752_, 7);
lean_ctor_set(v___x_3752_, 1, v___x_3758_);
lean_ctor_set(v___x_3752_, 0, v___x_3757_);
v___x_3760_ = v___x_3752_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3761_; lean_object* v___x_3763_; 
v___x_3761_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3749_ == 0)
{
lean_ctor_set_tag(v___x_3748_, 7);
lean_ctor_set(v___x_3748_, 1, v___x_3761_);
lean_ctor_set(v___x_3748_, 0, v___x_3760_);
v___x_3763_ = v___x_3748_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
v___x_3764_ = l_Lean_indentExpr(v_snd_3750_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3765_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_del_object(v___x_3752_);
lean_dec(v_snd_3750_);
lean_del_object(v___x_3748_);
v___x_3777_ = lean_box(0);
v___x_3778_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v___x_3576_, v_fst_3746_, v___x_3777_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v_fst_3746_);
v___y_3560_ = v___x_3778_;
goto v___jp_3559_;
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_del_object(v___x_3752_);
lean_dec(v_snd_3750_);
lean_del_object(v___x_3748_);
lean_dec(v_fst_3746_);
lean_dec_ref(v___x_3576_);
lean_dec_ref(v_type_3380_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v_a_3779_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3754_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3754_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec_ref(v___x_3576_);
lean_dec_ref(v_type_3380_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v_a_3790_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3743_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3743_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
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
lean_dec_ref(v___x_3576_);
v___y_3560_ = v___x_3739_;
goto v___jp_3559_;
}
}
else
{
v___y_3652_ = v_a_3736_;
goto v___jp_3651_;
}
}
}
else
{
lean_object* v___x_3800_; 
lean_dec(v_ctorName_3365_);
lean_inc(v___y_3375_);
lean_inc_ref(v___y_3374_);
lean_inc(v___y_3373_);
lean_inc_ref(v___y_3372_);
lean_inc_ref(v___x_3576_);
v___x_3800_ = lean_infer_type(v___x_3576_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3802_; uint8_t v___x_3803_; lean_object* v___x_3804_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3800_, 1);
v___x_3802_ = lean_box(0);
v___x_3803_ = 0;
v___x_3804_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3801_, v___x_3802_, v___x_3803_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v_snd_3806_; lean_object* v_fst_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3850_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v_snd_3806_ = lean_ctor_get(v_a_3805_, 1);
v_fst_3807_ = lean_ctor_get(v_a_3805_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_a_3805_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3809_ = v_a_3805_;
v_isShared_3810_ = v_isSharedCheck_3850_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_snd_3806_);
lean_inc(v_fst_3807_);
lean_dec(v_a_3805_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3850_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v_snd_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3848_; 
v_snd_3811_ = lean_ctor_get(v_snd_3806_, 1);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_snd_3806_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; 
v_unused_3849_ = lean_ctor_get(v_snd_3806_, 0);
lean_dec(v_unused_3849_);
v___x_3813_ = v_snd_3806_;
v_isShared_3814_ = v_isSharedCheck_3848_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_snd_3811_);
lean_dec(v_snd_3806_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3848_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3815_; 
lean_inc(v_snd_3811_);
lean_inc_ref(v_type_3380_);
v___x_3815_ = l_Lean_Meta_isExprDefEq(v_type_3380_, v_snd_3811_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; uint8_t v___x_3817_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
v___x_3817_ = lean_unbox(v_a_3816_);
lean_dec(v_a_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
lean_dec(v_fst_3807_);
lean_dec_ref(v___x_3576_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v___x_3818_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3819_ = l_Lean_indentExpr(v_type_3380_);
if (v_isShared_3814_ == 0)
{
lean_ctor_set_tag(v___x_3813_, 7);
lean_ctor_set(v___x_3813_, 1, v___x_3819_);
lean_ctor_set(v___x_3813_, 0, v___x_3818_);
v___x_3821_ = v___x_3813_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3822_; lean_object* v___x_3824_; 
v___x_3822_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3810_ == 0)
{
lean_ctor_set_tag(v___x_3809_, 7);
lean_ctor_set(v___x_3809_, 1, v___x_3822_);
lean_ctor_set(v___x_3809_, 0, v___x_3821_);
v___x_3824_ = v___x_3809_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
v___x_3825_ = l_Lean_indentExpr(v_snd_3811_);
v___x_3826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3826_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_del_object(v___x_3813_);
lean_dec(v_snd_3811_);
lean_del_object(v___x_3809_);
v___x_3838_ = lean_box(0);
v___x_3839_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v___x_3576_, v_fst_3807_, v___x_3838_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v_fst_3807_);
v___y_3560_ = v___x_3839_;
goto v___jp_3559_;
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_del_object(v___x_3813_);
lean_dec(v_snd_3811_);
lean_del_object(v___x_3809_);
lean_dec(v_fst_3807_);
lean_dec_ref(v___x_3576_);
lean_dec_ref(v_type_3380_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v_a_3840_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3815_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3815_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec_ref(v___x_3576_);
lean_dec_ref(v_type_3380_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v_a_3851_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3804_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3804_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_dec_ref(v___x_3576_);
v___y_3560_ = v___x_3800_;
goto v___jp_3559_;
}
}
}
else
{
lean_object* v_options_3859_; lean_object* v_ref_3860_; lean_object* v_inheritedTraceOptions_3861_; uint8_t v_hasTrace_3862_; uint8_t v___x_3863_; 
lean_dec(v_ctorName_3365_);
lean_dec(v_us_3361_);
v_options_3859_ = lean_ctor_get(v___y_3374_, 2);
v_ref_3860_ = lean_ctor_get(v___y_3374_, 5);
v_inheritedTraceOptions_3861_ = lean_ctor_get(v___y_3374_, 13);
v_hasTrace_3862_ = lean_ctor_get_uint8(v_options_3859_, sizeof(void*)*1);
v___x_3863_ = lean_bool_not(v_hasTrace_3862_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___y_3867_; lean_object* v___y_3868_; uint8_t v___y_3869_; lean_object* v_a_3870_; lean_object* v___y_3883_; uint8_t v___y_3884_; lean_object* v___y_3885_; lean_object* v_a_3886_; uint8_t v___y_3896_; uint8_t v_a_3960_; 
v___x_3864_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3865_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
if (v_hasTrace_3862_ == 0)
{
v_a_3960_ = v_hasTrace_3862_;
goto v___jp_3959_;
}
else
{
lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3971_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3972_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3861_, v_options_3859_, v___x_3971_);
if (v___x_3972_ == 0)
{
v_a_3960_ = v___x_3972_;
goto v___jp_3959_;
}
else
{
v___y_3896_ = v___x_3972_;
goto v___jp_3895_;
}
}
v___jp_3866_:
{
lean_object* v___x_3871_; double v___x_3872_; double v___x_3873_; double v___x_3874_; double v___x_3875_; double v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3871_ = lean_io_mono_nanos_now();
v___x_3872_ = lean_float_of_nat(v___y_3867_);
v___x_3873_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3874_ = lean_float_div(v___x_3872_, v___x_3873_);
v___x_3875_ = lean_float_of_nat(v___x_3871_);
v___x_3876_ = lean_float_div(v___x_3875_, v___x_3873_);
v___x_3877_ = lean_box_float(v___x_3874_);
v___x_3878_ = lean_box_float(v___x_3876_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3877_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_a_3870_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
v___x_3881_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3864_, v___x_3571_, v___x_3865_, v_options_3859_, v___y_3869_, v___y_3868_, v___f_3367_, v___x_3880_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v___y_3549_ = v___x_3881_;
goto v___jp_3548_;
}
v___jp_3882_:
{
lean_object* v___x_3887_; double v___x_3888_; double v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3887_ = lean_io_get_num_heartbeats();
v___x_3888_ = lean_float_of_nat(v___y_3885_);
v___x_3889_ = lean_float_of_nat(v___x_3887_);
v___x_3890_ = lean_box_float(v___x_3888_);
v___x_3891_ = lean_box_float(v___x_3889_);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v_a_3886_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3864_, v___x_3571_, v___x_3865_, v_options_3859_, v___y_3884_, v___y_3883_, v___f_3367_, v___x_3893_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v___y_3549_ = v___x_3894_;
goto v___jp_3548_;
}
v___jp_3895_:
{
lean_object* v___x_3897_; lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3958_; 
v___x_3897_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___y_3375_);
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3958_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3958_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3903_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3859_, v___x_3902_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3904_ = lean_io_mono_nanos_now();
v___x_3905_ = l_Lean_SourceInfo_fromRef(v_ref_3860_, v___x_3903_);
v___x_3906_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3907_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3905_);
v___x_3908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3905_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = l_Lean_Syntax_node1(v___x_3905_, v___x_3906_, v___x_3908_);
lean_inc_ref(v_type_3380_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set_tag(v___x_3900_, 1);
lean_ctor_set(v___x_3900_, 0, v_type_3380_);
v___x_3911_ = v___x_3900_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_type_3380_);
v___x_3911_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3912_, 0, v___x_3909_);
lean_closure_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3912_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
lean_ctor_set_tag(v___x_3916_, 1);
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
v___y_3867_ = v___x_3904_;
v___y_3868_ = v_a_3898_;
v___y_3869_ = v___y_3896_;
v_a_3870_ = v___x_3919_;
goto v___jp_3866_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
v_a_3922_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3913_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3913_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
lean_ctor_set_tag(v___x_3924_, 0);
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
v___y_3867_ = v___x_3904_;
v___y_3868_ = v_a_3898_;
v___y_3869_ = v___y_3896_;
v_a_3870_ = v___x_3927_;
goto v___jp_3866_;
}
}
}
}
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3931_ = lean_io_get_num_heartbeats();
v___x_3932_ = l_Lean_SourceInfo_fromRef(v_ref_3860_, v___x_3863_);
v___x_3933_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3934_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3932_);
v___x_3935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3932_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = l_Lean_Syntax_node1(v___x_3932_, v___x_3933_, v___x_3935_);
lean_inc_ref(v_type_3380_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set_tag(v___x_3900_, 1);
lean_ctor_set(v___x_3900_, 0, v_type_3380_);
v___x_3938_ = v___x_3900_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_type_3380_);
v___x_3938_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3939_, 0, v___x_3936_);
lean_closure_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3939_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3940_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3940_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
lean_ctor_set_tag(v___x_3943_, 1);
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
v___y_3883_ = v_a_3898_;
v___y_3884_ = v___y_3896_;
v___y_3885_ = v___x_3931_;
v_a_3886_ = v___x_3946_;
goto v___jp_3882_;
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
v_a_3949_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3940_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3940_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
lean_ctor_set_tag(v___x_3951_, 0);
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
v___y_3883_ = v_a_3898_;
v___y_3884_ = v___y_3896_;
v___y_3885_ = v___x_3931_;
v_a_3886_ = v___x_3954_;
goto v___jp_3882_;
}
}
}
}
}
}
}
v___jp_3959_:
{
lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3961_ = l_Lean_trace_profiler;
v___x_3962_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3859_, v___x_3961_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_dec_ref(v___f_3367_);
v___x_3963_ = l_Lean_SourceInfo_fromRef(v_ref_3860_, v___x_3962_);
v___x_3964_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3963_);
v___x_3966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3963_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
v___x_3967_ = l_Lean_Syntax_node1(v___x_3963_, v___x_3964_, v___x_3966_);
lean_inc_ref(v_type_3380_);
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v_type_3380_);
v___x_3969_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3969_, 0, v___x_3967_);
lean_closure_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3969_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v___y_3549_ = v___x_3970_;
goto v___jp_3548_;
}
else
{
v___y_3896_ = v_a_3960_;
goto v___jp_3895_;
}
}
}
else
{
uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_dec_ref(v___f_3367_);
v___x_3973_ = 0;
v___x_3974_ = l_Lean_SourceInfo_fromRef(v_ref_3860_, v___x_3973_);
v___x_3975_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3976_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3974_);
v___x_3977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3974_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = l_Lean_Syntax_node1(v___x_3974_, v___x_3975_, v___x_3977_);
lean_inc_ref(v_type_3380_);
v___x_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3979_, 0, v_type_3380_);
v___x_3980_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3980_, 0, v___x_3978_);
lean_closure_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3980_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v___y_3549_ = v___x_3981_;
goto v___jp_3548_;
}
}
v___jp_3381_:
{
lean_object* v___x_3390_; uint8_t v___x_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = l_Array_append___redArg(v_xs_3362_, v___y_3382_);
lean_dec_ref(v___y_3382_);
v___x_3391_ = 0;
v___x_3392_ = 1;
v___x_3393_ = l_Lean_Meta_mkForallFVars(v___x_3390_, v_type_3380_, v___x_3391_, v___y_3384_, v___y_3384_, v___x_3392_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v___x_3395_ = l_Lean_Meta_mkLambdaFVars(v___x_3390_, v___y_3383_, v___x_3391_, v___y_3384_, v___x_3391_, v___y_3384_, v___x_3392_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec_ref(v___x_3390_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3405_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3398_ = v___x_3395_;
v_isShared_3399_ = v_isSharedCheck_3405_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3395_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3405_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v_a_3396_);
lean_ctor_set(v___x_3400_, 1, v___y_3385_);
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v_a_3394_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3401_);
v___x_3403_ = v___x_3398_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v_a_3394_);
lean_dec(v___y_3385_);
v_a_3406_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3395_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3395_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec_ref(v___x_3390_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3383_);
v_a_3414_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3393_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3393_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
v___jp_3422_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___y_3424_);
lean_ctor_set(v___x_3434_, 1, v___y_3433_);
lean_inc(v___y_3423_);
v___x_3435_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3423_, v___x_3434_, v___y_3427_, v___y_3432_, v___y_3426_, v___y_3428_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_dec_ref_known(v___x_3435_, 1);
v___y_3382_ = v___y_3425_;
v___y_3383_ = v___y_3429_;
v___y_3384_ = v___y_3430_;
v___y_3385_ = v___y_3431_;
v___y_3386_ = v___y_3427_;
v___y_3387_ = v___y_3432_;
v___y_3388_ = v___y_3426_;
v___y_3389_ = v___y_3428_;
goto v___jp_3381_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3429_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_type_3380_);
lean_dec_ref(v_xs_3362_);
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
v___jp_3444_:
{
uint8_t v___x_3456_; 
v___x_3456_ = lean_nat_dec_eq(v___y_3451_, v___y_3455_);
lean_dec(v___y_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_dec(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v___y_3446_);
lean_dec_ref(v_type_3380_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v___x_3457_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3458_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3457_, v___y_3445_, v___y_3454_, v___y_3448_, v___y_3453_, v___y_3447_, v___y_3449_);
return v___x_3458_;
}
else
{
lean_object* v_options_3459_; uint8_t v_hasTrace_3460_; 
v_options_3459_ = lean_ctor_get(v___y_3447_, 2);
v_hasTrace_3460_ = lean_ctor_get_uint8(v_options_3459_, sizeof(void*)*1);
if (v_hasTrace_3460_ == 0)
{
lean_dec(v___y_3451_);
lean_dec(v___x_3363_);
v___y_3382_ = v___y_3446_;
v___y_3383_ = v___y_3450_;
v___y_3384_ = v___x_3456_;
v___y_3385_ = v___y_3452_;
v___y_3386_ = v___y_3448_;
v___y_3387_ = v___y_3453_;
v___y_3388_ = v___y_3447_;
v___y_3389_ = v___y_3449_;
goto v___jp_3381_;
}
else
{
lean_object* v_inheritedTraceOptions_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_inheritedTraceOptions_3461_ = lean_ctor_get(v___y_3447_, 13);
v___x_3462_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3463_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3464_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3461_, v_options_3459_, v___x_3463_);
if (v___x_3464_ == 0)
{
lean_dec(v___y_3451_);
lean_dec(v___x_3363_);
v___y_3382_ = v___y_3446_;
v___y_3383_ = v___y_3450_;
v___y_3384_ = v___x_3456_;
v___y_3385_ = v___y_3452_;
v___y_3386_ = v___y_3448_;
v___y_3387_ = v___y_3453_;
v___y_3388_ = v___y_3447_;
v___y_3389_ = v___y_3449_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3465_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3466_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3450_);
v___x_3467_ = l_Lean_inlineExpr(v___y_3450_, v___x_3466_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3465_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_nat_dec_eq(v___y_3451_, v___x_3363_);
lean_dec(v___x_3363_);
lean_dec(v___y_3451_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3470_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3446_);
v___x_3471_ = lean_array_to_list(v___y_3446_);
v___x_3472_ = lean_box(0);
v___x_3473_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3471_, v___x_3472_);
v___x_3474_ = l_Lean_MessageData_ofList(v___x_3473_);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3470_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___y_3423_ = v___x_3462_;
v___y_3424_ = v___x_3468_;
v___y_3425_ = v___y_3446_;
v___y_3426_ = v___y_3447_;
v___y_3427_ = v___y_3448_;
v___y_3428_ = v___y_3449_;
v___y_3429_ = v___y_3450_;
v___y_3430_ = v___x_3456_;
v___y_3431_ = v___y_3452_;
v___y_3432_ = v___y_3453_;
v___y_3433_ = v___x_3477_;
goto v___jp_3422_;
}
else
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3423_ = v___x_3462_;
v___y_3424_ = v___x_3468_;
v___y_3425_ = v___y_3446_;
v___y_3426_ = v___y_3447_;
v___y_3427_ = v___y_3448_;
v___y_3428_ = v___y_3449_;
v___y_3429_ = v___y_3450_;
v___y_3430_ = v___x_3456_;
v___y_3431_ = v___y_3452_;
v___y_3432_ = v___y_3453_;
v___y_3433_ = v___x_3478_;
goto v___jp_3422_;
}
}
}
}
}
v___jp_3479_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = lean_box(1);
lean_inc_ref(v___y_3484_);
v___x_3489_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3488_, v_localInst2Index_3369_, v___y_3484_);
v___x_3490_ = lean_array_get_size(v___y_3487_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_size_3491_; 
v_size_3491_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_size_3491_);
v___y_3445_ = v___y_3480_;
v___y_3446_ = v___y_3487_;
v___y_3447_ = v___y_3481_;
v___y_3448_ = v___y_3482_;
v___y_3449_ = v___y_3483_;
v___y_3450_ = v___y_3484_;
v___y_3451_ = v___x_3490_;
v___y_3452_ = v___x_3489_;
v___y_3453_ = v___y_3485_;
v___y_3454_ = v___y_3486_;
v___y_3455_ = v_size_3491_;
goto v___jp_3444_;
}
else
{
lean_inc(v___x_3363_);
v___y_3445_ = v___y_3480_;
v___y_3446_ = v___y_3487_;
v___y_3447_ = v___y_3481_;
v___y_3448_ = v___y_3482_;
v___y_3449_ = v___y_3483_;
v___y_3450_ = v___y_3484_;
v___y_3451_ = v___x_3490_;
v___y_3452_ = v___x_3489_;
v___y_3453_ = v___y_3485_;
v___y_3454_ = v___y_3486_;
v___y_3455_ = v___x_3363_;
goto v___jp_3444_;
}
}
v___jp_3492_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3500_ = lean_array_get_size(v_insts_3368_);
v___x_3501_ = lean_mk_empty_array_with_capacity(v___x_3363_);
v___x_3502_ = lean_nat_dec_lt(v___x_3363_, v___x_3500_);
if (v___x_3502_ == 0)
{
lean_dec(v___x_3364_);
v___y_3480_ = v___y_3494_;
v___y_3481_ = v___y_3498_;
v___y_3482_ = v___y_3496_;
v___y_3483_ = v___y_3499_;
v___y_3484_ = v___y_3493_;
v___y_3485_ = v___y_3497_;
v___y_3486_ = v___y_3495_;
v___y_3487_ = v___x_3501_;
goto v___jp_3479_;
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v_visitedExpr_3507_; uint8_t v___x_3508_; 
v___x_3503_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11);
lean_inc(v___x_3363_);
v___x_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3363_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
lean_inc_ref(v___x_3501_);
v___x_3505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v___x_3364_);
lean_ctor_set(v___x_3505_, 2, v___x_3501_);
lean_inc_ref(v___y_3493_);
v___x_3506_ = l_Lean_collectFVars(v___x_3505_, v___y_3493_);
v_visitedExpr_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc_ref(v_visitedExpr_3507_);
lean_dec_ref(v___x_3506_);
v___x_3508_ = lean_nat_dec_le(v___x_3500_, v___x_3500_);
if (v___x_3508_ == 0)
{
if (v___x_3502_ == 0)
{
lean_dec_ref(v_visitedExpr_3507_);
v___y_3480_ = v___y_3494_;
v___y_3481_ = v___y_3498_;
v___y_3482_ = v___y_3496_;
v___y_3483_ = v___y_3499_;
v___y_3484_ = v___y_3493_;
v___y_3485_ = v___y_3497_;
v___y_3486_ = v___y_3495_;
v___y_3487_ = v___x_3501_;
goto v___jp_3479_;
}
else
{
size_t v___x_3509_; size_t v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = ((size_t)0ULL);
v___x_3510_ = lean_usize_of_nat(v___x_3500_);
v___x_3511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3507_, v_insts_3368_, v___x_3509_, v___x_3510_, v___x_3501_);
lean_dec_ref(v_visitedExpr_3507_);
v___y_3480_ = v___y_3494_;
v___y_3481_ = v___y_3498_;
v___y_3482_ = v___y_3496_;
v___y_3483_ = v___y_3499_;
v___y_3484_ = v___y_3493_;
v___y_3485_ = v___y_3497_;
v___y_3486_ = v___y_3495_;
v___y_3487_ = v___x_3511_;
goto v___jp_3479_;
}
}
else
{
size_t v___x_3512_; size_t v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = ((size_t)0ULL);
v___x_3513_ = lean_usize_of_nat(v___x_3500_);
v___x_3514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3507_, v_insts_3368_, v___x_3512_, v___x_3513_, v___x_3501_);
lean_dec_ref(v_visitedExpr_3507_);
v___y_3480_ = v___y_3494_;
v___y_3481_ = v___y_3498_;
v___y_3482_ = v___y_3496_;
v___y_3483_ = v___y_3499_;
v___y_3484_ = v___y_3493_;
v___y_3485_ = v___y_3497_;
v___y_3486_ = v___y_3495_;
v___y_3487_ = v___x_3514_;
goto v___jp_3479_;
}
}
}
v___jp_3515_:
{
lean_object* v___x_3523_; 
lean_inc_ref(v_val_3516_);
v___x_3523_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3524_; lean_object* v_a_3525_; uint8_t v___x_3526_; 
lean_dec_ref_known(v___x_3523_, 1);
v___x_3524_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3516_, v___y_3520_);
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = l_Lean_Expr_hasMVar(v_a_3525_);
if (v___x_3526_ == 0)
{
v___y_3493_ = v_a_3525_;
v___y_3494_ = v___y_3517_;
v___y_3495_ = v___y_3518_;
v___y_3496_ = v___y_3519_;
v___y_3497_ = v___y_3520_;
v___y_3498_ = v___y_3521_;
v___y_3499_ = v___y_3522_;
goto v___jp_3492_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec_ref(v_type_3380_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v___x_3527_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13);
v___x_3528_ = lean_unsigned_to_nat(30u);
v___x_3529_ = l_Lean_inlineExprTrailing(v_a_3525_, v___x_3528_);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3527_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3530_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3531_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref(v_val_3516_);
lean_dec_ref(v_type_3380_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v_a_3540_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3523_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3523_);
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
if (lean_obj_tag(v___y_3549_) == 0)
{
lean_object* v_a_3550_; 
v_a_3550_ = lean_ctor_get(v___y_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___y_3549_, 1);
v_val_3516_ = v_a_3550_;
v___y_3517_ = v___y_3370_;
v___y_3518_ = v___y_3371_;
v___y_3519_ = v___y_3372_;
v___y_3520_ = v___y_3373_;
v___y_3521_ = v___y_3374_;
v___y_3522_ = v___y_3375_;
goto v___jp_3515_;
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v_type_3380_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v_a_3551_ = lean_ctor_get(v___y_3549_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___y_3549_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___y_3549_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___y_3549_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
v___jp_3559_:
{
if (lean_obj_tag(v___y_3560_) == 0)
{
lean_object* v_a_3561_; 
v_a_3561_ = lean_ctor_get(v___y_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___y_3560_, 1);
v_val_3516_ = v_a_3561_;
v___y_3517_ = v___y_3370_;
v___y_3518_ = v___y_3371_;
v___y_3519_ = v___y_3372_;
v___y_3520_ = v___y_3373_;
v___y_3521_ = v___y_3374_;
v___y_3522_ = v___y_3375_;
goto v___jp_3515_;
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec_ref(v_type_3380_);
lean_dec(v_localInst2Index_3369_);
lean_dec(v___x_3364_);
lean_dec(v___x_3363_);
lean_dec_ref(v_xs_3362_);
v_a_3562_ = lean_ctor_get(v___y_3560_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___y_3560_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___y_3560_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___y_3560_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object** _args){
lean_object* v_inductiveTypeName_3982_ = _args[0];
lean_object* v_us_3983_ = _args[1];
lean_object* v_xs_3984_ = _args[2];
lean_object* v___x_3985_ = _args[3];
lean_object* v___x_3986_ = _args[4];
lean_object* v_ctorName_3987_ = _args[5];
lean_object* v___x_3988_ = _args[6];
lean_object* v___f_3989_ = _args[7];
lean_object* v_insts_3990_ = _args[8];
lean_object* v_localInst2Index_3991_ = _args[9];
lean_object* v___y_3992_ = _args[10];
lean_object* v___y_3993_ = _args[11];
lean_object* v___y_3994_ = _args[12];
lean_object* v___y_3995_ = _args[13];
lean_object* v___y_3996_ = _args[14];
lean_object* v___y_3997_ = _args[15];
lean_object* v___y_3998_ = _args[16];
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_3982_, v_us_3983_, v_xs_3984_, v___x_3985_, v___x_3986_, v_ctorName_3987_, v___x_3988_, v___f_3989_, v_insts_3990_, v_localInst2Index_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec_ref(v_insts_3990_);
lean_dec_ref(v___x_3988_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t v_sz_4000_, size_t v_i_4001_, lean_object* v_bs_4002_){
_start:
{
uint8_t v___x_4003_; 
v___x_4003_ = lean_usize_dec_lt(v_i_4001_, v_sz_4000_);
if (v___x_4003_ == 0)
{
return v_bs_4002_;
}
else
{
lean_object* v_v_4004_; lean_object* v___x_4005_; lean_object* v_bs_x27_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; size_t v___x_4011_; size_t v___x_4012_; lean_object* v___x_4013_; 
v_v_4004_ = lean_array_uget(v_bs_4002_, v_i_4001_);
v___x_4005_ = lean_unsigned_to_nat(0u);
v_bs_x27_4006_ = lean_array_uset(v_bs_4002_, v_i_4001_, v___x_4005_);
v___x_4007_ = l_Lean_Expr_fvarId_x21(v_v_4004_);
lean_dec(v_v_4004_);
v___x_4008_ = 1;
v___x_4009_ = lean_box(v___x_4008_);
v___x_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4007_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
v___x_4011_ = ((size_t)1ULL);
v___x_4012_ = lean_usize_add(v_i_4001_, v___x_4011_);
v___x_4013_ = lean_array_uset(v_bs_x27_4006_, v_i_4001_, v___x_4010_);
v_i_4001_ = v___x_4012_;
v_bs_4002_ = v___x_4013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object* v_sz_4015_, lean_object* v_i_4016_, lean_object* v_bs_4017_){
_start:
{
size_t v_sz_boxed_4018_; size_t v_i_boxed_4019_; lean_object* v_res_4020_; 
v_sz_boxed_4018_ = lean_unbox_usize(v_sz_4015_);
lean_dec(v_sz_4015_);
v_i_boxed_4019_ = lean_unbox_usize(v_i_4016_);
lean_dec(v_i_4016_);
v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_boxed_4018_, v_i_boxed_4019_, v_bs_4017_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object* v_k_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
lean_inc(v___y_4023_);
lean_inc_ref(v___y_4022_);
v___x_4029_ = lean_apply_7(v_k_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, lean_box(0));
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object* v_bs_4039_, lean_object* v_k_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___f_4048_; lean_object* v___x_4049_; 
lean_inc(v___y_4042_);
lean_inc_ref(v___y_4041_);
v___f_4048_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4048_, 0, v_k_4040_);
lean_closure_set(v___f_4048_, 1, v___y_4041_);
lean_closure_set(v___f_4048_, 2, v___y_4042_);
v___x_4049_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_4039_, v___f_4048_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
if (lean_obj_tag(v___x_4049_) == 0)
{
return v___x_4049_;
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object* v_bs_4058_, lean_object* v_k_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4058_, v_k_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec_ref(v_bs_4058_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_bs_4068_, lean_object* v_k_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
size_t v_sz_4077_; size_t v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_sz_4077_ = lean_array_size(v_bs_4068_);
v___x_4078_ = ((size_t)0ULL);
v___x_4079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4077_, v___x_4078_, v_bs_4068_);
v___x_4080_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v___x_4079_, v_k_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
lean_dec_ref(v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_bs_4081_, lean_object* v_k_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4081_, v_k_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4091_, lean_object* v_inductiveTypeName_4092_, lean_object* v_us_4093_, lean_object* v___x_4094_, lean_object* v_ctorName_4095_, lean_object* v___f_4096_, uint8_t v_addHypotheses_4097_, lean_object* v_xs_4098_, lean_object* v_x_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___f_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4107_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4098_, 2);
v___x_4108_ = l_Array_toSubarray___redArg(v_xs_4098_, v___x_4107_, v_numParams_4091_);
v___x_4109_ = l_Subarray_copy___redArg(v___x_4108_);
lean_inc_ref(v___x_4109_);
v___f_4110_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 17, 8);
lean_closure_set(v___f_4110_, 0, v_inductiveTypeName_4092_);
lean_closure_set(v___f_4110_, 1, v_us_4093_);
lean_closure_set(v___f_4110_, 2, v_xs_4098_);
lean_closure_set(v___f_4110_, 3, v___x_4107_);
lean_closure_set(v___f_4110_, 4, v___x_4094_);
lean_closure_set(v___f_4110_, 5, v_ctorName_4095_);
lean_closure_set(v___f_4110_, 6, v___x_4109_);
lean_closure_set(v___f_4110_, 7, v___f_4096_);
v___x_4111_ = lean_box(v_addHypotheses_4097_);
v___x_4112_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4112_, 0, v___x_4111_);
lean_closure_set(v___x_4112_, 1, lean_box(0));
lean_closure_set(v___x_4112_, 2, v___x_4109_);
lean_closure_set(v___x_4112_, 3, v___f_4110_);
v___x_4113_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_xs_4098_, v___x_4112_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4114_, lean_object* v_inductiveTypeName_4115_, lean_object* v_us_4116_, lean_object* v___x_4117_, lean_object* v_ctorName_4118_, lean_object* v___f_4119_, lean_object* v_addHypotheses_4120_, lean_object* v_xs_4121_, lean_object* v_x_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
uint8_t v_addHypotheses_boxed_4130_; lean_object* v_res_4131_; 
v_addHypotheses_boxed_4130_ = lean_unbox(v_addHypotheses_4120_);
v_res_4131_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4114_, v_inductiveTypeName_4115_, v_us_4116_, v___x_4117_, v_ctorName_4118_, v___f_4119_, v_addHypotheses_boxed_4130_, v_xs_4121_, v_x_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec_ref(v_x_4122_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4132_, lean_object* v_a_4133_){
_start:
{
if (lean_obj_tag(v_a_4132_) == 0)
{
lean_object* v___x_4134_; 
v___x_4134_ = l_List_reverse___redArg(v_a_4133_);
return v___x_4134_;
}
else
{
lean_object* v_head_4135_; lean_object* v_tail_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4145_; 
v_head_4135_ = lean_ctor_get(v_a_4132_, 0);
v_tail_4136_ = lean_ctor_get(v_a_4132_, 1);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_a_4132_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4138_ = v_a_4132_;
v_isShared_4139_ = v_isSharedCheck_4145_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_tail_4136_);
lean_inc(v_head_4135_);
lean_dec(v_a_4132_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4145_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4140_; lean_object* v___x_4142_; 
v___x_4140_ = l_Lean_Level_param___override(v_head_4135_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 1, v_a_4133_);
lean_ctor_set(v___x_4138_, 0, v___x_4140_);
v___x_4142_ = v___x_4138_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4140_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v_a_4133_);
v___x_4142_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
v_a_4132_ = v_tail_4136_;
v_a_4133_ = v___x_4142_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4147_, lean_object* v_ctorName_4148_, uint8_t v_addHypotheses_4149_, lean_object* v_indVal_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v_toConstantVal_4158_; lean_object* v_numParams_4159_; lean_object* v_levelParams_4160_; lean_object* v_type_4161_; lean_object* v___f_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v_us_4165_; lean_object* v___x_4166_; lean_object* v___f_4167_; uint8_t v___x_4168_; lean_object* v___x_4169_; 
v_toConstantVal_4158_ = lean_ctor_get(v_indVal_4150_, 0);
lean_inc_ref(v_toConstantVal_4158_);
v_numParams_4159_ = lean_ctor_get(v_indVal_4150_, 1);
lean_inc(v_numParams_4159_);
lean_dec_ref(v_indVal_4150_);
v_levelParams_4160_ = lean_ctor_get(v_toConstantVal_4158_, 1);
lean_inc(v_levelParams_4160_);
v_type_4161_ = lean_ctor_get(v_toConstantVal_4158_, 2);
lean_inc_ref(v_type_4161_);
lean_dec_ref(v_toConstantVal_4158_);
v___f_4162_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4163_ = lean_box(1);
v___x_4164_ = lean_box(0);
v_us_4165_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4160_, v___x_4164_);
v___x_4166_ = lean_box(v_addHypotheses_4149_);
v___f_4167_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 16, 7);
lean_closure_set(v___f_4167_, 0, v_numParams_4159_);
lean_closure_set(v___f_4167_, 1, v_inductiveTypeName_4147_);
lean_closure_set(v___f_4167_, 2, v_us_4165_);
lean_closure_set(v___f_4167_, 3, v___x_4163_);
lean_closure_set(v___f_4167_, 4, v_ctorName_4148_);
lean_closure_set(v___f_4167_, 5, v___f_4162_);
lean_closure_set(v___f_4167_, 6, v___x_4166_);
v___x_4168_ = 0;
v___x_4169_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_4161_, v___f_4167_, v___x_4168_, v___x_4168_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4170_, lean_object* v_ctorName_4171_, lean_object* v_addHypotheses_4172_, lean_object* v_indVal_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
uint8_t v_addHypotheses_boxed_4181_; lean_object* v_res_4182_; 
v_addHypotheses_boxed_4181_ = lean_unbox(v_addHypotheses_4172_);
v_res_4182_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4170_, v_ctorName_4171_, v_addHypotheses_boxed_4181_, v_indVal_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object* v_00_u03b1_4183_, lean_object* v_bs_4184_, lean_object* v_k_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4184_, v_k_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4194_, lean_object* v_bs_4195_, lean_object* v_k_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(v_00_u03b1_4194_, v_bs_4195_, v_k_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_bs_4195_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_4205_, lean_object* v_bs_4206_, lean_object* v_k_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4206_, v_k_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_4216_, lean_object* v_bs_4217_, lean_object* v_k_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_4216_, v_bs_4217_, v_k_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4227_, lean_object* v_levelParams_4228_, lean_object* v_type_4229_, lean_object* v_value_4230_, lean_object* v_hints_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; uint8_t v___y_4236_; uint8_t v___y_4243_; lean_object* v_env_4246_; uint8_t v___x_4247_; 
v___x_4234_ = lean_st_ref_get(v___y_4232_);
v_env_4246_ = lean_ctor_get(v___x_4234_, 0);
lean_inc_ref_n(v_env_4246_, 2);
lean_dec(v___x_4234_);
v___x_4247_ = l_Lean_Environment_hasUnsafe(v_env_4246_, v_type_4229_);
if (v___x_4247_ == 0)
{
uint8_t v___x_4248_; 
v___x_4248_ = l_Lean_Environment_hasUnsafe(v_env_4246_, v_value_4230_);
v___y_4243_ = v___x_4248_;
goto v___jp_4242_;
}
else
{
lean_dec_ref(v_env_4246_);
v___y_4243_ = v___x_4247_;
goto v___jp_4242_;
}
v___jp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_inc(v_name_4227_);
v___x_4237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4237_, 0, v_name_4227_);
lean_ctor_set(v___x_4237_, 1, v_levelParams_4228_);
lean_ctor_set(v___x_4237_, 2, v_type_4229_);
v___x_4238_ = lean_box(0);
v___x_4239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4239_, 0, v_name_4227_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4240_, 0, v___x_4237_);
lean_ctor_set(v___x_4240_, 1, v_value_4230_);
lean_ctor_set(v___x_4240_, 2, v_hints_4231_);
lean_ctor_set(v___x_4240_, 3, v___x_4239_);
lean_ctor_set_uint8(v___x_4240_, sizeof(void*)*4, v___y_4236_);
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
return v___x_4241_;
}
v___jp_4242_:
{
if (v___y_4243_ == 0)
{
uint8_t v___x_4244_; 
v___x_4244_ = 1;
v___y_4236_ = v___x_4244_;
goto v___jp_4235_;
}
else
{
uint8_t v___x_4245_; 
v___x_4245_ = 0;
v___y_4236_ = v___x_4245_;
goto v___jp_4235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4249_, lean_object* v_levelParams_4250_, lean_object* v_type_4251_, lean_object* v_value_4252_, lean_object* v_hints_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4249_, v_levelParams_4250_, v_type_4251_, v_value_4252_, v_hints_4253_, v___y_4254_);
lean_dec(v___y_4254_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4257_, lean_object* v_levelParams_4258_, lean_object* v_type_4259_, lean_object* v_value_4260_, lean_object* v_hints_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4257_, v_levelParams_4258_, v_type_4259_, v_value_4260_, v_hints_4261_, v___y_4267_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4270_, lean_object* v_levelParams_4271_, lean_object* v_type_4272_, lean_object* v_value_4273_, lean_object* v_hints_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4270_, v_levelParams_4271_, v_type_4272_, v_value_4273_, v_hints_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object* v___y_4283_, uint8_t v_isExporting_4284_, lean_object* v___x_4285_, lean_object* v___y_4286_, lean_object* v___x_4287_, lean_object* v_a_x3f_4288_){
_start:
{
lean_object* v___x_4290_; lean_object* v_env_4291_; lean_object* v_nextMacroScope_4292_; lean_object* v_ngen_4293_; lean_object* v_auxDeclNGen_4294_; lean_object* v_traceState_4295_; lean_object* v_messages_4296_; lean_object* v_infoState_4297_; lean_object* v_snapshotTasks_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4323_; 
v___x_4290_ = lean_st_ref_take(v___y_4283_);
v_env_4291_ = lean_ctor_get(v___x_4290_, 0);
v_nextMacroScope_4292_ = lean_ctor_get(v___x_4290_, 1);
v_ngen_4293_ = lean_ctor_get(v___x_4290_, 2);
v_auxDeclNGen_4294_ = lean_ctor_get(v___x_4290_, 3);
v_traceState_4295_ = lean_ctor_get(v___x_4290_, 4);
v_messages_4296_ = lean_ctor_get(v___x_4290_, 6);
v_infoState_4297_ = lean_ctor_get(v___x_4290_, 7);
v_snapshotTasks_4298_ = lean_ctor_get(v___x_4290_, 8);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; 
v_unused_4324_ = lean_ctor_get(v___x_4290_, 5);
lean_dec(v_unused_4324_);
v___x_4300_ = v___x_4290_;
v_isShared_4301_ = v_isSharedCheck_4323_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_snapshotTasks_4298_);
lean_inc(v_infoState_4297_);
lean_inc(v_messages_4296_);
lean_inc(v_traceState_4295_);
lean_inc(v_auxDeclNGen_4294_);
lean_inc(v_ngen_4293_);
lean_inc(v_nextMacroScope_4292_);
lean_inc(v_env_4291_);
lean_dec(v___x_4290_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4323_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4302_ = l_Lean_Environment_setExporting(v_env_4291_, v_isExporting_4284_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 5, v___x_4285_);
lean_ctor_set(v___x_4300_, 0, v___x_4302_);
v___x_4304_ = v___x_4300_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v_nextMacroScope_4292_);
lean_ctor_set(v_reuseFailAlloc_4322_, 2, v_ngen_4293_);
lean_ctor_set(v_reuseFailAlloc_4322_, 3, v_auxDeclNGen_4294_);
lean_ctor_set(v_reuseFailAlloc_4322_, 4, v_traceState_4295_);
lean_ctor_set(v_reuseFailAlloc_4322_, 5, v___x_4285_);
lean_ctor_set(v_reuseFailAlloc_4322_, 6, v_messages_4296_);
lean_ctor_set(v_reuseFailAlloc_4322_, 7, v_infoState_4297_);
lean_ctor_set(v_reuseFailAlloc_4322_, 8, v_snapshotTasks_4298_);
v___x_4304_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v_mctx_4307_; lean_object* v_zetaDeltaFVarIds_4308_; lean_object* v_postponed_4309_; lean_object* v_diag_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4320_; 
v___x_4305_ = lean_st_ref_set(v___y_4283_, v___x_4304_);
v___x_4306_ = lean_st_ref_take(v___y_4286_);
v_mctx_4307_ = lean_ctor_get(v___x_4306_, 0);
v_zetaDeltaFVarIds_4308_ = lean_ctor_get(v___x_4306_, 2);
v_postponed_4309_ = lean_ctor_get(v___x_4306_, 3);
v_diag_4310_ = lean_ctor_get(v___x_4306_, 4);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4320_ == 0)
{
lean_object* v_unused_4321_; 
v_unused_4321_ = lean_ctor_get(v___x_4306_, 1);
lean_dec(v_unused_4321_);
v___x_4312_ = v___x_4306_;
v_isShared_4313_ = v_isSharedCheck_4320_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_diag_4310_);
lean_inc(v_postponed_4309_);
lean_inc(v_zetaDeltaFVarIds_4308_);
lean_inc(v_mctx_4307_);
lean_dec(v___x_4306_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4320_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
lean_ctor_set(v___x_4312_, 1, v___x_4287_);
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_mctx_4307_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v___x_4287_);
lean_ctor_set(v_reuseFailAlloc_4319_, 2, v_zetaDeltaFVarIds_4308_);
lean_ctor_set(v_reuseFailAlloc_4319_, 3, v_postponed_4309_);
lean_ctor_set(v_reuseFailAlloc_4319_, 4, v_diag_4310_);
v___x_4315_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4316_ = lean_st_ref_set(v___y_4286_, v___x_4315_);
v___x_4317_ = lean_box(0);
v___x_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4317_);
return v___x_4318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object* v___y_4325_, lean_object* v_isExporting_4326_, lean_object* v___x_4327_, lean_object* v___y_4328_, lean_object* v___x_4329_, lean_object* v_a_x3f_4330_, lean_object* v___y_4331_){
_start:
{
uint8_t v_isExporting_boxed_4332_; lean_object* v_res_4333_; 
v_isExporting_boxed_4332_ = lean_unbox(v_isExporting_4326_);
v_res_4333_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4325_, v_isExporting_boxed_4332_, v___x_4327_, v___y_4328_, v___x_4329_, v_a_x3f_4330_);
lean_dec(v_a_x3f_4330_);
lean_dec(v___y_4328_);
lean_dec(v___y_4325_);
return v_res_4333_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4334_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
return v___x_4336_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
return v___x_4338_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4340_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
lean_ctor_set(v___x_4340_, 2, v___x_4339_);
lean_ctor_set(v___x_4340_, 3, v___x_4339_);
lean_ctor_set(v___x_4340_, 4, v___x_4339_);
lean_ctor_set(v___x_4340_, 5, v___x_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object* v_x_4341_, uint8_t v_isExporting_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v___x_4350_; lean_object* v_env_4351_; uint8_t v_isExporting_4352_; uint8_t v___y_4419_; lean_object* v___x_4421_; uint8_t v_isModule_4422_; uint8_t v___x_4423_; 
v___x_4350_ = lean_st_ref_get(v___y_4348_);
v_env_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc_ref(v_env_4351_);
lean_dec(v___x_4350_);
v_isExporting_4352_ = lean_ctor_get_uint8(v_env_4351_, sizeof(void*)*8);
v___x_4421_ = l_Lean_Environment_header(v_env_4351_);
lean_dec_ref(v_env_4351_);
v_isModule_4422_ = lean_ctor_get_uint8(v___x_4421_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4421_);
v___x_4423_ = lean_bool_not(v_isModule_4422_);
if (v___x_4423_ == 0)
{
if (v_isExporting_4352_ == 0)
{
if (v_isExporting_4342_ == 0)
{
lean_object* v___x_4424_; 
lean_inc(v___y_4348_);
lean_inc_ref(v___y_4347_);
lean_inc(v___y_4346_);
lean_inc_ref(v___y_4345_);
lean_inc(v___y_4344_);
lean_inc_ref(v___y_4343_);
v___x_4424_ = lean_apply_7(v_x_4341_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, lean_box(0));
return v___x_4424_;
}
else
{
goto v___jp_4353_;
}
}
else
{
v___y_4419_ = v_isExporting_4342_;
goto v___jp_4418_;
}
}
else
{
v___y_4419_ = v___x_4423_;
goto v___jp_4418_;
}
v___jp_4353_:
{
lean_object* v___x_4354_; lean_object* v_env_4355_; lean_object* v_nextMacroScope_4356_; lean_object* v_ngen_4357_; lean_object* v_auxDeclNGen_4358_; lean_object* v_traceState_4359_; lean_object* v_messages_4360_; lean_object* v_infoState_4361_; lean_object* v_snapshotTasks_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4416_; 
v___x_4354_ = lean_st_ref_take(v___y_4348_);
v_env_4355_ = lean_ctor_get(v___x_4354_, 0);
v_nextMacroScope_4356_ = lean_ctor_get(v___x_4354_, 1);
v_ngen_4357_ = lean_ctor_get(v___x_4354_, 2);
v_auxDeclNGen_4358_ = lean_ctor_get(v___x_4354_, 3);
v_traceState_4359_ = lean_ctor_get(v___x_4354_, 4);
v_messages_4360_ = lean_ctor_get(v___x_4354_, 6);
v_infoState_4361_ = lean_ctor_get(v___x_4354_, 7);
v_snapshotTasks_4362_ = lean_ctor_get(v___x_4354_, 8);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4416_ == 0)
{
lean_object* v_unused_4417_; 
v_unused_4417_ = lean_ctor_get(v___x_4354_, 5);
lean_dec(v_unused_4417_);
v___x_4364_ = v___x_4354_;
v_isShared_4365_ = v_isSharedCheck_4416_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_snapshotTasks_4362_);
lean_inc(v_infoState_4361_);
lean_inc(v_messages_4360_);
lean_inc(v_traceState_4359_);
lean_inc(v_auxDeclNGen_4358_);
lean_inc(v_ngen_4357_);
lean_inc(v_nextMacroScope_4356_);
lean_inc(v_env_4355_);
lean_dec(v___x_4354_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4416_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4369_; 
v___x_4366_ = l_Lean_Environment_setExporting(v_env_4355_, v_isExporting_4342_);
v___x_4367_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 5, v___x_4367_);
lean_ctor_set(v___x_4364_, 0, v___x_4366_);
v___x_4369_ = v___x_4364_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4366_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_nextMacroScope_4356_);
lean_ctor_set(v_reuseFailAlloc_4415_, 2, v_ngen_4357_);
lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_auxDeclNGen_4358_);
lean_ctor_set(v_reuseFailAlloc_4415_, 4, v_traceState_4359_);
lean_ctor_set(v_reuseFailAlloc_4415_, 5, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4415_, 6, v_messages_4360_);
lean_ctor_set(v_reuseFailAlloc_4415_, 7, v_infoState_4361_);
lean_ctor_set(v_reuseFailAlloc_4415_, 8, v_snapshotTasks_4362_);
v___x_4369_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v_mctx_4372_; lean_object* v_zetaDeltaFVarIds_4373_; lean_object* v_postponed_4374_; lean_object* v_diag_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4413_; 
v___x_4370_ = lean_st_ref_set(v___y_4348_, v___x_4369_);
v___x_4371_ = lean_st_ref_take(v___y_4346_);
v_mctx_4372_ = lean_ctor_get(v___x_4371_, 0);
v_zetaDeltaFVarIds_4373_ = lean_ctor_get(v___x_4371_, 2);
v_postponed_4374_ = lean_ctor_get(v___x_4371_, 3);
v_diag_4375_ = lean_ctor_get(v___x_4371_, 4);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4413_ == 0)
{
lean_object* v_unused_4414_; 
v_unused_4414_ = lean_ctor_get(v___x_4371_, 1);
lean_dec(v_unused_4414_);
v___x_4377_ = v___x_4371_;
v_isShared_4378_ = v_isSharedCheck_4413_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_diag_4375_);
lean_inc(v_postponed_4374_);
lean_inc(v_zetaDeltaFVarIds_4373_);
lean_inc(v_mctx_4372_);
lean_dec(v___x_4371_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4413_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4379_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 1, v___x_4379_);
v___x_4381_ = v___x_4377_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_mctx_4372_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v___x_4379_);
lean_ctor_set(v_reuseFailAlloc_4412_, 2, v_zetaDeltaFVarIds_4373_);
lean_ctor_set(v_reuseFailAlloc_4412_, 3, v_postponed_4374_);
lean_ctor_set(v_reuseFailAlloc_4412_, 4, v_diag_4375_);
v___x_4381_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
lean_object* v___x_4382_; lean_object* v_r_4383_; 
v___x_4382_ = lean_st_ref_set(v___y_4346_, v___x_4381_);
lean_inc(v___y_4348_);
lean_inc_ref(v___y_4347_);
lean_inc(v___y_4346_);
lean_inc_ref(v___y_4345_);
lean_inc(v___y_4344_);
lean_inc_ref(v___y_4343_);
v_r_4383_ = lean_apply_7(v_x_4341_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, lean_box(0));
if (lean_obj_tag(v_r_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4400_; 
v_a_4384_ = lean_ctor_get(v_r_4383_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v_r_4383_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4386_ = v_r_4383_;
v_isShared_4387_ = v_isSharedCheck_4400_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v_r_4383_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4400_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
lean_inc(v_a_4384_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set_tag(v___x_4386_, 1);
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
v___x_4390_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4348_, v_isExporting_4352_, v___x_4367_, v___y_4346_, v___x_4379_, v___x_4389_);
lean_dec_ref(v___x_4389_);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; 
v_unused_4398_ = lean_ctor_get(v___x_4390_, 0);
lean_dec(v_unused_4398_);
v___x_4392_ = v___x_4390_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_dec(v___x_4390_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v_a_4384_);
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4384_);
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
else
{
lean_object* v_a_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
v_a_4401_ = lean_ctor_get(v_r_4383_, 0);
lean_inc(v_a_4401_);
lean_dec_ref_known(v_r_4383_, 1);
v___x_4402_ = lean_box(0);
v___x_4403_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4348_, v_isExporting_4352_, v___x_4367_, v___y_4346_, v___x_4379_, v___x_4402_);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4410_ == 0)
{
lean_object* v_unused_4411_; 
v_unused_4411_ = lean_ctor_get(v___x_4403_, 0);
lean_dec(v_unused_4411_);
v___x_4405_ = v___x_4403_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_dec(v___x_4403_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
lean_ctor_set_tag(v___x_4405_, 1);
lean_ctor_set(v___x_4405_, 0, v_a_4401_);
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4401_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
}
}
}
v___jp_4418_:
{
if (v___y_4419_ == 0)
{
goto v___jp_4353_;
}
else
{
lean_object* v___x_4420_; 
lean_inc(v___y_4348_);
lean_inc_ref(v___y_4347_);
lean_inc(v___y_4346_);
lean_inc_ref(v___y_4345_);
lean_inc(v___y_4344_);
lean_inc_ref(v___y_4343_);
v___x_4420_ = lean_apply_7(v_x_4341_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, lean_box(0));
return v___x_4420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v_x_4425_, lean_object* v_isExporting_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
uint8_t v_isExporting_boxed_4434_; lean_object* v_res_4435_; 
v_isExporting_boxed_4434_ = lean_unbox(v_isExporting_4426_);
v_res_4435_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4425_, v_isExporting_boxed_4434_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b1_4436_, lean_object* v_x_4437_, uint8_t v_isExporting_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4437_, v_isExporting_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object* v_00_u03b1_4447_, lean_object* v_x_4448_, lean_object* v_isExporting_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
uint8_t v_isExporting_boxed_4457_; lean_object* v_res_4458_; 
v_isExporting_boxed_4457_ = lean_unbox(v_isExporting_4449_);
v_res_4458_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(v_00_u03b1_4447_, v_x_4448_, v_isExporting_boxed_4457_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
return v_res_4479_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4481_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4482_ = l_Lean_stringToMessageData(v___x_4481_);
return v___x_4482_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4484_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4485_ = l_Lean_stringToMessageData(v___x_4484_);
return v___x_4485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4));
v___x_4488_ = l_Lean_stringToMessageData(v___x_4487_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4489_, lean_object* v___x_4490_, lean_object* v_inductiveTypeName_4491_, uint8_t v___x_4492_, lean_object* v___x_4493_, lean_object* v_ctorName_4494_, uint8_t v_addHypotheses_4495_, lean_object* v___f_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v___y_4505_; lean_object* v___x_4508_; 
lean_inc(v_inductiveTypeName_4491_);
v___x_4508_ = l_Lean_Elab_Deriving_mkContext(v___x_4489_, v___x_4490_, v_inductiveTypeName_4491_, v___x_4492_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
if (lean_obj_tag(v___x_4508_) == 0)
{
lean_object* v_a_4509_; lean_object* v_options_4510_; lean_object* v_currNamespace_4511_; lean_object* v_inheritedTraceOptions_4512_; lean_object* v___x_4513_; 
v_a_4509_ = lean_ctor_get(v___x_4508_, 0);
lean_inc(v_a_4509_);
lean_dec_ref_known(v___x_4508_, 1);
v_options_4510_ = lean_ctor_get(v___y_4501_, 2);
v_currNamespace_4511_ = lean_ctor_get(v___y_4501_, 6);
v_inheritedTraceOptions_4512_ = lean_ctor_get(v___y_4501_, 13);
lean_inc(v_inductiveTypeName_4491_);
v___x_4513_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4491_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v_instName_4515_; lean_object* v_auxFunNames_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; uint8_t v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; uint8_t v___y_4570_; lean_object* v___y_4608_; uint8_t v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v_a_4625_; lean_object* v___y_4696_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc_n(v_a_4514_, 2);
lean_dec_ref_known(v___x_4513_, 1);
v_instName_4515_ = lean_ctor_get(v_a_4509_, 0);
lean_inc(v_instName_4515_);
v_auxFunNames_4516_ = lean_ctor_get(v_a_4509_, 2);
lean_inc_ref(v_auxFunNames_4516_);
lean_dec(v_a_4509_);
v___x_4517_ = lean_unsigned_to_nat(0u);
v___x_4518_ = lean_array_get(v___x_4493_, v_auxFunNames_4516_, v___x_4517_);
lean_dec_ref(v_auxFunNames_4516_);
lean_inc(v_currNamespace_4511_);
v___x_4519_ = l_Lean_Name_append(v_currNamespace_4511_, v___x_4518_);
v___x_4715_ = lean_box(v_addHypotheses_4495_);
lean_inc(v_inductiveTypeName_4491_);
v___x_4716_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4716_, 0, v_inductiveTypeName_4491_);
lean_closure_set(v___x_4716_, 1, v_ctorName_4494_);
lean_closure_set(v___x_4716_, 2, v___x_4715_);
lean_closure_set(v___x_4716_, 3, v_a_4514_);
lean_inc(v___x_4519_);
v___x_4717_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4519_, v___x_4716_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; 
lean_dec_ref(v___f_4496_);
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref_known(v___x_4717_, 1);
v_a_4625_ = v_a_4718_;
goto v___jp_4624_;
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4751_; 
v_a_4719_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4721_ = v___x_4717_;
v_isShared_4722_ = v_isSharedCheck_4751_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4717_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4751_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
uint8_t v___y_4727_; uint8_t v___x_4749_; 
v___x_4749_ = l_Lean_Exception_isInterrupt(v_a_4719_);
if (v___x_4749_ == 0)
{
uint8_t v___x_4750_; 
lean_inc(v_a_4719_);
v___x_4750_ = l_Lean_Exception_isRuntime(v_a_4719_);
v___y_4727_ = v___x_4750_;
goto v___jp_4726_;
}
else
{
v___y_4727_ = v___x_4749_;
goto v___jp_4726_;
}
v___jp_4723_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = lean_box(0);
lean_inc(v___y_4502_);
lean_inc_ref(v___y_4501_);
lean_inc(v___y_4500_);
lean_inc_ref(v___y_4499_);
lean_inc(v___y_4498_);
lean_inc_ref(v___y_4497_);
v___x_4725_ = lean_apply_8(v___f_4496_, v___x_4724_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, lean_box(0));
v___y_4696_ = v___x_4725_;
goto v___jp_4695_;
}
v___jp_4726_:
{
if (v___y_4727_ == 0)
{
uint8_t v_hasTrace_4728_; 
lean_del_object(v___x_4721_);
v_hasTrace_4728_ = lean_ctor_get_uint8(v_options_4510_, sizeof(void*)*1);
if (v_hasTrace_4728_ == 0)
{
lean_dec(v_a_4719_);
goto v___jp_4723_;
}
else
{
lean_object* v___x_4729_; lean_object* v___x_4730_; uint8_t v___x_4731_; 
v___x_4729_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4730_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4512_, v_options_4510_, v___x_4730_);
if (v___x_4731_ == 0)
{
lean_dec(v_a_4719_);
goto v___jp_4723_;
}
else
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4732_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
v___x_4733_ = l_Lean_Exception_toMessageData(v_a_4719_);
v___x_4734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4732_);
lean_ctor_set(v___x_4734_, 1, v___x_4733_);
v___x_4735_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4729_, v___x_4734_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4737_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v___x_4735_, 1);
lean_inc(v___y_4502_);
lean_inc_ref(v___y_4501_);
lean_inc(v___y_4500_);
lean_inc_ref(v___y_4499_);
lean_inc(v___y_4498_);
lean_inc_ref(v___y_4497_);
v___x_4737_ = lean_apply_8(v___f_4496_, v_a_4736_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, lean_box(0));
v___y_4696_ = v___x_4737_;
goto v___jp_4695_;
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec(v___x_4519_);
lean_dec(v_instName_4515_);
lean_dec(v_a_4514_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec_ref(v___f_4496_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4738_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4735_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4735_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
}
else
{
lean_object* v___x_4747_; 
lean_dec(v___x_4519_);
lean_dec(v_instName_4515_);
lean_dec(v_a_4514_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec_ref(v___f_4496_);
lean_dec(v_inductiveTypeName_4491_);
if (v_isShared_4722_ == 0)
{
v___x_4747_ = v___x_4721_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4719_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
v___jp_4520_:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = l_Lean_mkIdent(v_instName_4515_);
v___x_4530_ = l_Lean_mkCIdent(v___x_4519_);
v___x_4531_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4491_, v___x_4529_, v___y_4522_, v___x_4530_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_options_4532_; uint8_t v_hasTrace_4533_; 
v_options_4532_ = lean_ctor_get(v___y_4527_, 2);
v_hasTrace_4533_ = lean_ctor_get_uint8(v_options_4532_, sizeof(void*)*1);
if (v_hasTrace_4533_ == 0)
{
lean_object* v_a_4534_; 
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4521_);
v_a_4534_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4534_);
lean_dec_ref_known(v___x_4531_, 1);
v___y_4505_ = v_a_4534_;
goto v___jp_4504_;
}
else
{
lean_object* v_a_4535_; lean_object* v_inheritedTraceOptions_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v_a_4535_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4531_, 1);
v_inheritedTraceOptions_4536_ = lean_ctor_get(v___y_4527_, 13);
v___x_4537_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4521_);
v___x_4538_ = l_Lean_Name_append(v___x_4537_, v___y_4521_);
v___x_4539_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4536_, v_options_4532_, v___x_4538_);
lean_dec(v___x_4538_);
if (v___x_4539_ == 0)
{
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4521_);
v___y_4505_ = v_a_4535_;
goto v___jp_4504_;
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4540_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4535_);
v___x_4541_ = l_Lean_MessageData_ofSyntax(v_a_4535_);
v___x_4542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4540_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
v___x_4543_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4521_, v___x_4542_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_dec_ref_known(v___x_4543_, 1);
v___y_4505_ = v_a_4535_;
goto v___jp_4504_;
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v_a_4535_);
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4521_);
v_a_4552_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4531_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4531_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
v___jp_4560_:
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Lean_compileDecls(v___y_4564_, v___y_4570_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v___x_4572_; 
lean_dec_ref_known(v___x_4571_, 1);
lean_inc(v___x_4519_);
v___x_4572_ = l_Lean_enableRealizationsForConst(v___x_4519_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_options_4573_; lean_object* v_inheritedTraceOptions_4574_; uint8_t v_hasTrace_4575_; lean_object* v___x_4576_; 
lean_dec_ref_known(v___x_4572_, 1);
v_options_4573_ = lean_ctor_get(v___y_4561_, 2);
v_inheritedTraceOptions_4574_ = lean_ctor_get(v___y_4561_, 13);
v_hasTrace_4575_ = lean_ctor_get_uint8(v_options_4573_, sizeof(void*)*1);
v___x_4576_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4575_ == 0)
{
v___y_4521_ = v___x_4576_;
v___y_4522_ = v___y_4566_;
v___y_4523_ = v___y_4569_;
v___y_4524_ = v___y_4565_;
v___y_4525_ = v___y_4563_;
v___y_4526_ = v___y_4568_;
v___y_4527_ = v___y_4561_;
v___y_4528_ = v___y_4562_;
goto v___jp_4520_;
}
else
{
lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4577_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4578_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4574_, v_options_4573_, v___x_4577_);
if (v___x_4578_ == 0)
{
v___y_4521_ = v___x_4576_;
v___y_4522_ = v___y_4566_;
v___y_4523_ = v___y_4569_;
v___y_4524_ = v___y_4565_;
v___y_4525_ = v___y_4563_;
v___y_4526_ = v___y_4568_;
v___y_4527_ = v___y_4561_;
v___y_4528_ = v___y_4562_;
goto v___jp_4520_;
}
else
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4579_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4519_);
v___x_4580_ = l_Lean_MessageData_ofConstName(v___x_4519_, v___y_4567_);
v___x_4581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4579_);
lean_ctor_set(v___x_4581_, 1, v___x_4580_);
v___x_4582_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4576_, v___x_4581_, v___y_4563_, v___y_4568_, v___y_4561_, v___y_4562_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_dec_ref_known(v___x_4582_, 1);
v___y_4521_ = v___x_4576_;
v___y_4522_ = v___y_4566_;
v___y_4523_ = v___y_4569_;
v___y_4524_ = v___y_4565_;
v___y_4525_ = v___y_4563_;
v___y_4526_ = v___y_4568_;
v___y_4527_ = v___y_4561_;
v___y_4528_ = v___y_4562_;
goto v___jp_4520_;
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___x_4519_);
lean_dec(v_instName_4515_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
}
}
else
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4598_; 
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___x_4519_);
lean_dec(v_instName_4515_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4591_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4593_ = v___x_4572_;
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4572_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
else
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4606_; 
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___x_4519_);
lean_dec(v_instName_4515_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4599_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4601_ = v___x_4571_;
v_isShared_4602_ = v_isSharedCheck_4606_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4571_);
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
v___jp_4607_:
{
lean_object* v___x_4616_; uint8_t v_isNoncomputableSection_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; uint8_t v___x_4621_; 
v___x_4616_ = lean_st_ref_get(v___y_4615_);
v_isNoncomputableSection_4617_ = lean_ctor_get_uint8(v___y_4610_, sizeof(void*)*8 + 4);
v___x_4618_ = lean_unsigned_to_nat(1u);
v___x_4619_ = lean_mk_empty_array_with_capacity(v___x_4618_);
lean_inc(v___x_4519_);
v___x_4620_ = lean_array_push(v___x_4619_, v___x_4519_);
v___x_4621_ = lean_bool_not(v_isNoncomputableSection_4617_);
if (v___x_4621_ == 0)
{
lean_object* v_env_4622_; uint8_t v___x_4623_; 
v_env_4622_ = lean_ctor_get(v___x_4616_, 0);
lean_inc_ref(v_env_4622_);
lean_dec(v___x_4616_);
lean_inc(v___x_4519_);
v___x_4623_ = l_Lean_isMarkedMeta(v_env_4622_, v___x_4519_);
v___y_4561_ = v___y_4614_;
v___y_4562_ = v___y_4615_;
v___y_4563_ = v___y_4612_;
v___y_4564_ = v___x_4620_;
v___y_4565_ = v___y_4611_;
v___y_4566_ = v___y_4608_;
v___y_4567_ = v___y_4609_;
v___y_4568_ = v___y_4613_;
v___y_4569_ = v___y_4610_;
v___y_4570_ = v___x_4623_;
goto v___jp_4560_;
}
else
{
lean_dec(v___x_4616_);
v___y_4561_ = v___y_4614_;
v___y_4562_ = v___y_4615_;
v___y_4563_ = v___y_4612_;
v___y_4564_ = v___x_4620_;
v___y_4565_ = v___y_4611_;
v___y_4566_ = v___y_4608_;
v___y_4567_ = v___y_4609_;
v___y_4568_ = v___y_4613_;
v___y_4569_ = v___y_4610_;
v___y_4570_ = v___x_4492_;
goto v___jp_4560_;
}
}
v___jp_4624_:
{
lean_object* v_snd_4626_; lean_object* v_fst_4627_; lean_object* v_fst_4628_; lean_object* v_snd_4629_; lean_object* v___x_4630_; lean_object* v_toConstantVal_4631_; lean_object* v_env_4632_; lean_object* v_levelParams_4633_; uint32_t v___x_4634_; uint32_t v___x_4635_; uint32_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4694_; 
v_snd_4626_ = lean_ctor_get(v_a_4625_, 1);
lean_inc(v_snd_4626_);
v_fst_4627_ = lean_ctor_get(v_a_4625_, 0);
lean_inc(v_fst_4627_);
lean_dec_ref(v_a_4625_);
v_fst_4628_ = lean_ctor_get(v_snd_4626_, 0);
lean_inc_n(v_fst_4628_, 2);
v_snd_4629_ = lean_ctor_get(v_snd_4626_, 1);
lean_inc(v_snd_4629_);
lean_dec(v_snd_4626_);
v___x_4630_ = lean_st_ref_get(v___y_4502_);
v_toConstantVal_4631_ = lean_ctor_get(v_a_4514_, 0);
lean_inc_ref(v_toConstantVal_4631_);
lean_dec(v_a_4514_);
v_env_4632_ = lean_ctor_get(v___x_4630_, 0);
lean_inc_ref(v_env_4632_);
lean_dec(v___x_4630_);
v_levelParams_4633_ = lean_ctor_get(v_toConstantVal_4631_, 1);
lean_inc(v_levelParams_4633_);
lean_dec_ref(v_toConstantVal_4631_);
v___x_4634_ = l_Lean_getMaxHeight(v_env_4632_, v_fst_4628_);
v___x_4635_ = 1;
v___x_4636_ = lean_uint32_add(v___x_4634_, v___x_4635_);
v___x_4637_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4637_, 0, v___x_4636_);
lean_inc(v___x_4519_);
v___x_4638_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4519_, v_levelParams_4633_, v_fst_4627_, v_fst_4628_, v___x_4637_, v___y_4502_);
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4641_ = v___x_4638_;
v_isShared_4642_ = v_isSharedCheck_4694_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4638_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4694_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
lean_ctor_set_tag(v___x_4641_, 1);
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
uint8_t v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = 0;
v___x_4646_ = l_Lean_addDecl(v___x_4644_, v___x_4645_, v___y_4501_, v___y_4502_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v___x_4647_; lean_object* v_env_4648_; uint8_t v___x_4649_; 
lean_dec_ref_known(v___x_4646_, 1);
v___x_4647_ = lean_st_ref_get(v___y_4502_);
v_env_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc_ref(v_env_4648_);
lean_dec(v___x_4647_);
lean_inc(v_inductiveTypeName_4491_);
v___x_4649_ = l_Lean_isMarkedMeta(v_env_4648_, v_inductiveTypeName_4491_);
if (v___x_4649_ == 0)
{
v___y_4608_ = v_snd_4629_;
v___y_4609_ = v___x_4645_;
v___y_4610_ = v___y_4497_;
v___y_4611_ = v___y_4498_;
v___y_4612_ = v___y_4499_;
v___y_4613_ = v___y_4500_;
v___y_4614_ = v___y_4501_;
v___y_4615_ = v___y_4502_;
goto v___jp_4607_;
}
else
{
lean_object* v___x_4650_; lean_object* v_env_4651_; lean_object* v_nextMacroScope_4652_; lean_object* v_ngen_4653_; lean_object* v_auxDeclNGen_4654_; lean_object* v_traceState_4655_; lean_object* v_messages_4656_; lean_object* v_infoState_4657_; lean_object* v_snapshotTasks_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4683_; 
v___x_4650_ = lean_st_ref_take(v___y_4502_);
v_env_4651_ = lean_ctor_get(v___x_4650_, 0);
v_nextMacroScope_4652_ = lean_ctor_get(v___x_4650_, 1);
v_ngen_4653_ = lean_ctor_get(v___x_4650_, 2);
v_auxDeclNGen_4654_ = lean_ctor_get(v___x_4650_, 3);
v_traceState_4655_ = lean_ctor_get(v___x_4650_, 4);
v_messages_4656_ = lean_ctor_get(v___x_4650_, 6);
v_infoState_4657_ = lean_ctor_get(v___x_4650_, 7);
v_snapshotTasks_4658_ = lean_ctor_get(v___x_4650_, 8);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4683_ == 0)
{
lean_object* v_unused_4684_; 
v_unused_4684_ = lean_ctor_get(v___x_4650_, 5);
lean_dec(v_unused_4684_);
v___x_4660_ = v___x_4650_;
v_isShared_4661_ = v_isSharedCheck_4683_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_snapshotTasks_4658_);
lean_inc(v_infoState_4657_);
lean_inc(v_messages_4656_);
lean_inc(v_traceState_4655_);
lean_inc(v_auxDeclNGen_4654_);
lean_inc(v_ngen_4653_);
lean_inc(v_nextMacroScope_4652_);
lean_inc(v_env_4651_);
lean_dec(v___x_4650_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4683_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
lean_inc(v___x_4519_);
v___x_4662_ = l_Lean_markMeta(v_env_4651_, v___x_4519_);
v___x_4663_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 5, v___x_4663_);
lean_ctor_set(v___x_4660_, 0, v___x_4662_);
v___x_4665_ = v___x_4660_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4662_);
lean_ctor_set(v_reuseFailAlloc_4682_, 1, v_nextMacroScope_4652_);
lean_ctor_set(v_reuseFailAlloc_4682_, 2, v_ngen_4653_);
lean_ctor_set(v_reuseFailAlloc_4682_, 3, v_auxDeclNGen_4654_);
lean_ctor_set(v_reuseFailAlloc_4682_, 4, v_traceState_4655_);
lean_ctor_set(v_reuseFailAlloc_4682_, 5, v___x_4663_);
lean_ctor_set(v_reuseFailAlloc_4682_, 6, v_messages_4656_);
lean_ctor_set(v_reuseFailAlloc_4682_, 7, v_infoState_4657_);
lean_ctor_set(v_reuseFailAlloc_4682_, 8, v_snapshotTasks_4658_);
v___x_4665_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v_mctx_4668_; lean_object* v_zetaDeltaFVarIds_4669_; lean_object* v_postponed_4670_; lean_object* v_diag_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4680_; 
v___x_4666_ = lean_st_ref_set(v___y_4502_, v___x_4665_);
v___x_4667_ = lean_st_ref_take(v___y_4500_);
v_mctx_4668_ = lean_ctor_get(v___x_4667_, 0);
v_zetaDeltaFVarIds_4669_ = lean_ctor_get(v___x_4667_, 2);
v_postponed_4670_ = lean_ctor_get(v___x_4667_, 3);
v_diag_4671_ = lean_ctor_get(v___x_4667_, 4);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4680_ == 0)
{
lean_object* v_unused_4681_; 
v_unused_4681_ = lean_ctor_get(v___x_4667_, 1);
lean_dec(v_unused_4681_);
v___x_4673_ = v___x_4667_;
v_isShared_4674_ = v_isSharedCheck_4680_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_diag_4671_);
lean_inc(v_postponed_4670_);
lean_inc(v_zetaDeltaFVarIds_4669_);
lean_inc(v_mctx_4668_);
lean_dec(v___x_4667_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4680_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4677_; 
v___x_4675_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 1, v___x_4675_);
v___x_4677_ = v___x_4673_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_mctx_4668_);
lean_ctor_set(v_reuseFailAlloc_4679_, 1, v___x_4675_);
lean_ctor_set(v_reuseFailAlloc_4679_, 2, v_zetaDeltaFVarIds_4669_);
lean_ctor_set(v_reuseFailAlloc_4679_, 3, v_postponed_4670_);
lean_ctor_set(v_reuseFailAlloc_4679_, 4, v_diag_4671_);
v___x_4677_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_st_ref_set(v___y_4500_, v___x_4677_);
v___y_4608_ = v_snd_4629_;
v___y_4609_ = v___x_4645_;
v___y_4610_ = v___y_4497_;
v___y_4611_ = v___y_4498_;
v___y_4612_ = v___y_4499_;
v___y_4613_ = v___y_4500_;
v___y_4614_ = v___y_4501_;
v___y_4615_ = v___y_4502_;
goto v___jp_4607_;
}
}
}
}
}
}
else
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4692_; 
lean_dec(v_snd_4629_);
lean_dec(v___x_4519_);
lean_dec(v_instName_4515_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4685_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4687_ = v___x_4646_;
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4646_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
if (v_isShared_4688_ == 0)
{
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4685_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
}
}
v___jp_4695_:
{
if (lean_obj_tag(v___y_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4706_; 
v_a_4697_ = lean_ctor_get(v___y_4696_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___y_4696_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4699_ = v___y_4696_;
v_isShared_4700_ = v_isSharedCheck_4706_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___y_4696_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4706_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
if (lean_obj_tag(v_a_4697_) == 0)
{
lean_object* v_a_4701_; lean_object* v___x_4703_; 
lean_dec(v___x_4519_);
lean_dec(v_instName_4515_);
lean_dec(v_a_4514_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4701_ = lean_ctor_get(v_a_4697_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v_a_4697_, 1);
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 0, v_a_4701_);
v___x_4703_ = v___x_4699_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4701_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
else
{
lean_object* v_a_4705_; 
lean_del_object(v___x_4699_);
v_a_4705_ = lean_ctor_get(v_a_4697_, 0);
lean_inc(v_a_4705_);
lean_dec_ref_known(v_a_4697_, 1);
v_a_4625_ = v_a_4705_;
goto v___jp_4624_;
}
}
}
else
{
lean_object* v_a_4707_; lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4714_; 
lean_dec(v___x_4519_);
lean_dec(v_instName_4515_);
lean_dec(v_a_4514_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4707_ = lean_ctor_get(v___y_4696_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___y_4696_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4709_ = v___y_4696_;
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
else
{
lean_inc(v_a_4707_);
lean_dec(v___y_4696_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_dec(v_a_4509_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec_ref(v___f_4496_);
lean_dec(v_ctorName_4494_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4752_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4513_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4513_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec_ref(v___f_4496_);
lean_dec(v_ctorName_4494_);
lean_dec(v_inductiveTypeName_4491_);
v_a_4760_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4508_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4508_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
v___jp_4504_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___y_4505_);
v___x_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
return v___x_4507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4768_, lean_object* v___x_4769_, lean_object* v_inductiveTypeName_4770_, lean_object* v___x_4771_, lean_object* v___x_4772_, lean_object* v_ctorName_4773_, lean_object* v_addHypotheses_4774_, lean_object* v___f_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
uint8_t v___x_17548__boxed_4783_; uint8_t v_addHypotheses_boxed_4784_; lean_object* v_res_4785_; 
v___x_17548__boxed_4783_ = lean_unbox(v___x_4771_);
v_addHypotheses_boxed_4784_ = lean_unbox(v_addHypotheses_4774_);
v_res_4785_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4768_, v___x_4769_, v_inductiveTypeName_4770_, v___x_17548__boxed_4783_, v___x_4772_, v_ctorName_4773_, v_addHypotheses_boxed_4784_, v___f_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v___x_4772_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4788_, lean_object* v_ctorName_4789_, uint8_t v_addHypotheses_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_){
_start:
{
lean_object* v___f_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___f_4805_; uint8_t v___x_4806_; uint8_t v___x_4807_; lean_object* v___x_4808_; 
v___f_4798_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4799_ = lean_box(0);
v___x_4800_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4801_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4802_ = 1;
v___x_4803_ = lean_box(v___x_4802_);
v___x_4804_ = lean_box(v_addHypotheses_4790_);
lean_inc(v_ctorName_4789_);
v___f_4805_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4805_, 0, v___x_4800_);
lean_closure_set(v___f_4805_, 1, v___x_4801_);
lean_closure_set(v___f_4805_, 2, v_inductiveTypeName_4788_);
lean_closure_set(v___f_4805_, 3, v___x_4803_);
lean_closure_set(v___f_4805_, 4, v___x_4799_);
lean_closure_set(v___f_4805_, 5, v_ctorName_4789_);
lean_closure_set(v___f_4805_, 6, v___x_4804_);
lean_closure_set(v___f_4805_, 7, v___f_4798_);
v___x_4806_ = l_Lean_isPrivateName(v_ctorName_4789_);
lean_dec(v_ctorName_4789_);
v___x_4807_ = lean_bool_not(v___x_4806_);
v___x_4808_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4805_, v___x_4807_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4809_, lean_object* v_ctorName_4810_, lean_object* v_addHypotheses_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_){
_start:
{
uint8_t v_addHypotheses_boxed_4819_; lean_object* v_res_4820_; 
v_addHypotheses_boxed_4819_ = lean_unbox(v_addHypotheses_4811_);
v_res_4820_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4809_, v_ctorName_4810_, v_addHypotheses_boxed_4819_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_);
lean_dec(v_a_4817_);
lean_dec_ref(v_a_4816_);
lean_dec(v_a_4815_);
lean_dec_ref(v_a_4814_);
lean_dec(v_a_4813_);
lean_dec_ref(v_a_4812_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4821_, lean_object* v_ctorName_4822_, uint8_t v_addHypotheses_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4827_ = lean_box(v_addHypotheses_4823_);
v___x_4828_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4828_, 0, v_inductiveTypeName_4821_);
lean_closure_set(v___x_4828_, 1, v_ctorName_4822_);
lean_closure_set(v___x_4828_, 2, v___x_4827_);
v___x_4829_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4828_, v_a_4824_, v_a_4825_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4859_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4832_ = v___x_4829_;
v_isShared_4833_ = v_isSharedCheck_4859_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4829_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4859_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
if (lean_obj_tag(v_a_4830_) == 0)
{
uint8_t v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4837_; 
v___x_4834_ = 0;
v___x_4835_ = lean_box(v___x_4834_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 0, v___x_4835_);
v___x_4837_ = v___x_4832_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v___x_4835_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
else
{
lean_object* v_val_4839_; lean_object* v___x_4840_; 
lean_del_object(v___x_4832_);
v_val_4839_ = lean_ctor_get(v_a_4830_, 0);
lean_inc(v_val_4839_);
lean_dec_ref_known(v_a_4830_, 1);
v___x_4840_ = l_Lean_Elab_Command_elabCommand(v_val_4839_, v_a_4824_, v_a_4825_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4849_; 
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4849_ == 0)
{
lean_object* v_unused_4850_; 
v_unused_4850_ = lean_ctor_get(v___x_4840_, 0);
lean_dec(v_unused_4850_);
v___x_4842_ = v___x_4840_;
v_isShared_4843_ = v_isSharedCheck_4849_;
goto v_resetjp_4841_;
}
else
{
lean_dec(v___x_4840_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4849_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
uint8_t v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4847_; 
v___x_4844_ = 1;
v___x_4845_ = lean_box(v___x_4844_);
if (v_isShared_4843_ == 0)
{
lean_ctor_set(v___x_4842_, 0, v___x_4845_);
v___x_4847_ = v___x_4842_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
else
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4858_; 
v_a_4851_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4853_ = v___x_4840_;
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4840_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4854_ == 0)
{
v___x_4856_ = v___x_4853_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4851_);
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
}
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4867_; 
v_a_4860_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4862_ = v___x_4829_;
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4829_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4868_, lean_object* v_ctorName_4869_, lean_object* v_addHypotheses_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_){
_start:
{
uint8_t v_addHypotheses_boxed_4874_; lean_object* v_res_4875_; 
v_addHypotheses_boxed_4874_ = lean_unbox(v_addHypotheses_4870_);
v_res_4875_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4868_, v_ctorName_4869_, v_addHypotheses_boxed_4874_, v_a_4871_, v_a_4872_);
lean_dec(v_a_4872_);
lean_dec_ref(v_a_4871_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4879_, uint8_t v_addHypotheses_4880_, lean_object* v_as_x27_4881_, lean_object* v_b_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
if (lean_obj_tag(v_as_x27_4881_) == 0)
{
lean_object* v___x_4886_; 
lean_dec(v_declName_4879_);
v___x_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4886_, 0, v_b_4882_);
return v___x_4886_;
}
else
{
lean_object* v_head_4887_; lean_object* v_tail_4888_; lean_object* v___x_4889_; 
lean_dec_ref(v_b_4882_);
v_head_4887_ = lean_ctor_get(v_as_x27_4881_, 0);
v_tail_4888_ = lean_ctor_get(v_as_x27_4881_, 1);
lean_inc(v_head_4887_);
lean_inc(v_declName_4879_);
v___x_4889_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4879_, v_head_4887_, v_addHypotheses_4880_, v___y_4883_, v___y_4884_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4903_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4892_ = v___x_4889_;
v_isShared_4893_ = v_isSharedCheck_4903_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___x_4889_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4903_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4894_; uint8_t v___x_4895_; 
v___x_4894_ = lean_box(0);
v___x_4895_ = lean_unbox(v_a_4890_);
if (v___x_4895_ == 0)
{
lean_object* v___x_4896_; 
lean_del_object(v___x_4892_);
lean_dec(v_a_4890_);
v___x_4896_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v_as_x27_4881_ = v_tail_4888_;
v_b_4882_ = v___x_4896_;
goto _start;
}
else
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4901_; 
lean_dec(v_declName_4879_);
v___x_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4898_, 0, v_a_4890_);
v___x_4899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4898_);
lean_ctor_set(v___x_4899_, 1, v___x_4894_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 0, v___x_4899_);
v___x_4901_ = v___x_4892_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
else
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4911_; 
lean_dec(v_declName_4879_);
v_a_4904_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4911_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4906_ = v___x_4889_;
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4889_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_4912_, lean_object* v_addHypotheses_4913_, lean_object* v_as_x27_4914_, lean_object* v_b_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
uint8_t v_addHypotheses_boxed_4919_; lean_object* v_res_4920_; 
v_addHypotheses_boxed_4919_ = lean_unbox(v_addHypotheses_4913_);
v_res_4920_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4912_, v_addHypotheses_boxed_4919_, v_as_x27_4914_, v_b_4915_, v___y_4916_, v___y_4917_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
lean_dec(v_as_x27_4914_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_4921_, lean_object* v_declName_4922_, uint8_t v_addHypotheses_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v_ctors_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v_ctors_4927_ = lean_ctor_get(v_a_4921_, 4);
v___x_4928_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_4929_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4922_, v_addHypotheses_4923_, v_ctors_4927_, v___x_4928_, v___y_4924_, v___y_4925_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4944_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4932_ = v___x_4929_;
v_isShared_4933_ = v_isSharedCheck_4944_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4929_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4944_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v_fst_4934_; 
v_fst_4934_ = lean_ctor_get(v_a_4930_, 0);
lean_inc(v_fst_4934_);
lean_dec(v_a_4930_);
if (lean_obj_tag(v_fst_4934_) == 0)
{
uint8_t v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4938_; 
v___x_4935_ = 0;
v___x_4936_ = lean_box(v___x_4935_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4936_);
v___x_4938_ = v___x_4932_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4936_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
else
{
lean_object* v_val_4940_; lean_object* v___x_4942_; 
v_val_4940_ = lean_ctor_get(v_fst_4934_, 0);
lean_inc(v_val_4940_);
lean_dec_ref_known(v_fst_4934_, 1);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v_val_4940_);
v___x_4942_ = v___x_4932_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_val_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
else
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4952_; 
v_a_4945_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4947_ = v___x_4929_;
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4929_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4950_; 
if (v_isShared_4948_ == 0)
{
v___x_4950_ = v___x_4947_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4945_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_4953_, lean_object* v_declName_4954_, lean_object* v_addHypotheses_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
uint8_t v_addHypotheses_boxed_4959_; lean_object* v_res_4960_; 
v_addHypotheses_boxed_4959_ = lean_unbox(v_addHypotheses_4955_);
v_res_4960_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_4953_, v_declName_4954_, v_addHypotheses_boxed_4959_, v___y_4956_, v___y_4957_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec_ref(v_a_4953_);
return v_res_4960_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4961_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4962_);
return v___x_4963_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4964_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4965_ = lean_unsigned_to_nat(0u);
v___x_4966_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4965_);
lean_ctor_set(v___x_4966_, 1, v___x_4965_);
lean_ctor_set(v___x_4966_, 2, v___x_4965_);
lean_ctor_set(v___x_4966_, 3, v___x_4965_);
lean_ctor_set(v___x_4966_, 4, v___x_4964_);
lean_ctor_set(v___x_4966_, 5, v___x_4964_);
lean_ctor_set(v___x_4966_, 6, v___x_4964_);
lean_ctor_set(v___x_4966_, 7, v___x_4964_);
lean_ctor_set(v___x_4966_, 8, v___x_4964_);
lean_ctor_set(v___x_4966_, 9, v___x_4964_);
return v___x_4966_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4967_ = lean_unsigned_to_nat(32u);
v___x_4968_ = lean_mk_empty_array_with_capacity(v___x_4967_);
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
return v___x_4969_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4970_ = ((size_t)5ULL);
v___x_4971_ = lean_unsigned_to_nat(0u);
v___x_4972_ = lean_unsigned_to_nat(32u);
v___x_4973_ = lean_mk_empty_array_with_capacity(v___x_4972_);
v___x_4974_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_4975_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4975_, 0, v___x_4974_);
lean_ctor_set(v___x_4975_, 1, v___x_4973_);
lean_ctor_set(v___x_4975_, 2, v___x_4971_);
lean_ctor_set(v___x_4975_, 3, v___x_4971_);
lean_ctor_set_usize(v___x_4975_, 4, v___x_4970_);
return v___x_4975_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4976_ = lean_box(1);
v___x_4977_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_4978_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
lean_ctor_set(v___x_4979_, 1, v___x_4977_);
lean_ctor_set(v___x_4979_, 2, v___x_4976_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v___x_4983_; lean_object* v_env_4984_; lean_object* v___x_4985_; lean_object* v_scopes_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v_opts_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4983_ = lean_st_ref_get(v___y_4981_);
v_env_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc_ref(v_env_4984_);
lean_dec(v___x_4983_);
v___x_4985_ = lean_st_ref_get(v___y_4981_);
v_scopes_4986_ = lean_ctor_get(v___x_4985_, 2);
lean_inc(v_scopes_4986_);
lean_dec(v___x_4985_);
v___x_4987_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4988_ = l_List_head_x21___redArg(v___x_4987_, v_scopes_4986_);
lean_dec(v_scopes_4986_);
v_opts_4989_ = lean_ctor_get(v___x_4988_, 1);
lean_inc_ref(v_opts_4989_);
lean_dec(v___x_4988_);
v___x_4990_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_4991_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5);
v___x_4992_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4992_, 0, v_env_4984_);
lean_ctor_set(v___x_4992_, 1, v___x_4990_);
lean_ctor_set(v___x_4992_, 2, v___x_4991_);
lean_ctor_set(v___x_4992_, 3, v_opts_4989_);
v___x_4993_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
lean_ctor_set(v___x_4993_, 1, v_msgData_4980_);
v___x_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_4995_, v___y_4996_);
lean_dec(v___y_4996_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_4999_, lean_object* v_macroStack_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v___x_5003_; lean_object* v_scopes_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v_opts_5007_; lean_object* v___x_5008_; uint8_t v___x_5009_; uint8_t v___x_5010_; 
v___x_5003_ = lean_st_ref_get(v___y_5001_);
v_scopes_5004_ = lean_ctor_get(v___x_5003_, 2);
lean_inc(v_scopes_5004_);
lean_dec(v___x_5003_);
v___x_5005_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5006_ = l_List_head_x21___redArg(v___x_5005_, v_scopes_5004_);
lean_dec(v_scopes_5004_);
v_opts_5007_ = lean_ctor_get(v___x_5006_, 1);
lean_inc_ref(v_opts_5007_);
lean_dec(v___x_5006_);
v___x_5008_ = l_Lean_Elab_pp_macroStack;
v___x_5009_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_5007_, v___x_5008_);
lean_dec_ref(v_opts_5007_);
v___x_5010_ = lean_bool_not(v___x_5009_);
if (v___x_5010_ == 0)
{
if (lean_obj_tag(v_macroStack_5000_) == 0)
{
lean_object* v___x_5011_; 
v___x_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5011_, 0, v_msgData_4999_);
return v___x_5011_;
}
else
{
lean_object* v_head_5012_; lean_object* v_after_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5028_; 
v_head_5012_ = lean_ctor_get(v_macroStack_5000_, 0);
lean_inc(v_head_5012_);
v_after_5013_ = lean_ctor_get(v_head_5012_, 1);
v_isSharedCheck_5028_ = !lean_is_exclusive(v_head_5012_);
if (v_isSharedCheck_5028_ == 0)
{
lean_object* v_unused_5029_; 
v_unused_5029_ = lean_ctor_get(v_head_5012_, 0);
lean_dec(v_unused_5029_);
v___x_5015_ = v_head_5012_;
v_isShared_5016_ = v_isSharedCheck_5028_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_after_5013_);
lean_dec(v_head_5012_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5028_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5017_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_5016_ == 0)
{
lean_ctor_set_tag(v___x_5015_, 7);
lean_ctor_set(v___x_5015_, 1, v___x_5017_);
lean_ctor_set(v___x_5015_, 0, v_msgData_4999_);
v___x_5019_ = v___x_5015_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_msgData_4999_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v_msgData_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5020_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_5021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5019_);
lean_ctor_set(v___x_5021_, 1, v___x_5020_);
v___x_5022_ = l_Lean_MessageData_ofSyntax(v_after_5013_);
v___x_5023_ = l_Lean_indentD(v___x_5022_);
v_msgData_5024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5024_, 0, v___x_5021_);
lean_ctor_set(v_msgData_5024_, 1, v___x_5023_);
v___x_5025_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_5024_, v_macroStack_5000_);
v___x_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
return v___x_5026_;
}
}
}
}
else
{
lean_object* v___x_5030_; 
lean_dec(v_macroStack_5000_);
v___x_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5030_, 0, v_msgData_4999_);
return v___x_5030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_5031_, lean_object* v_macroStack_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5031_, v_macroStack_5032_, v___y_5033_);
lean_dec(v___y_5033_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_){
_start:
{
lean_object* v___x_5040_; 
v___x_5040_ = l_Lean_Elab_Command_getRef___redArg(v___y_5037_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v_macroStack_5042_; lean_object* v___x_5043_; lean_object* v_a_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5055_; 
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5041_);
lean_dec_ref_known(v___x_5040_, 1);
v_macroStack_5042_ = lean_ctor_get(v___y_5037_, 4);
v___x_5043_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_5036_, v___y_5038_);
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc(v_a_5044_);
lean_dec_ref(v___x_5043_);
v___x_5045_ = l_Lean_Elab_getBetterRef(v_a_5041_, v_macroStack_5042_);
lean_dec(v_a_5041_);
lean_inc(v_macroStack_5042_);
v___x_5046_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_5044_, v_macroStack_5042_, v___y_5038_);
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5049_ = v___x_5046_;
v_isShared_5050_ = v_isSharedCheck_5055_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5046_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5055_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5051_; lean_object* v___x_5053_; 
v___x_5051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5045_);
lean_ctor_set(v___x_5051_, 1, v_a_5047_);
if (v_isShared_5050_ == 0)
{
lean_ctor_set_tag(v___x_5049_, 1);
lean_ctor_set(v___x_5049_, 0, v___x_5051_);
v___x_5053_ = v___x_5049_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5051_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_dec_ref(v_msg_5036_);
v_a_5056_ = lean_ctor_get(v___x_5040_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5040_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_5040_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5040_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5064_, v___y_5065_, v___y_5066_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_){
_start:
{
lean_object* v___x_5073_; lean_object* v_env_5074_; lean_object* v___x_5075_; 
v___x_5073_ = lean_st_ref_get(v___y_5071_);
v_env_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc_ref(v_env_5074_);
lean_dec(v___x_5073_);
lean_inc(v_constName_5069_);
v___x_5075_ = l_Lean_isInductiveCore_x3f(v_env_5074_, v_constName_5069_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v___x_5076_; uint8_t v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5076_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5077_ = 0;
v___x_5078_ = l_Lean_MessageData_ofConstName(v_constName_5069_, v___x_5077_);
v___x_5079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5079_, 0, v___x_5076_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
v___x_5080_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5079_);
lean_ctor_set(v___x_5081_, 1, v___x_5080_);
v___x_5082_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5081_, v___y_5070_, v___y_5071_);
return v___x_5082_;
}
else
{
lean_object* v_val_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5090_; 
lean_dec(v_constName_5069_);
v_val_5083_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_5075_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_val_5083_);
lean_dec(v___x_5075_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5086_ == 0)
{
lean_ctor_set_tag(v___x_5085_, 0);
v___x_5088_ = v___x_5085_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_val_5083_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5091_, v___y_5092_, v___y_5093_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
return v_res_5095_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5098_ = l_Lean_stringToMessageData(v___x_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v___x_5106_; 
lean_inc(v_declName_5099_);
v___x_5106_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5099_, v___y_5100_, v___y_5101_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; uint8_t v___x_5108_; lean_object* v___x_5109_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5107_);
lean_dec_ref_known(v___x_5106_, 1);
v___x_5108_ = 0;
lean_inc(v_declName_5099_);
v___x_5109_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5107_, v_declName_5099_, v___x_5108_, v___y_5100_, v___y_5101_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_object* v_a_5110_; uint8_t v___x_5111_; 
v_a_5110_ = lean_ctor_get(v___x_5109_, 0);
lean_inc(v_a_5110_);
lean_dec_ref_known(v___x_5109_, 1);
v___x_5111_ = lean_unbox(v_a_5110_);
lean_dec(v_a_5110_);
if (v___x_5111_ == 0)
{
uint8_t v___x_5112_; lean_object* v___x_5113_; 
v___x_5112_ = 1;
lean_inc(v_declName_5099_);
v___x_5113_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5107_, v_declName_5099_, v___x_5112_, v___y_5100_, v___y_5101_);
lean_dec(v_a_5107_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; uint8_t v___x_5115_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_a_5114_);
lean_dec_ref_known(v___x_5113_, 1);
v___x_5115_ = lean_unbox(v_a_5114_);
lean_dec(v_a_5114_);
if (v___x_5115_ == 0)
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; 
v___x_5116_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5117_ = l_Lean_MessageData_ofConstName(v_declName_5099_, v___x_5108_);
v___x_5118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5116_);
lean_ctor_set(v___x_5118_, 1, v___x_5117_);
v___x_5119_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5120_, 0, v___x_5118_);
lean_ctor_set(v___x_5120_, 1, v___x_5119_);
v___x_5121_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5120_, v___y_5100_, v___y_5101_);
return v___x_5121_;
}
else
{
lean_dec(v_declName_5099_);
goto v___jp_5103_;
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
lean_dec(v_declName_5099_);
v_a_5122_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5113_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5113_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
}
}
else
{
lean_dec(v_a_5107_);
lean_dec(v_declName_5099_);
goto v___jp_5103_;
}
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5137_; 
lean_dec(v_a_5107_);
lean_dec(v_declName_5099_);
v_a_5130_ = lean_ctor_get(v___x_5109_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5109_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5132_ = v___x_5109_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5109_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5135_; 
if (v_isShared_5133_ == 0)
{
v___x_5135_ = v___x_5132_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5130_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
lean_dec(v_declName_5099_);
v_a_5138_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5106_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5106_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
v___jp_5103_:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5104_ = lean_box(0);
v___x_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
return v___x_5105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5146_, v___y_5147_, v___y_5148_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_){
_start:
{
lean_object* v___f_5155_; lean_object* v___x_5156_; 
lean_inc(v_declName_5151_);
v___f_5155_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5155_, 0, v_declName_5151_);
v___x_5156_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5151_, v___f_5155_, v_a_5152_, v_a_5153_);
return v___x_5156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5157_, v_a_5158_, v_a_5159_);
lean_dec(v_a_5159_);
lean_dec_ref(v_a_5158_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5162_, uint8_t v_addHypotheses_5163_, lean_object* v_as_5164_, lean_object* v_as_x27_5165_, lean_object* v_b_5166_, lean_object* v_a_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_){
_start:
{
lean_object* v___x_5171_; 
v___x_5171_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5162_, v_addHypotheses_5163_, v_as_x27_5165_, v_b_5166_, v___y_5168_, v___y_5169_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5172_, lean_object* v_addHypotheses_5173_, lean_object* v_as_5174_, lean_object* v_as_x27_5175_, lean_object* v_b_5176_, lean_object* v_a_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
uint8_t v_addHypotheses_boxed_5181_; lean_object* v_res_5182_; 
v_addHypotheses_boxed_5181_ = lean_unbox(v_addHypotheses_5173_);
v_res_5182_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5172_, v_addHypotheses_boxed_5181_, v_as_5174_, v_as_x27_5175_, v_b_5176_, v_a_5177_, v___y_5178_, v___y_5179_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec(v_as_x27_5175_);
lean_dec(v_as_5174_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5183_, v___y_5185_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5188_, v___y_5189_, v___y_5190_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5193_, lean_object* v_msg_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5194_, v___y_5195_, v___y_5196_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5199_, lean_object* v_msg_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5199_, v_msg_5200_, v___y_5201_, v___y_5202_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5205_, lean_object* v_macroStack_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v___x_5210_; 
v___x_5210_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5205_, v_macroStack_5206_, v___y_5208_);
return v___x_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5211_, lean_object* v_macroStack_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5211_, v_macroStack_5212_, v___y_5213_, v___y_5214_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v___x_5220_; lean_object* v_env_5221_; uint8_t v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5220_ = lean_st_ref_get(v___y_5218_);
v_env_5221_ = lean_ctor_get(v___x_5220_, 0);
lean_inc_ref(v_env_5221_);
lean_dec(v___x_5220_);
v___x_5222_ = l_Lean_isInductiveCore(v_env_5221_, v_declName_5217_);
v___x_5223_ = lean_box(v___x_5222_);
v___x_5224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5225_, v___y_5226_);
lean_dec(v___y_5226_);
return v_res_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5229_, v___y_5231_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
lean_object* v_res_5238_; 
v_res_5238_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5234_, v___y_5235_, v___y_5236_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
uint8_t v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; 
v___x_5243_ = lean_bool_not(v_____do__lift_5239_);
v___x_5244_ = lean_box(v___x_5243_);
v___x_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5244_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
uint8_t v_____do__lift_1626__boxed_5250_; lean_object* v_res_5251_; 
v_____do__lift_1626__boxed_5250_ = lean_unbox(v_____do__lift_5246_);
v_res_5251_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1626__boxed_5250_, v___y_5247_, v___y_5248_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5252_, size_t v_i_5253_, size_t v_stop_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_){
_start:
{
uint8_t v___x_5258_; 
v___x_5258_ = lean_usize_dec_eq(v_i_5253_, v_stop_5254_);
if (v___x_5258_ == 0)
{
uint8_t v___x_5259_; uint8_t v_a_5261_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5259_ = 1;
v___x_5267_ = lean_array_uget_borrowed(v_as_5252_, v_i_5253_);
lean_inc(v___x_5267_);
v___x_5268_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5267_, v___y_5256_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v_a_5269_; uint8_t v___x_5270_; uint8_t v___x_5271_; 
v_a_5269_ = lean_ctor_get(v___x_5268_, 0);
lean_inc(v_a_5269_);
lean_dec_ref_known(v___x_5268_, 1);
v___x_5270_ = lean_unbox(v_a_5269_);
lean_dec(v_a_5269_);
v___x_5271_ = lean_bool_not(v___x_5270_);
v_a_5261_ = v___x_5271_;
goto v___jp_5260_;
}
else
{
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v_a_5272_; uint8_t v___x_5273_; 
v_a_5272_ = lean_ctor_get(v___x_5268_, 0);
lean_inc(v_a_5272_);
lean_dec_ref_known(v___x_5268_, 1);
v___x_5273_ = lean_unbox(v_a_5272_);
lean_dec(v_a_5272_);
v_a_5261_ = v___x_5273_;
goto v___jp_5260_;
}
else
{
return v___x_5268_;
}
}
v___jp_5260_:
{
if (v_a_5261_ == 0)
{
size_t v___x_5262_; size_t v___x_5263_; 
v___x_5262_ = ((size_t)1ULL);
v___x_5263_ = lean_usize_add(v_i_5253_, v___x_5262_);
v_i_5253_ = v___x_5263_;
goto _start;
}
else
{
lean_object* v___x_5265_; lean_object* v___x_5266_; 
v___x_5265_ = lean_box(v___x_5259_);
v___x_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5265_);
return v___x_5266_;
}
}
}
else
{
uint8_t v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; 
v___x_5274_ = 0;
v___x_5275_ = lean_box(v___x_5274_);
v___x_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5276_, 0, v___x_5275_);
return v___x_5276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object* v_as_5277_, lean_object* v_i_5278_, lean_object* v_stop_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
size_t v_i_boxed_5283_; size_t v_stop_boxed_5284_; lean_object* v_res_5285_; 
v_i_boxed_5283_ = lean_unbox_usize(v_i_5278_);
lean_dec(v_i_5278_);
v_stop_boxed_5284_ = lean_unbox_usize(v_stop_5279_);
lean_dec(v_stop_5279_);
v_res_5285_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5277_, v_i_boxed_5283_, v_stop_boxed_5284_, v___y_5280_, v___y_5281_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec_ref(v_as_5277_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object* v_as_5286_, size_t v_i_5287_, size_t v_stop_5288_, lean_object* v_b_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
uint8_t v___x_5293_; 
v___x_5293_ = lean_usize_dec_eq(v_i_5287_, v_stop_5288_);
if (v___x_5293_ == 0)
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5294_ = lean_array_uget_borrowed(v_as_5286_, v_i_5287_);
lean_inc(v___x_5294_);
v___x_5295_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v___x_5294_, v___y_5290_, v___y_5291_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; size_t v___x_5297_; size_t v___x_5298_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
lean_inc(v_a_5296_);
lean_dec_ref_known(v___x_5295_, 1);
v___x_5297_ = ((size_t)1ULL);
v___x_5298_ = lean_usize_add(v_i_5287_, v___x_5297_);
v_i_5287_ = v___x_5298_;
v_b_5289_ = v_a_5296_;
goto _start;
}
else
{
return v___x_5295_;
}
}
else
{
lean_object* v___x_5300_; 
v___x_5300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5300_, 0, v_b_5289_);
return v___x_5300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object* v_as_5301_, lean_object* v_i_5302_, lean_object* v_stop_5303_, lean_object* v_b_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_){
_start:
{
size_t v_i_boxed_5308_; size_t v_stop_boxed_5309_; lean_object* v_res_5310_; 
v_i_boxed_5308_ = lean_unbox_usize(v_i_5302_);
lean_dec(v_i_5302_);
v_stop_boxed_5309_ = lean_unbox_usize(v_stop_5303_);
lean_dec(v_stop_5303_);
v_res_5310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5301_, v_i_boxed_5308_, v_stop_boxed_5309_, v_b_5304_, v___y_5305_, v___y_5306_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec_ref(v_as_5301_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object* v_declNames_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_){
_start:
{
uint8_t v___y_5316_; lean_object* v___y_5317_; lean_object* v___x_5335_; lean_object* v___x_5336_; uint8_t v_a_5338_; lean_object* v___y_5355_; uint8_t v___x_5358_; 
v___x_5335_ = lean_unsigned_to_nat(0u);
v___x_5336_ = lean_array_get_size(v_declNames_5311_);
v___x_5358_ = lean_nat_dec_lt(v___x_5335_, v___x_5336_);
if (v___x_5358_ == 0)
{
lean_object* v___x_5359_; 
v___x_5359_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5358_, v_a_5312_, v_a_5313_);
v___y_5355_ = v___x_5359_;
goto v___jp_5354_;
}
else
{
if (v___x_5358_ == 0)
{
uint8_t v___x_5360_; 
v___x_5360_ = lean_bool_not(v___x_5358_);
v_a_5338_ = v___x_5360_;
goto v___jp_5337_;
}
else
{
size_t v___x_5361_; size_t v___x_5362_; lean_object* v___x_5363_; 
v___x_5361_ = ((size_t)0ULL);
v___x_5362_ = lean_usize_of_nat(v___x_5336_);
v___x_5363_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5311_, v___x_5361_, v___x_5362_, v_a_5312_, v_a_5313_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v_a_5364_; uint8_t v___x_5365_; lean_object* v___x_5366_; 
v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
lean_inc(v_a_5364_);
lean_dec_ref_known(v___x_5363_, 1);
v___x_5365_ = lean_unbox(v_a_5364_);
lean_dec(v_a_5364_);
v___x_5366_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5365_, v_a_5312_, v_a_5313_);
v___y_5355_ = v___x_5366_;
goto v___jp_5354_;
}
else
{
v___y_5355_ = v___x_5363_;
goto v___jp_5354_;
}
}
}
v___jp_5315_:
{
if (lean_obj_tag(v___y_5317_) == 0)
{
lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5325_; 
v_isSharedCheck_5325_ = !lean_is_exclusive(v___y_5317_);
if (v_isSharedCheck_5325_ == 0)
{
lean_object* v_unused_5326_; 
v_unused_5326_ = lean_ctor_get(v___y_5317_, 0);
lean_dec(v_unused_5326_);
v___x_5319_ = v___y_5317_;
v_isShared_5320_ = v_isSharedCheck_5325_;
goto v_resetjp_5318_;
}
else
{
lean_dec(v___y_5317_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5325_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5321_; lean_object* v___x_5323_; 
v___x_5321_ = lean_box(v___y_5316_);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v___x_5321_);
v___x_5323_ = v___x_5319_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v___x_5321_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5334_; 
v_a_5327_ = lean_ctor_get(v___y_5317_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___y_5317_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5329_ = v___y_5317_;
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___y_5317_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5332_; 
if (v_isShared_5330_ == 0)
{
v___x_5332_ = v___x_5329_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
v___jp_5337_:
{
if (v_a_5338_ == 0)
{
lean_object* v___x_5339_; lean_object* v___x_5340_; 
v___x_5339_ = lean_box(v_a_5338_);
v___x_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5340_, 0, v___x_5339_);
return v___x_5340_;
}
else
{
uint8_t v___x_5341_; 
v___x_5341_ = lean_nat_dec_lt(v___x_5335_, v___x_5336_);
if (v___x_5341_ == 0)
{
lean_object* v___x_5342_; lean_object* v___x_5343_; 
v___x_5342_ = lean_box(v_a_5338_);
v___x_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5342_);
return v___x_5343_;
}
else
{
lean_object* v___x_5344_; uint8_t v___x_5345_; 
v___x_5344_ = lean_box(0);
v___x_5345_ = lean_nat_dec_le(v___x_5336_, v___x_5336_);
if (v___x_5345_ == 0)
{
if (v___x_5341_ == 0)
{
lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5346_ = lean_box(v_a_5338_);
v___x_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5346_);
return v___x_5347_;
}
else
{
size_t v___x_5348_; size_t v___x_5349_; lean_object* v___x_5350_; 
v___x_5348_ = ((size_t)0ULL);
v___x_5349_ = lean_usize_of_nat(v___x_5336_);
v___x_5350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5311_, v___x_5348_, v___x_5349_, v___x_5344_, v_a_5312_, v_a_5313_);
v___y_5316_ = v_a_5338_;
v___y_5317_ = v___x_5350_;
goto v___jp_5315_;
}
}
else
{
size_t v___x_5351_; size_t v___x_5352_; lean_object* v___x_5353_; 
v___x_5351_ = ((size_t)0ULL);
v___x_5352_ = lean_usize_of_nat(v___x_5336_);
v___x_5353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5311_, v___x_5351_, v___x_5352_, v___x_5344_, v_a_5312_, v_a_5313_);
v___y_5316_ = v_a_5338_;
v___y_5317_ = v___x_5353_;
goto v___jp_5315_;
}
}
}
}
v___jp_5354_:
{
if (lean_obj_tag(v___y_5355_) == 0)
{
lean_object* v_a_5356_; uint8_t v___x_5357_; 
v_a_5356_ = lean_ctor_get(v___y_5355_, 0);
lean_inc(v_a_5356_);
lean_dec_ref_known(v___y_5355_, 1);
v___x_5357_ = lean_unbox(v_a_5356_);
lean_dec(v_a_5356_);
v_a_5338_ = v___x_5357_;
goto v___jp_5337_;
}
else
{
return v___y_5355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5367_, v_a_5368_, v_a_5369_);
lean_dec(v_a_5369_);
lean_dec_ref(v_a_5368_);
lean_dec_ref(v_declNames_5367_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5436_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5437_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5438_ = l_Lean_Elab_registerDerivingHandler(v___x_5436_, v___x_5437_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v___x_5439_; uint8_t v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
lean_dec_ref_known(v___x_5438_, 1);
v___x_5439_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5440_ = 0;
v___x_5441_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5442_ = l_Lean_registerTraceClass(v___x_5439_, v___x_5440_, v___x_5441_);
return v___x_5442_;
}
else
{
return v___x_5438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5444_;
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
