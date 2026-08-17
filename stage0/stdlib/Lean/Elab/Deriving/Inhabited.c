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
v___x_923_ = lean_st_ref_put(v_a_908_, v___x_922_);
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
v___x_951_ = lean_st_ref_put(v_a_932_, v___x_950_);
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
lean_object* v_options_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_options_1357_ = lean_ctor_get(v___y_1355_, 2);
v___x_1358_ = l_Lean_Elab_pp_macroStack;
v___x_1359_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_dec(v_macroStack_1354_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_msgData_1353_);
return v___x_1360_;
}
else
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1380_, lean_object* v_macroStack_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1380_, v_macroStack_1381_, v___y_1382_);
lean_dec_ref(v___y_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(lean_object* v_msg_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_ref_1393_; lean_object* v___x_1394_; lean_object* v_a_1395_; lean_object* v_macroStack_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_ref_1393_ = lean_ctor_get(v___y_1390_, 5);
v___x_1394_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1385_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v_macroStack_1396_ = lean_ctor_get(v___y_1386_, 1);
v___x_1397_ = l_Lean_Elab_getBetterRef(v_ref_1393_, v_macroStack_1396_);
lean_inc(v_macroStack_1396_);
v___x_1398_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_a_1395_, v_macroStack_1396_, v___y_1390_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1397_);
lean_ctor_set(v___x_1403_, 1, v_a_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 1);
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1416_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__0));
v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__2));
v___x_1422_ = l_Lean_stringToMessageData(v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(lean_object* v_constName_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v_env_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_st_ref_get(v___y_1429_);
v_env_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc_ref(v_env_1432_);
lean_dec(v___x_1431_);
lean_inc(v_constName_1423_);
v___x_1433_ = l_Lean_isInductiveCore_x3f(v_env_1432_, v_constName_1423_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1434_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_1435_ = 0;
v___x_1436_ = l_Lean_MessageData_ofConstName(v_constName_1423_, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1434_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_1439_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1440_;
}
else
{
lean_object* v_val_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_constName_1423_);
v_val_1441_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1433_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_val_1441_);
lean_dec(v___x_1433_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set_tag(v___x_1443_, 0);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_val_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___boxed(lean_object* v_constName_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_constName_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(size_t v_sz_1458_, size_t v_i_1459_, lean_object* v_bs_1460_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_usize_dec_lt(v_i_1459_, v_sz_1458_);
if (v___x_1461_ == 0)
{
return v_bs_1460_;
}
else
{
lean_object* v_v_1462_; lean_object* v___x_1463_; lean_object* v_bs_x27_1464_; size_t v___x_1465_; size_t v___x_1466_; lean_object* v___x_1467_; 
v_v_1462_ = lean_array_uget(v_bs_1460_, v_i_1459_);
v___x_1463_ = lean_unsigned_to_nat(0u);
v_bs_x27_1464_ = lean_array_uset(v_bs_1460_, v_i_1459_, v___x_1463_);
v___x_1465_ = ((size_t)1ULL);
v___x_1466_ = lean_usize_add(v_i_1459_, v___x_1465_);
v___x_1467_ = lean_array_uset(v_bs_x27_1464_, v_i_1459_, v_v_1462_);
v_i_1459_ = v___x_1466_;
v_bs_1460_ = v___x_1467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0___boxed(lean_object* v_sz_1469_, lean_object* v_i_1470_, lean_object* v_bs_1471_){
_start:
{
size_t v_sz_boxed_1472_; size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_sz_boxed_1472_ = lean_unbox_usize(v_sz_1469_);
lean_dec(v_sz_1469_);
v_i_boxed_1473_ = lean_unbox_usize(v_i_1470_);
lean_dec(v_i_1470_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_boxed_1472_, v_i_boxed_1473_, v_bs_1471_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(lean_object* v_inductiveTypeName_1552_, lean_object* v_instId_1553_, lean_object* v_usedInstIdxs_1554_, lean_object* v_auxFunId_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1563_; 
lean_inc(v_inductiveTypeName_1552_);
v___x_1563_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_1552_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v_numParams_1565_; lean_object* v_numIndices_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v_numParams_1565_ = lean_ctor_get(v_a_1564_, 1);
lean_inc(v_numParams_1565_);
v_numIndices_1566_ = lean_ctor_get(v_a_1564_, 2);
lean_inc(v_numIndices_1566_);
lean_dec(v_a_1564_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_nat_add(v_numParams_1565_, v_numIndices_1566_);
lean_dec(v_numIndices_1566_);
lean_dec(v_numParams_1565_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__1));
v___x_1570_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v___x_1568_, v_usedInstIdxs_1554_, v___x_1567_, v___x_1569_, v_a_1560_, v_a_1561_);
lean_dec(v___x_1568_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1647_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1647_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1647_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_fst_1575_; lean_object* v_snd_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1646_; 
v_fst_1575_ = lean_ctor_get(v_a_1571_, 0);
v_snd_1576_ = lean_ctor_get(v_a_1571_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_a_1571_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1578_ = v_a_1571_;
v_isShared_1579_ = v_isSharedCheck_1646_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_snd_1576_);
lean_inc(v_fst_1575_);
lean_dec(v_a_1571_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1646_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_ref_1580_; lean_object* v_quotContext_1581_; lean_object* v_currMacroScope_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
v_ref_1580_ = lean_ctor_get(v_a_1560_, 5);
v_quotContext_1581_ = lean_ctor_get(v_a_1560_, 10);
v_currMacroScope_1582_ = lean_ctor_get(v_a_1560_, 11);
v___x_1583_ = 0;
v___x_1584_ = l_Lean_SourceInfo_fromRef(v_ref_1580_, v___x_1583_);
v___x_1585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__16));
v___x_1586_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__3));
v___x_1587_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__4));
lean_inc(v___x_1584_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 2);
lean_ctor_set(v___x_1578_, 1, v___x_1587_);
lean_ctor_set(v___x_1578_, 0, v___x_1584_);
v___x_1589_ = v___x_1578_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; size_t v_sz_1610_; size_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1590_ = l_Lean_mkCIdent(v_inductiveTypeName_1552_);
lean_inc_n(v___x_1584_, 24);
v___x_1591_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1586_, v___x_1589_, v___x_1590_);
v___x_1592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__9));
v___x_1593_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__10);
v___x_1594_ = l_Array_append___redArg(v___x_1593_, v_fst_1575_);
lean_dec(v_fst_1575_);
v___x_1595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1584_);
lean_ctor_set(v___x_1595_, 1, v___x_1592_);
lean_ctor_set(v___x_1595_, 2, v___x_1594_);
v___x_1596_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1585_, v___x_1591_, v___x_1595_);
v___x_1597_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__7));
v___x_1598_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__9));
v___x_1599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1584_);
lean_ctor_set(v___x_1599_, 1, v___x_1592_);
lean_ctor_set(v___x_1599_, 2, v___x_1593_);
lean_inc_ref_n(v___x_1599_, 12);
v___x_1600_ = l_Lean_Syntax_node7(v___x_1584_, v___x_1598_, v___x_1599_, v___x_1599_, v___x_1599_, v___x_1599_, v___x_1599_, v___x_1599_, v___x_1599_);
v___x_1601_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__10));
v___x_1602_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__11));
v___x_1603_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__13));
v___x_1604_ = l_Lean_Syntax_node1(v___x_1584_, v___x_1603_, v___x_1599_);
v___x_1605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1584_);
lean_ctor_set(v___x_1605_, 1, v___x_1601_);
v___x_1606_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__15));
v___x_1607_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1606_, v_instId_1553_, v___x_1599_);
v___x_1608_ = l_Lean_Syntax_node1(v___x_1584_, v___x_1592_, v___x_1607_);
v___x_1609_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__17));
v_sz_1610_ = lean_array_size(v_snd_1576_);
v___x_1611_ = ((size_t)0ULL);
v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__0(v_sz_1610_, v___x_1611_, v_snd_1576_);
v___x_1613_ = l_Array_append___redArg(v___x_1593_, v___x_1612_);
lean_dec_ref(v___x_1612_);
v___x_1614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1584_);
lean_ctor_set(v___x_1614_, 1, v___x_1592_);
lean_ctor_set(v___x_1614_, 2, v___x_1613_);
v___x_1615_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__19));
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__20));
v___x_1617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1584_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__17);
v___x_1619_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
lean_inc(v_currMacroScope_1582_);
lean_inc(v_quotContext_1581_);
v___x_1620_ = l_Lean_addMacroScope(v_quotContext_1581_, v___x_1619_, v_currMacroScope_1582_);
v___x_1621_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg___closed__21));
v___x_1622_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1584_);
lean_ctor_set(v___x_1622_, 1, v___x_1618_);
lean_ctor_set(v___x_1622_, 2, v___x_1620_);
lean_ctor_set(v___x_1622_, 3, v___x_1621_);
v___x_1623_ = l_Lean_Syntax_node1(v___x_1584_, v___x_1592_, v___x_1596_);
v___x_1624_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1585_, v___x_1622_, v___x_1623_);
v___x_1625_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1615_, v___x_1617_, v___x_1624_);
v___x_1626_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1609_, v___x_1614_, v___x_1625_);
v___x_1627_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__22));
v___x_1628_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__23));
v___x_1629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1584_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__25));
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__26));
v___x_1632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1584_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Lean_Syntax_node1(v___x_1584_, v___x_1592_, v_auxFunId_1555_);
v___x_1634_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__27));
v___x_1635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1584_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_Syntax_node3(v___x_1584_, v___x_1630_, v___x_1632_, v___x_1633_, v___x_1635_);
v___x_1637_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___closed__30));
v___x_1638_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1637_, v___x_1599_, v___x_1599_);
v___x_1639_ = l_Lean_Syntax_node4(v___x_1584_, v___x_1627_, v___x_1629_, v___x_1636_, v___x_1638_, v___x_1599_);
v___x_1640_ = l_Lean_Syntax_node6(v___x_1584_, v___x_1602_, v___x_1604_, v___x_1605_, v___x_1599_, v___x_1608_, v___x_1626_, v___x_1639_);
v___x_1641_ = l_Lean_Syntax_node2(v___x_1584_, v___x_1597_, v___x_1600_, v___x_1640_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1641_);
v___x_1643_ = v___x_1573_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v_auxFunId_1555_);
lean_dec(v_instId_1553_);
lean_dec(v_inductiveTypeName_1552_);
v_a_1648_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1570_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1570_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_auxFunId_1555_);
lean_dec(v_instId_1553_);
lean_dec(v_inductiveTypeName_1552_);
v_a_1656_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1563_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1563_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith___boxed(lean_object* v_inductiveTypeName_1664_, lean_object* v_instId_1665_, lean_object* v_usedInstIdxs_1666_, lean_object* v_auxFunId_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_1664_, v_instId_1665_, v_usedInstIdxs_1666_, v_auxFunId_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_usedInstIdxs_1666_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(lean_object* v_upperBound_1676_, lean_object* v_usedInstIdxs_1677_, lean_object* v_inst_1678_, lean_object* v_R_1679_, lean_object* v_a_1680_, lean_object* v_b_1681_, lean_object* v_c_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___redArg(v_upperBound_1676_, v_usedInstIdxs_1677_, v_a_1680_, v_b_1681_, v___y_1687_, v___y_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2___boxed(lean_object* v_upperBound_1691_, lean_object* v_usedInstIdxs_1692_, lean_object* v_inst_1693_, lean_object* v_R_1694_, lean_object* v_a_1695_, lean_object* v_b_1696_, lean_object* v_c_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__2(v_upperBound_1691_, v_usedInstIdxs_1692_, v_inst_1693_, v_R_1694_, v_a_1695_, v_b_1696_, v_c_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v_usedInstIdxs_1692_);
lean_dec(v_upperBound_1691_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(lean_object* v_00_u03b1_1706_, lean_object* v_msg_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v_msg_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1716_, lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1(v_00_u03b1_1716_, v_msg_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(lean_object* v_msgData_1726_, lean_object* v_macroStack_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg(v_msgData_1726_, v_macroStack_1727_, v___y_1732_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1736_, lean_object* v_macroStack_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2(v_msgData_1736_, v_macroStack_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1745_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_unsigned_to_nat(32u);
v___x_1747_ = lean_mk_empty_array_with_capacity(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1749_ = ((size_t)5ULL);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_unsigned_to_nat(32u);
v___x_1752_ = lean_mk_empty_array_with_capacity(v___x_1751_);
v___x_1753_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__0);
v___x_1754_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v___x_1752_);
lean_ctor_set(v___x_1754_, 2, v___x_1750_);
lean_ctor_set(v___x_1754_, 3, v___x_1750_);
lean_ctor_set_usize(v___x_1754_, 4, v___x_1749_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v_traceState_1758_; lean_object* v_traces_1759_; lean_object* v___x_1760_; lean_object* v_traceState_1761_; lean_object* v_env_1762_; lean_object* v_nextMacroScope_1763_; lean_object* v_ngen_1764_; lean_object* v_auxDeclNGen_1765_; lean_object* v_cache_1766_; lean_object* v_messages_1767_; lean_object* v_infoState_1768_; lean_object* v_snapshotTasks_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1788_; 
v___x_1757_ = lean_st_ref_get(v___y_1755_);
v_traceState_1758_ = lean_ctor_get(v___x_1757_, 4);
lean_inc_ref(v_traceState_1758_);
lean_dec(v___x_1757_);
v_traces_1759_ = lean_ctor_get(v_traceState_1758_, 0);
lean_inc_ref(v_traces_1759_);
lean_dec_ref(v_traceState_1758_);
v___x_1760_ = lean_st_ref_take(v___y_1755_);
v_traceState_1761_ = lean_ctor_get(v___x_1760_, 4);
v_env_1762_ = lean_ctor_get(v___x_1760_, 0);
v_nextMacroScope_1763_ = lean_ctor_get(v___x_1760_, 1);
v_ngen_1764_ = lean_ctor_get(v___x_1760_, 2);
v_auxDeclNGen_1765_ = lean_ctor_get(v___x_1760_, 3);
v_cache_1766_ = lean_ctor_get(v___x_1760_, 5);
v_messages_1767_ = lean_ctor_get(v___x_1760_, 6);
v_infoState_1768_ = lean_ctor_get(v___x_1760_, 7);
v_snapshotTasks_1769_ = lean_ctor_get(v___x_1760_, 8);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1771_ = v___x_1760_;
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snapshotTasks_1769_);
lean_inc(v_infoState_1768_);
lean_inc(v_messages_1767_);
lean_inc(v_cache_1766_);
lean_inc(v_traceState_1761_);
lean_inc(v_auxDeclNGen_1765_);
lean_inc(v_ngen_1764_);
lean_inc(v_nextMacroScope_1763_);
lean_inc(v_env_1762_);
lean_dec(v___x_1760_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
uint64_t v_tid_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1786_; 
v_tid_1773_ = lean_ctor_get_uint64(v_traceState_1761_, sizeof(void*)*1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_traceState_1761_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v_traceState_1761_, 0);
lean_dec(v_unused_1787_);
v___x_1775_ = v_traceState_1761_;
v_isShared_1776_ = v_isSharedCheck_1786_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v_traceState_1761_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1786_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___closed__1);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1777_);
v___x_1779_ = v___x_1775_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1777_);
lean_ctor_set_uint64(v_reuseFailAlloc_1785_, sizeof(void*)*1, v_tid_1773_);
v___x_1779_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 4, v___x_1779_);
v___x_1781_ = v___x_1771_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_env_1762_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_nextMacroScope_1763_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_ngen_1764_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_auxDeclNGen_1765_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1784_, 5, v_cache_1766_);
lean_ctor_set(v_reuseFailAlloc_1784_, 6, v_messages_1767_);
lean_ctor_set(v_reuseFailAlloc_1784_, 7, v_infoState_1768_);
lean_ctor_set(v_reuseFailAlloc_1784_, 8, v_snapshotTasks_1769_);
v___x_1781_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_st_ref_put(v___y_1755_, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_traces_1759_);
return v___x_1783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg___boxed(lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1789_);
lean_dec(v___y_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_1797_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___boxed(lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2(v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(lean_object* v_x_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
v___x_1816_ = lean_apply_7(v_x_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, lean_box(0));
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed(lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0(v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(lean_object* v_mvarId_1826_, lean_object* v_x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___f_1835_; lean_object* v___x_1836_; 
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
v___f_1835_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1835_, 0, v_x_1827_);
lean_closure_set(v___f_1835_, 1, v___y_1828_);
lean_closure_set(v___f_1835_, 2, v___y_1829_);
v___x_1836_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1826_, v___f_1835_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1836_) == 0)
{
return v___x_1836_;
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg___boxed(lean_object* v_mvarId_1845_, lean_object* v_x_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1845_, v_x_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(lean_object* v_00_u03b1_1855_, lean_object* v_mvarId_1856_, lean_object* v_x_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v_mvarId_1856_, v_x_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___boxed(lean_object* v_00_u03b1_1866_, lean_object* v_mvarId_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4(v_00_u03b1_1866_, v_mvarId_1867_, v_x_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1876_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__0));
v___x_1879_ = l_Lean_stringToMessageData(v___x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(lean_object* v_a_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___closed__1);
v___x_1890_ = lean_unsigned_to_nat(30u);
v___x_1891_ = l_Lean_inlineExprTrailing(v_a_1880_, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1889_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed(lean_object* v_a_1894_, lean_object* v_x_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0(v_a_1894_, v_x_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v_x_1895_);
return v_res_1903_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(lean_object* v_e_1904_){
_start:
{
if (lean_obj_tag(v_e_1904_) == 0)
{
uint8_t v___x_1905_; 
v___x_1905_ = 2;
return v___x_1905_;
}
else
{
uint8_t v___x_1906_; 
v___x_1906_ = 0;
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7___boxed(lean_object* v_e_1907_){
_start:
{
uint8_t v_res_1908_; lean_object* v_r_1909_; 
v_res_1908_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_e_1907_);
lean_dec_ref(v_e_1907_);
v_r_1909_ = lean_box(v_res_1908_);
return v_r_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(lean_object* v_opts_1910_, lean_object* v_opt_1911_){
_start:
{
lean_object* v_name_1912_; lean_object* v_defValue_1913_; lean_object* v_map_1914_; lean_object* v___x_1915_; 
v_name_1912_ = lean_ctor_get(v_opt_1911_, 0);
v_defValue_1913_ = lean_ctor_get(v_opt_1911_, 1);
v_map_1914_ = lean_ctor_get(v_opts_1910_, 0);
v___x_1915_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1914_, v_name_1912_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_inc(v_defValue_1913_);
return v_defValue_1913_;
}
else
{
lean_object* v_val_1916_; 
v_val_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v___x_1915_, 1);
if (lean_obj_tag(v_val_1916_) == 3)
{
lean_object* v_v_1917_; 
v_v_1917_ = lean_ctor_get(v_val_1916_, 0);
lean_inc(v_v_1917_);
lean_dec_ref_known(v_val_1916_, 1);
return v_v_1917_;
}
else
{
lean_dec(v_val_1916_);
lean_inc(v_defValue_1913_);
return v_defValue_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8___boxed(lean_object* v_opts_1918_, lean_object* v_opt_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_1918_, v_opt_1919_);
lean_dec_ref(v_opt_1919_);
lean_dec_ref(v_opts_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
v_a_1923_ = lean_ctor_get(v_x_1921_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_x_1921_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v_x_1921_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v_x_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set_tag(v___x_1925_, 1);
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_a_1931_ = lean_ctor_get(v_x_1921_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_x_1921_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v_x_1921_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v_x_1921_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 0);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg___boxed(lean_object* v_x_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(size_t v_sz_1942_, size_t v_i_1943_, lean_object* v_bs_1944_){
_start:
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_usize_dec_lt(v_i_1943_, v_sz_1942_);
if (v___x_1945_ == 0)
{
return v_bs_1944_;
}
else
{
lean_object* v_v_1946_; lean_object* v_msg_1947_; lean_object* v___x_1948_; lean_object* v_bs_x27_1949_; size_t v___x_1950_; size_t v___x_1951_; lean_object* v___x_1952_; 
v_v_1946_ = lean_array_uget_borrowed(v_bs_1944_, v_i_1943_);
v_msg_1947_ = lean_ctor_get(v_v_1946_, 1);
lean_inc_ref(v_msg_1947_);
v___x_1948_ = lean_unsigned_to_nat(0u);
v_bs_x27_1949_ = lean_array_uset(v_bs_1944_, v_i_1943_, v___x_1948_);
v___x_1950_ = ((size_t)1ULL);
v___x_1951_ = lean_usize_add(v_i_1943_, v___x_1950_);
v___x_1952_ = lean_array_uset(v_bs_x27_1949_, v_i_1943_, v_msg_1947_);
v_i_1943_ = v___x_1951_;
v_bs_1944_ = v___x_1952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1954_, lean_object* v_i_1955_, lean_object* v_bs_1956_){
_start:
{
size_t v_sz_boxed_1957_; size_t v_i_boxed_1958_; lean_object* v_res_1959_; 
v_sz_boxed_1957_ = lean_unbox_usize(v_sz_1954_);
lean_dec(v_sz_1954_);
v_i_boxed_1958_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_res_1959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_boxed_1957_, v_i_boxed_1958_, v_bs_1956_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(lean_object* v_oldTraces_1960_, lean_object* v_data_1961_, lean_object* v_ref_1962_, lean_object* v_msg_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_fileName_1969_; lean_object* v_fileMap_1970_; lean_object* v_options_1971_; lean_object* v_currRecDepth_1972_; lean_object* v_maxRecDepth_1973_; lean_object* v_ref_1974_; lean_object* v_currNamespace_1975_; lean_object* v_openDecls_1976_; lean_object* v_initHeartbeats_1977_; lean_object* v_maxHeartbeats_1978_; lean_object* v_quotContext_1979_; lean_object* v_currMacroScope_1980_; uint8_t v_diag_1981_; lean_object* v_cancelTk_x3f_1982_; uint8_t v_suppressElabErrors_1983_; lean_object* v_inheritedTraceOptions_1984_; lean_object* v___x_1985_; lean_object* v_traceState_1986_; lean_object* v_traces_1987_; lean_object* v_ref_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; size_t v_sz_1991_; size_t v___x_1992_; lean_object* v___x_1993_; lean_object* v_msg_1994_; lean_object* v___x_1995_; lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2033_; 
v_fileName_1969_ = lean_ctor_get(v___y_1966_, 0);
v_fileMap_1970_ = lean_ctor_get(v___y_1966_, 1);
v_options_1971_ = lean_ctor_get(v___y_1966_, 2);
v_currRecDepth_1972_ = lean_ctor_get(v___y_1966_, 3);
v_maxRecDepth_1973_ = lean_ctor_get(v___y_1966_, 4);
v_ref_1974_ = lean_ctor_get(v___y_1966_, 5);
v_currNamespace_1975_ = lean_ctor_get(v___y_1966_, 6);
v_openDecls_1976_ = lean_ctor_get(v___y_1966_, 7);
v_initHeartbeats_1977_ = lean_ctor_get(v___y_1966_, 8);
v_maxHeartbeats_1978_ = lean_ctor_get(v___y_1966_, 9);
v_quotContext_1979_ = lean_ctor_get(v___y_1966_, 10);
v_currMacroScope_1980_ = lean_ctor_get(v___y_1966_, 11);
v_diag_1981_ = lean_ctor_get_uint8(v___y_1966_, sizeof(void*)*14);
v_cancelTk_x3f_1982_ = lean_ctor_get(v___y_1966_, 12);
v_suppressElabErrors_1983_ = lean_ctor_get_uint8(v___y_1966_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1984_ = lean_ctor_get(v___y_1966_, 13);
v___x_1985_ = lean_st_ref_get(v___y_1967_);
v_traceState_1986_ = lean_ctor_get(v___x_1985_, 4);
lean_inc_ref(v_traceState_1986_);
lean_dec(v___x_1985_);
v_traces_1987_ = lean_ctor_get(v_traceState_1986_, 0);
lean_inc_ref(v_traces_1987_);
lean_dec_ref(v_traceState_1986_);
v_ref_1988_ = l_Lean_replaceRef(v_ref_1962_, v_ref_1974_);
lean_inc_ref(v_inheritedTraceOptions_1984_);
lean_inc(v_cancelTk_x3f_1982_);
lean_inc(v_currMacroScope_1980_);
lean_inc(v_quotContext_1979_);
lean_inc(v_maxHeartbeats_1978_);
lean_inc(v_initHeartbeats_1977_);
lean_inc(v_openDecls_1976_);
lean_inc(v_currNamespace_1975_);
lean_inc(v_maxRecDepth_1973_);
lean_inc(v_currRecDepth_1972_);
lean_inc_ref(v_options_1971_);
lean_inc_ref(v_fileMap_1970_);
lean_inc_ref(v_fileName_1969_);
v___x_1989_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1989_, 0, v_fileName_1969_);
lean_ctor_set(v___x_1989_, 1, v_fileMap_1970_);
lean_ctor_set(v___x_1989_, 2, v_options_1971_);
lean_ctor_set(v___x_1989_, 3, v_currRecDepth_1972_);
lean_ctor_set(v___x_1989_, 4, v_maxRecDepth_1973_);
lean_ctor_set(v___x_1989_, 5, v_ref_1988_);
lean_ctor_set(v___x_1989_, 6, v_currNamespace_1975_);
lean_ctor_set(v___x_1989_, 7, v_openDecls_1976_);
lean_ctor_set(v___x_1989_, 8, v_initHeartbeats_1977_);
lean_ctor_set(v___x_1989_, 9, v_maxHeartbeats_1978_);
lean_ctor_set(v___x_1989_, 10, v_quotContext_1979_);
lean_ctor_set(v___x_1989_, 11, v_currMacroScope_1980_);
lean_ctor_set(v___x_1989_, 12, v_cancelTk_x3f_1982_);
lean_ctor_set(v___x_1989_, 13, v_inheritedTraceOptions_1984_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*14, v_diag_1981_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*14 + 1, v_suppressElabErrors_1983_);
v___x_1990_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1987_);
lean_dec_ref(v_traces_1987_);
v_sz_1991_ = lean_array_size(v___x_1990_);
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5_spec__9(v_sz_1991_, v___x_1992_, v___x_1990_);
v_msg_1994_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1994_, 0, v_data_1961_);
lean_ctor_set(v_msg_1994_, 1, v_msg_1963_);
lean_ctor_set(v_msg_1994_, 2, v___x_1993_);
v___x_1995_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0_spec__0(v_msg_1994_, v___y_1964_, v___y_1965_, v___x_1989_, v___y_1967_);
lean_dec_ref_known(v___x_1989_, 14);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2033_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2033_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v_traceState_2001_; lean_object* v_env_2002_; lean_object* v_nextMacroScope_2003_; lean_object* v_ngen_2004_; lean_object* v_auxDeclNGen_2005_; lean_object* v_cache_2006_; lean_object* v_messages_2007_; lean_object* v_infoState_2008_; lean_object* v_snapshotTasks_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2032_; 
v___x_2000_ = lean_st_ref_take(v___y_1967_);
v_traceState_2001_ = lean_ctor_get(v___x_2000_, 4);
v_env_2002_ = lean_ctor_get(v___x_2000_, 0);
v_nextMacroScope_2003_ = lean_ctor_get(v___x_2000_, 1);
v_ngen_2004_ = lean_ctor_get(v___x_2000_, 2);
v_auxDeclNGen_2005_ = lean_ctor_get(v___x_2000_, 3);
v_cache_2006_ = lean_ctor_get(v___x_2000_, 5);
v_messages_2007_ = lean_ctor_get(v___x_2000_, 6);
v_infoState_2008_ = lean_ctor_get(v___x_2000_, 7);
v_snapshotTasks_2009_ = lean_ctor_get(v___x_2000_, 8);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2011_ = v___x_2000_;
v_isShared_2012_ = v_isSharedCheck_2032_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snapshotTasks_2009_);
lean_inc(v_infoState_2008_);
lean_inc(v_messages_2007_);
lean_inc(v_cache_2006_);
lean_inc(v_traceState_2001_);
lean_inc(v_auxDeclNGen_2005_);
lean_inc(v_ngen_2004_);
lean_inc(v_nextMacroScope_2003_);
lean_inc(v_env_2002_);
lean_dec(v___x_2000_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2032_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
uint64_t v_tid_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2030_; 
v_tid_2013_ = lean_ctor_get_uint64(v_traceState_2001_, sizeof(void*)*1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_traceState_2001_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_traceState_2001_, 0);
lean_dec(v_unused_2031_);
v___x_2015_ = v_traceState_2001_;
v_isShared_2016_ = v_isSharedCheck_2030_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v_traceState_2001_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2030_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v_ref_1962_);
lean_ctor_set(v___x_2017_, 1, v_a_1996_);
v___x_2018_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1960_, v___x_2017_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2018_);
v___x_2020_ = v___x_2015_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2018_);
lean_ctor_set_uint64(v_reuseFailAlloc_2029_, sizeof(void*)*1, v_tid_2013_);
v___x_2020_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 4, v___x_2020_);
v___x_2022_ = v___x_2011_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_env_2002_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_nextMacroScope_2003_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_ngen_2004_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v_auxDeclNGen_2005_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 5, v_cache_2006_);
lean_ctor_set(v_reuseFailAlloc_2028_, 6, v_messages_2007_);
lean_ctor_set(v_reuseFailAlloc_2028_, 7, v_infoState_2008_);
lean_ctor_set(v_reuseFailAlloc_2028_, 8, v_snapshotTasks_2009_);
v___x_2022_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = lean_st_ref_put(v___y_1967_, v___x_2022_);
v___x_2024_ = lean_box(0);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2024_);
v___x_2026_ = v___x_1998_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg___boxed(lean_object* v_oldTraces_2034_, lean_object* v_data_2035_, lean_object* v_ref_2036_, lean_object* v_msg_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2034_, v_data_2035_, v_ref_2036_, v_msg_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2043_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__0));
v___x_2046_ = l_Lean_stringToMessageData(v___x_2045_);
return v___x_2046_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2047_; double v___x_2048_; 
v___x_2047_ = lean_unsigned_to_nat(1000u);
v___x_2048_ = lean_float_of_nat(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(lean_object* v_cls_2049_, uint8_t v_collapsed_2050_, lean_object* v_tag_2051_, lean_object* v_opts_2052_, uint8_t v_clsEnabled_2053_, lean_object* v_oldTraces_2054_, lean_object* v_msg_2055_, lean_object* v_resStartStop_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_fst_2064_; lean_object* v_snd_2065_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v_data_2069_; lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___y_2077_; lean_object* v_a_2078_; uint8_t v___y_2093_; double v___y_2124_; 
v_fst_2064_ = lean_ctor_get(v_resStartStop_2056_, 0);
lean_inc(v_fst_2064_);
v_snd_2065_ = lean_ctor_get(v_resStartStop_2056_, 1);
lean_inc(v_snd_2065_);
lean_dec_ref(v_resStartStop_2056_);
v_fst_2072_ = lean_ctor_get(v_snd_2065_, 0);
lean_inc(v_fst_2072_);
v_snd_2073_ = lean_ctor_get(v_snd_2065_, 1);
lean_inc(v_snd_2073_);
lean_dec(v_snd_2065_);
v___x_2074_ = l_Lean_trace_profiler;
v___x_2075_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2052_, v___x_2074_);
if (v___x_2075_ == 0)
{
v___y_2093_ = v___x_2075_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2130_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_2052_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; double v___x_2133_; double v___x_2134_; double v___x_2135_; 
v___x_2131_ = l_Lean_trace_profiler_threshold;
v___x_2132_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2052_, v___x_2131_);
v___x_2133_ = lean_float_of_nat(v___x_2132_);
v___x_2134_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_2135_ = lean_float_div(v___x_2133_, v___x_2134_);
v___y_2124_ = v___x_2135_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; double v___x_2138_; 
v___x_2136_ = l_Lean_trace_profiler_threshold;
v___x_2137_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_2052_, v___x_2136_);
v___x_2138_ = lean_float_of_nat(v___x_2137_);
v___y_2124_ = v___x_2138_;
goto v___jp_2123_;
}
}
v___jp_2066_:
{
lean_object* v___x_2070_; 
lean_inc(v___y_2067_);
v___x_2070_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2054_, v_data_2069_, v___y_2067_, v___y_2068_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v___x_2071_; 
lean_dec_ref_known(v___x_2070_, 1);
v___x_2071_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2064_);
return v___x_2071_;
}
else
{
lean_dec(v_fst_2064_);
return v___x_2070_;
}
}
v___jp_2076_:
{
uint8_t v_result_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; double v___x_2082_; lean_object* v_data_2083_; 
v_result_2079_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__7(v_fst_2064_);
v___x_2080_ = lean_box(v_result_2079_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
v___x_2082_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2051_);
lean_inc_ref(v___x_2081_);
lean_inc(v_cls_2049_);
v_data_2083_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2083_, 0, v_cls_2049_);
lean_ctor_set(v_data_2083_, 1, v___x_2081_);
lean_ctor_set(v_data_2083_, 2, v_tag_2051_);
lean_ctor_set_float(v_data_2083_, sizeof(void*)*3, v___x_2082_);
lean_ctor_set_float(v_data_2083_, sizeof(void*)*3 + 8, v___x_2082_);
lean_ctor_set_uint8(v_data_2083_, sizeof(void*)*3 + 16, v_collapsed_2050_);
if (v___x_2075_ == 0)
{
lean_dec_ref_known(v___x_2081_, 1);
lean_dec(v_snd_2073_);
lean_dec(v_fst_2072_);
lean_dec_ref(v_tag_2051_);
lean_dec(v_cls_2049_);
v___y_2067_ = v___y_2077_;
v___y_2068_ = v_a_2078_;
v_data_2069_ = v_data_2083_;
goto v___jp_2066_;
}
else
{
lean_object* v_data_2084_; double v___x_2085_; double v___x_2086_; 
lean_dec_ref_known(v_data_2083_, 3);
v_data_2084_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2084_, 0, v_cls_2049_);
lean_ctor_set(v_data_2084_, 1, v___x_2081_);
lean_ctor_set(v_data_2084_, 2, v_tag_2051_);
v___x_2085_ = lean_unbox_float(v_fst_2072_);
lean_dec(v_fst_2072_);
lean_ctor_set_float(v_data_2084_, sizeof(void*)*3, v___x_2085_);
v___x_2086_ = lean_unbox_float(v_snd_2073_);
lean_dec(v_snd_2073_);
lean_ctor_set_float(v_data_2084_, sizeof(void*)*3 + 8, v___x_2086_);
lean_ctor_set_uint8(v_data_2084_, sizeof(void*)*3 + 16, v_collapsed_2050_);
v___y_2067_ = v___y_2077_;
v___y_2068_ = v_a_2078_;
v_data_2069_ = v_data_2084_;
goto v___jp_2066_;
}
}
v___jp_2087_:
{
lean_object* v_ref_2088_; lean_object* v___x_2089_; 
v_ref_2088_ = lean_ctor_get(v___y_2061_, 5);
lean_inc(v___y_2062_);
lean_inc_ref(v___y_2061_);
lean_inc(v___y_2060_);
lean_inc_ref(v___y_2059_);
lean_inc(v___y_2058_);
lean_inc_ref(v___y_2057_);
lean_inc(v_fst_2064_);
v___x_2089_ = lean_apply_8(v_msg_2055_, v_fst_2064_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, lean_box(0));
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___y_2077_ = v_ref_2088_;
v_a_2078_ = v_a_2090_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2091_; 
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_2077_ = v_ref_2088_;
v_a_2078_ = v___x_2091_;
goto v___jp_2076_;
}
}
v___jp_2092_:
{
if (v_clsEnabled_2053_ == 0)
{
if (v___y_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v_traceState_2095_; lean_object* v_env_2096_; lean_object* v_nextMacroScope_2097_; lean_object* v_ngen_2098_; lean_object* v_auxDeclNGen_2099_; lean_object* v_cache_2100_; lean_object* v_messages_2101_; lean_object* v_infoState_2102_; lean_object* v_snapshotTasks_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v_snd_2073_);
lean_dec(v_fst_2072_);
lean_dec_ref(v_msg_2055_);
lean_dec_ref(v_tag_2051_);
lean_dec(v_cls_2049_);
v___x_2094_ = lean_st_ref_take(v___y_2062_);
v_traceState_2095_ = lean_ctor_get(v___x_2094_, 4);
v_env_2096_ = lean_ctor_get(v___x_2094_, 0);
v_nextMacroScope_2097_ = lean_ctor_get(v___x_2094_, 1);
v_ngen_2098_ = lean_ctor_get(v___x_2094_, 2);
v_auxDeclNGen_2099_ = lean_ctor_get(v___x_2094_, 3);
v_cache_2100_ = lean_ctor_get(v___x_2094_, 5);
v_messages_2101_ = lean_ctor_get(v___x_2094_, 6);
v_infoState_2102_ = lean_ctor_get(v___x_2094_, 7);
v_snapshotTasks_2103_ = lean_ctor_get(v___x_2094_, 8);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2105_ = v___x_2094_;
v_isShared_2106_ = v_isSharedCheck_2122_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_snapshotTasks_2103_);
lean_inc(v_infoState_2102_);
lean_inc(v_messages_2101_);
lean_inc(v_cache_2100_);
lean_inc(v_traceState_2095_);
lean_inc(v_auxDeclNGen_2099_);
lean_inc(v_ngen_2098_);
lean_inc(v_nextMacroScope_2097_);
lean_inc(v_env_2096_);
lean_dec(v___x_2094_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2122_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
uint64_t v_tid_2107_; lean_object* v_traces_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2121_; 
v_tid_2107_ = lean_ctor_get_uint64(v_traceState_2095_, sizeof(void*)*1);
v_traces_2108_ = lean_ctor_get(v_traceState_2095_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_traceState_2095_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2110_ = v_traceState_2095_;
v_isShared_2111_ = v_isSharedCheck_2121_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_traces_2108_);
lean_dec(v_traceState_2095_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2121_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2054_, v_traces_2108_);
lean_dec_ref(v_traces_2108_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v___x_2112_);
v___x_2114_ = v___x_2110_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2112_);
lean_ctor_set_uint64(v_reuseFailAlloc_2120_, sizeof(void*)*1, v_tid_2107_);
v___x_2114_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 4, v___x_2114_);
v___x_2116_ = v___x_2105_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_env_2096_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_nextMacroScope_2097_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_ngen_2098_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_auxDeclNGen_2099_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2119_, 5, v_cache_2100_);
lean_ctor_set(v_reuseFailAlloc_2119_, 6, v_messages_2101_);
lean_ctor_set(v_reuseFailAlloc_2119_, 7, v_infoState_2102_);
lean_ctor_set(v_reuseFailAlloc_2119_, 8, v_snapshotTasks_2103_);
v___x_2116_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_st_ref_put(v___y_2062_, v___x_2116_);
v___x_2118_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_2064_);
return v___x_2118_;
}
}
}
}
}
else
{
goto v___jp_2087_;
}
}
else
{
goto v___jp_2087_;
}
}
v___jp_2123_:
{
double v___x_2125_; double v___x_2126_; double v___x_2127_; uint8_t v___x_2128_; 
v___x_2125_ = lean_unbox_float(v_snd_2073_);
v___x_2126_ = lean_unbox_float(v_fst_2072_);
v___x_2127_ = lean_float_sub(v___x_2125_, v___x_2126_);
v___x_2128_ = lean_float_decLt(v___y_2124_, v___x_2127_);
v___y_2093_ = v___x_2128_;
goto v___jp_2092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___boxed(lean_object* v_cls_2139_, lean_object* v_collapsed_2140_, lean_object* v_tag_2141_, lean_object* v_opts_2142_, lean_object* v_clsEnabled_2143_, lean_object* v_oldTraces_2144_, lean_object* v_msg_2145_, lean_object* v_resStartStop_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
uint8_t v_collapsed_boxed_2154_; uint8_t v_clsEnabled_boxed_2155_; lean_object* v_res_2156_; 
v_collapsed_boxed_2154_ = lean_unbox(v_collapsed_2140_);
v_clsEnabled_boxed_2155_ = lean_unbox(v_clsEnabled_2143_);
v_res_2156_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v_cls_2139_, v_collapsed_boxed_2154_, v_tag_2141_, v_opts_2142_, v_clsEnabled_boxed_2155_, v_oldTraces_2144_, v_msg_2145_, v_resStartStop_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_opts_2142_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_){
_start:
{
lean_object* v_ks_2161_; lean_object* v_vs_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2186_; 
v_ks_2161_ = lean_ctor_get(v_x_2157_, 0);
v_vs_2162_ = lean_ctor_get(v_x_2157_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_x_2157_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2164_ = v_x_2157_;
v_isShared_2165_ = v_isSharedCheck_2186_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_vs_2162_);
lean_inc(v_ks_2161_);
lean_dec(v_x_2157_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2186_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_array_get_size(v_ks_2161_);
v___x_2167_ = lean_nat_dec_lt(v_x_2158_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
lean_dec(v_x_2158_);
v___x_2168_ = lean_array_push(v_ks_2161_, v_x_2159_);
v___x_2169_ = lean_array_push(v_vs_2162_, v_x_2160_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v___x_2169_);
lean_ctor_set(v___x_2164_, 0, v___x_2168_);
v___x_2171_ = v___x_2164_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
else
{
lean_object* v_k_x27_2173_; uint8_t v___x_2174_; 
v_k_x27_2173_ = lean_array_fget_borrowed(v_ks_2161_, v_x_2158_);
v___x_2174_ = l_Lean_instBEqMVarId_beq(v_x_2159_, v_k_x27_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2176_; 
if (v_isShared_2165_ == 0)
{
v___x_2176_ = v___x_2164_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_ks_2161_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_vs_2162_);
v___x_2176_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_unsigned_to_nat(1u);
v___x_2178_ = lean_nat_add(v_x_2158_, v___x_2177_);
lean_dec(v_x_2158_);
v_x_2157_ = v___x_2176_;
v_x_2158_ = v___x_2178_;
goto _start;
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2181_ = lean_array_fset(v_ks_2161_, v_x_2158_, v_x_2159_);
v___x_2182_ = lean_array_fset(v_vs_2162_, v_x_2158_, v_x_2160_);
lean_dec(v_x_2158_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v___x_2182_);
lean_ctor_set(v___x_2164_, 0, v___x_2181_);
v___x_2184_ = v___x_2164_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_n_2187_, lean_object* v_k_2188_, lean_object* v_v_2189_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_n_2187_, v___x_2190_, v_k_2188_, v_v_2189_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(lean_object* v_x_2193_, size_t v_x_2194_, size_t v_x_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_){
_start:
{
if (lean_obj_tag(v_x_2193_) == 0)
{
lean_object* v_es_2198_; size_t v___x_2199_; size_t v___x_2200_; lean_object* v_j_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v_es_2198_ = lean_ctor_get(v_x_2193_, 0);
v___x_2199_ = ((size_t)31ULL);
v___x_2200_ = lean_usize_land(v_x_2194_, v___x_2199_);
v_j_2201_ = lean_usize_to_nat(v___x_2200_);
v___x_2202_ = lean_array_get_size(v_es_2198_);
v___x_2203_ = lean_nat_dec_lt(v_j_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_dec(v_j_2201_);
lean_dec(v_x_2197_);
lean_dec(v_x_2196_);
return v_x_2193_;
}
else
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2242_; 
lean_inc_ref(v_es_2198_);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_x_2193_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v_x_2193_, 0);
lean_dec(v_unused_2243_);
v___x_2205_ = v_x_2193_;
v_isShared_2206_ = v_isSharedCheck_2242_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v_x_2193_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2242_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_v_2207_; lean_object* v___x_2208_; lean_object* v_xs_x27_2209_; lean_object* v___y_2211_; 
v_v_2207_ = lean_array_fget(v_es_2198_, v_j_2201_);
v___x_2208_ = lean_box(0);
v_xs_x27_2209_ = lean_array_fset(v_es_2198_, v_j_2201_, v___x_2208_);
switch(lean_obj_tag(v_v_2207_))
{
case 0:
{
lean_object* v_key_2216_; lean_object* v_val_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2227_; 
v_key_2216_ = lean_ctor_get(v_v_2207_, 0);
v_val_2217_ = lean_ctor_get(v_v_2207_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_v_2207_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2219_ = v_v_2207_;
v_isShared_2220_ = v_isSharedCheck_2227_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_val_2217_);
lean_inc(v_key_2216_);
lean_dec(v_v_2207_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2227_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
uint8_t v___x_2221_; 
v___x_2221_ = l_Lean_instBEqMVarId_beq(v_x_2196_, v_key_2216_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_del_object(v___x_2219_);
v___x_2222_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2216_, v_val_2217_, v_x_2196_, v_x_2197_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___y_2211_ = v___x_2223_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2225_; 
lean_dec(v_val_2217_);
lean_dec(v_key_2216_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v_x_2197_);
lean_ctor_set(v___x_2219_, 0, v_x_2196_);
v___x_2225_ = v___x_2219_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_x_2196_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_x_2197_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
v___y_2211_ = v___x_2225_;
goto v___jp_2210_;
}
}
}
}
case 1:
{
lean_object* v_node_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2240_; 
v_node_2228_ = lean_ctor_get(v_v_2207_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_v_2207_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2230_ = v_v_2207_;
v_isShared_2231_ = v_isSharedCheck_2240_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_node_2228_);
lean_dec(v_v_2207_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2240_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
size_t v___x_2232_; size_t v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2232_ = ((size_t)5ULL);
v___x_2233_ = lean_usize_shift_right(v_x_2194_, v___x_2232_);
v___x_2234_ = ((size_t)1ULL);
v___x_2235_ = lean_usize_add(v_x_2195_, v___x_2234_);
v___x_2236_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_node_2228_, v___x_2233_, v___x_2235_, v_x_2196_, v_x_2197_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2236_);
v___x_2238_ = v___x_2230_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
v___y_2211_ = v___x_2238_;
goto v___jp_2210_;
}
}
}
default: 
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_x_2196_);
lean_ctor_set(v___x_2241_, 1, v_x_2197_);
v___y_2211_ = v___x_2241_;
goto v___jp_2210_;
}
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_array_fset(v_xs_x27_2209_, v_j_2201_, v___y_2211_);
lean_dec(v_j_2201_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2212_);
v___x_2214_ = v___x_2205_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v_ks_2244_; lean_object* v_vs_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2265_; 
v_ks_2244_ = lean_ctor_get(v_x_2193_, 0);
v_vs_2245_ = lean_ctor_get(v_x_2193_, 1);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_x_2193_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2247_ = v_x_2193_;
v_isShared_2248_ = v_isSharedCheck_2265_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_vs_2245_);
lean_inc(v_ks_2244_);
lean_dec(v_x_2193_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2265_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_ks_2244_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_vs_2245_);
v___x_2250_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v_newNode_2251_; uint8_t v___y_2253_; size_t v___x_2259_; uint8_t v___x_2260_; 
v_newNode_2251_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v___x_2250_, v_x_2196_, v_x_2197_);
v___x_2259_ = ((size_t)7ULL);
v___x_2260_ = lean_usize_dec_le(v___x_2259_, v_x_2195_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2261_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2251_);
v___x_2262_ = lean_unsigned_to_nat(4u);
v___x_2263_ = lean_nat_dec_lt(v___x_2261_, v___x_2262_);
lean_dec(v___x_2261_);
v___y_2253_ = v___x_2263_;
goto v___jp_2252_;
}
else
{
v___y_2253_ = v___x_2260_;
goto v___jp_2252_;
}
v___jp_2252_:
{
if (v___y_2253_ == 0)
{
lean_object* v_ks_2254_; lean_object* v_vs_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_ks_2254_ = lean_ctor_get(v_newNode_2251_, 0);
lean_inc_ref(v_ks_2254_);
v_vs_2255_ = lean_ctor_get(v_newNode_2251_, 1);
lean_inc_ref(v_vs_2255_);
lean_dec_ref(v_newNode_2251_);
v___x_2256_ = lean_unsigned_to_nat(0u);
v___x_2257_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_2258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_x_2195_, v_ks_2254_, v_vs_2255_, v___x_2256_, v___x_2257_);
lean_dec_ref(v_vs_2255_);
lean_dec_ref(v_ks_2254_);
return v___x_2258_;
}
else
{
return v_newNode_2251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(size_t v_depth_2266_, lean_object* v_keys_2267_, lean_object* v_vals_2268_, lean_object* v_i_2269_, lean_object* v_entries_2270_){
_start:
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = lean_array_get_size(v_keys_2267_);
v___x_2272_ = lean_nat_dec_lt(v_i_2269_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec(v_i_2269_);
return v_entries_2270_;
}
else
{
lean_object* v_k_2273_; lean_object* v_v_2274_; uint64_t v___x_2275_; size_t v_h_2276_; size_t v___x_2277_; lean_object* v___x_2278_; size_t v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; size_t v_h_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_k_2273_ = lean_array_fget_borrowed(v_keys_2267_, v_i_2269_);
v_v_2274_ = lean_array_fget_borrowed(v_vals_2268_, v_i_2269_);
v___x_2275_ = l_Lean_instHashableMVarId_hash(v_k_2273_);
v_h_2276_ = lean_uint64_to_usize(v___x_2275_);
v___x_2277_ = ((size_t)5ULL);
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = ((size_t)1ULL);
v___x_2280_ = lean_usize_sub(v_depth_2266_, v___x_2279_);
v___x_2281_ = lean_usize_mul(v___x_2277_, v___x_2280_);
v_h_2282_ = lean_usize_shift_right(v_h_2276_, v___x_2281_);
v___x_2283_ = lean_nat_add(v_i_2269_, v___x_2278_);
lean_dec(v_i_2269_);
lean_inc(v_v_2274_);
lean_inc(v_k_2273_);
v___x_2284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_entries_2270_, v_h_2282_, v_depth_2266_, v_k_2273_, v_v_2274_);
v_i_2269_ = v___x_2283_;
v_entries_2270_ = v___x_2284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_depth_2286_, lean_object* v_keys_2287_, lean_object* v_vals_2288_, lean_object* v_i_2289_, lean_object* v_entries_2290_){
_start:
{
size_t v_depth_boxed_2291_; lean_object* v_res_2292_; 
v_depth_boxed_2291_ = lean_unbox_usize(v_depth_2286_);
lean_dec(v_depth_2286_);
v_res_2292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_boxed_2291_, v_keys_2287_, v_vals_2288_, v_i_2289_, v_entries_2290_);
lean_dec_ref(v_vals_2288_);
lean_dec_ref(v_keys_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
size_t v_x_18841__boxed_2298_; size_t v_x_18842__boxed_2299_; lean_object* v_res_2300_; 
v_x_18841__boxed_2298_ = lean_unbox_usize(v_x_2294_);
lean_dec(v_x_2294_);
v_x_18842__boxed_2299_ = lean_unbox_usize(v_x_2295_);
lean_dec(v_x_2295_);
v_res_2300_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2293_, v_x_18841__boxed_2298_, v_x_18842__boxed_2299_, v_x_2296_, v_x_2297_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(lean_object* v_x_2301_, lean_object* v_x_2302_, lean_object* v_x_2303_){
_start:
{
uint64_t v___x_2304_; size_t v___x_2305_; size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2304_ = l_Lean_instHashableMVarId_hash(v_x_2302_);
v___x_2305_ = lean_uint64_to_usize(v___x_2304_);
v___x_2306_ = ((size_t)1ULL);
v___x_2307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2301_, v___x_2305_, v___x_2306_, v_x_2302_, v_x_2303_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object* v_mvarId_2308_, lean_object* v_val_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v_mctx_2313_; lean_object* v_cache_2314_; lean_object* v_zetaDeltaFVarIds_2315_; lean_object* v_postponed_2316_; lean_object* v_diag_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2346_; 
v___x_2312_ = lean_st_ref_take(v___y_2310_);
v_mctx_2313_ = lean_ctor_get(v___x_2312_, 0);
v_cache_2314_ = lean_ctor_get(v___x_2312_, 1);
v_zetaDeltaFVarIds_2315_ = lean_ctor_get(v___x_2312_, 2);
v_postponed_2316_ = lean_ctor_get(v___x_2312_, 3);
v_diag_2317_ = lean_ctor_get(v___x_2312_, 4);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2319_ = v___x_2312_;
v_isShared_2320_ = v_isSharedCheck_2346_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_diag_2317_);
lean_inc(v_postponed_2316_);
lean_inc(v_zetaDeltaFVarIds_2315_);
lean_inc(v_cache_2314_);
lean_inc(v_mctx_2313_);
lean_dec(v___x_2312_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2346_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_depth_2321_; lean_object* v_levelAssignDepth_2322_; lean_object* v_lmvarCounter_2323_; lean_object* v_mvarCounter_2324_; lean_object* v_lDecls_2325_; lean_object* v_decls_2326_; lean_object* v_userNames_2327_; lean_object* v_lAssignment_2328_; lean_object* v_eAssignment_2329_; lean_object* v_dAssignment_2330_; lean_object* v_instanceTypedMVars_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2345_; 
v_depth_2321_ = lean_ctor_get(v_mctx_2313_, 0);
v_levelAssignDepth_2322_ = lean_ctor_get(v_mctx_2313_, 1);
v_lmvarCounter_2323_ = lean_ctor_get(v_mctx_2313_, 2);
v_mvarCounter_2324_ = lean_ctor_get(v_mctx_2313_, 3);
v_lDecls_2325_ = lean_ctor_get(v_mctx_2313_, 4);
v_decls_2326_ = lean_ctor_get(v_mctx_2313_, 5);
v_userNames_2327_ = lean_ctor_get(v_mctx_2313_, 6);
v_lAssignment_2328_ = lean_ctor_get(v_mctx_2313_, 7);
v_eAssignment_2329_ = lean_ctor_get(v_mctx_2313_, 8);
v_dAssignment_2330_ = lean_ctor_get(v_mctx_2313_, 9);
v_instanceTypedMVars_2331_ = lean_ctor_get(v_mctx_2313_, 10);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_mctx_2313_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2333_ = v_mctx_2313_;
v_isShared_2334_ = v_isSharedCheck_2345_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_instanceTypedMVars_2331_);
lean_inc(v_dAssignment_2330_);
lean_inc(v_eAssignment_2329_);
lean_inc(v_lAssignment_2328_);
lean_inc(v_userNames_2327_);
lean_inc(v_decls_2326_);
lean_inc(v_lDecls_2325_);
lean_inc(v_mvarCounter_2324_);
lean_inc(v_lmvarCounter_2323_);
lean_inc(v_levelAssignDepth_2322_);
lean_inc(v_depth_2321_);
lean_dec(v_mctx_2313_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2345_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2335_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_eAssignment_2329_, v_mvarId_2308_, v_val_2309_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 8, v___x_2335_);
v___x_2337_ = v___x_2333_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_depth_2321_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_levelAssignDepth_2322_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_lmvarCounter_2323_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_mvarCounter_2324_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v_lDecls_2325_);
lean_ctor_set(v_reuseFailAlloc_2344_, 5, v_decls_2326_);
lean_ctor_set(v_reuseFailAlloc_2344_, 6, v_userNames_2327_);
lean_ctor_set(v_reuseFailAlloc_2344_, 7, v_lAssignment_2328_);
lean_ctor_set(v_reuseFailAlloc_2344_, 8, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2344_, 9, v_dAssignment_2330_);
lean_ctor_set(v_reuseFailAlloc_2344_, 10, v_instanceTypedMVars_2331_);
v___x_2337_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2337_);
v___x_2339_ = v___x_2319_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_cache_2314_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_zetaDeltaFVarIds_2315_);
lean_ctor_set(v_reuseFailAlloc_2343_, 3, v_postponed_2316_);
lean_ctor_set(v_reuseFailAlloc_2343_, 4, v_diag_2317_);
v___x_2339_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_st_ref_put(v___y_2310_, v___x_2339_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg___boxed(lean_object* v_mvarId_2347_, lean_object* v_val_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2347_, v_val_2348_, v___y_2349_);
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
size_t v_x_19067__boxed_2389_; uint8_t v_res_2390_; lean_object* v_r_2391_; 
v_x_19067__boxed_2389_ = lean_unbox_usize(v_x_2387_);
lean_dec(v_x_2387_);
v_res_2390_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2386_, v_x_19067__boxed_2389_, v_x_2388_);
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
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v___x_2419_, v___y_2423_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2597_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2597_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2597_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_unbox(v_a_2428_);
lean_dec(v_a_2428_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
lean_del_object(v___x_2430_);
lean_inc(v___x_2419_);
v___x_2433_ = l_Lean_MVarId_getType(v___x_2419_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_options_2434_; uint8_t v_hasTrace_2435_; 
v_options_2434_ = lean_ctor_get(v___y_2424_, 2);
v_hasTrace_2435_ = lean_ctor_get_uint8(v_options_2434_, sizeof(void*)*1);
if (v_hasTrace_2435_ == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; 
v_a_2436_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2433_, 1);
v___x_2437_ = l_Lean_Meta_mkDefault(v_a_2436_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2439_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2419_, v_a_2438_, v___y_2423_);
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
lean_dec(v___x_2419_);
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
lean_object* v_a_2457_; lean_object* v_inheritedTraceOptions_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v_a_2467_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v_a_2482_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v_a_2487_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v_a_2498_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v_a_2510_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v_a_2515_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; 
v_a_2457_ = lean_ctor_get(v___x_2433_, 0);
lean_inc_n(v_a_2457_, 2);
lean_dec_ref_known(v___x_2433_, 1);
v_inheritedTraceOptions_2458_ = lean_ctor_get(v___y_2424_, 13);
v___f_2459_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2459_, 0, v_a_2457_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_2461_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_2462_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2463_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2458_, v_options_2434_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = l_Lean_trace_profiler;
v___x_2559_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2434_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
lean_dec_ref(v___f_2459_);
v___x_2560_ = l_Lean_Meta_mkDefault(v_a_2457_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2562_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc_n(v_a_2561_, 2);
lean_dec_ref_known(v___x_2560_, 1);
v___x_2562_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2419_, v_a_2561_, v___y_2423_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2575_; 
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v___x_2562_, 0);
lean_dec(v_unused_2576_);
v___x_2564_ = v___x_2562_;
v_isShared_2565_ = v_isSharedCheck_2575_;
goto v_resetjp_2563_;
}
else
{
lean_dec(v___x_2562_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2575_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
if (v___x_2463_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
lean_dec(v_a_2561_);
v___x_2566_ = lean_box(0);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2566_);
v___x_2568_ = v___x_2564_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
else
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_del_object(v___x_2564_);
v___x_2570_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2571_ = lean_unsigned_to_nat(30u);
v___x_2572_ = l_Lean_inlineExprTrailing(v_a_2561_, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2570_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2460_, v___x_2573_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2574_;
}
}
}
else
{
lean_dec(v_a_2561_);
return v___x_2562_;
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v___x_2419_);
v_a_2577_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2560_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2560_);
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
goto v___jp_2523_;
}
}
else
{
goto v___jp_2523_;
}
v___jp_2464_:
{
lean_object* v___x_2468_; double v___x_2469_; double v___x_2470_; double v___x_2471_; double v___x_2472_; double v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2468_ = lean_io_mono_nanos_now();
v___x_2469_ = lean_float_of_nat(v___y_2465_);
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
v___x_2478_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2460_, v_hasTrace_2435_, v___x_2461_, v_options_2434_, v___x_2463_, v___y_2466_, v___f_2459_, v___x_2477_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
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
if (lean_obj_tag(v___y_2492_) == 0)
{
lean_object* v_a_2493_; 
v_a_2493_ = lean_ctor_get(v___y_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___y_2492_, 1);
v___y_2485_ = v___y_2490_;
v___y_2486_ = v___y_2491_;
v_a_2487_ = v_a_2493_;
goto v___jp_2484_;
}
else
{
lean_object* v_a_2494_; 
v_a_2494_ = lean_ctor_get(v___y_2492_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___y_2492_, 1);
v___y_2480_ = v___y_2490_;
v___y_2481_ = v___y_2491_;
v_a_2482_ = v_a_2494_;
goto v___jp_2479_;
}
}
v___jp_2495_:
{
lean_object* v___x_2499_; double v___x_2500_; double v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2499_ = lean_io_get_num_heartbeats();
v___x_2500_ = lean_float_of_nat(v___y_2496_);
v___x_2501_ = lean_float_of_nat(v___x_2499_);
v___x_2502_ = lean_box_float(v___x_2500_);
v___x_2503_ = lean_box_float(v___x_2501_);
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v_a_2498_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2460_, v_hasTrace_2435_, v___x_2461_, v_options_2434_, v___x_2463_, v___y_2497_, v___f_2459_, v___x_2505_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2506_;
}
v___jp_2507_:
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_a_2510_);
v___y_2496_ = v___y_2508_;
v___y_2497_ = v___y_2509_;
v_a_2498_ = v___x_2511_;
goto v___jp_2495_;
}
v___jp_2512_:
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2515_);
v___y_2496_ = v___y_2513_;
v___y_2497_ = v___y_2514_;
v_a_2498_ = v___x_2516_;
goto v___jp_2495_;
}
v___jp_2517_:
{
if (lean_obj_tag(v___y_2520_) == 0)
{
lean_object* v_a_2521_; 
v_a_2521_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___y_2520_, 1);
v___y_2513_ = v___y_2518_;
v___y_2514_ = v___y_2519_;
v_a_2515_ = v_a_2521_;
goto v___jp_2512_;
}
else
{
lean_object* v_a_2522_; 
v_a_2522_ = lean_ctor_get(v___y_2520_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___y_2520_, 1);
v___y_2508_ = v___y_2518_;
v___y_2509_ = v___y_2519_;
v_a_2510_ = v_a_2522_;
goto v___jp_2507_;
}
}
v___jp_2523_:
{
lean_object* v___x_2524_; 
v___x_2524_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_2425_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2526_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2527_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2434_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_io_mono_nanos_now();
v___x_2529_ = l_Lean_Meta_mkDefault(v_a_2457_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc_n(v_a_2530_, 2);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2419_, v_a_2530_, v___y_2423_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_dec_ref_known(v___x_2531_, 1);
if (v___x_2463_ == 0)
{
lean_object* v___x_2532_; 
lean_dec(v_a_2530_);
v___x_2532_ = lean_box(0);
v___y_2485_ = v___x_2528_;
v___y_2486_ = v_a_2525_;
v_a_2487_ = v___x_2532_;
goto v___jp_2484_;
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
v___x_2537_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2460_, v___x_2536_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
v___y_2490_ = v___x_2528_;
v___y_2491_ = v_a_2525_;
v___y_2492_ = v___x_2537_;
goto v___jp_2489_;
}
}
else
{
lean_dec(v_a_2530_);
v___y_2490_ = v___x_2528_;
v___y_2491_ = v_a_2525_;
v___y_2492_ = v___x_2531_;
goto v___jp_2489_;
}
}
else
{
lean_object* v_a_2538_; 
lean_dec(v___x_2419_);
v_a_2538_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2529_, 1);
v___y_2480_ = v___x_2528_;
v___y_2481_ = v_a_2525_;
v_a_2482_ = v_a_2538_;
goto v___jp_2479_;
}
}
else
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_io_get_num_heartbeats();
v___x_2540_ = l_Lean_Meta_mkDefault(v_a_2457_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2542_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc_n(v_a_2541_, 2);
lean_dec_ref_known(v___x_2540_, 1);
v___x_2542_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2419_, v_a_2541_, v___y_2423_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_dec_ref_known(v___x_2542_, 1);
if (v___x_2463_ == 0)
{
lean_object* v___x_2543_; 
lean_dec(v_a_2541_);
v___x_2543_ = lean_box(0);
v___y_2513_ = v___x_2539_;
v___y_2514_ = v_a_2525_;
v_a_2515_ = v___x_2543_;
goto v___jp_2512_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2544_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2545_ = lean_unsigned_to_nat(30u);
v___x_2546_ = l_Lean_inlineExprTrailing(v_a_2541_, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2544_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2460_, v___x_2547_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
v___y_2518_ = v___x_2539_;
v___y_2519_ = v_a_2525_;
v___y_2520_ = v___x_2548_;
goto v___jp_2517_;
}
}
else
{
lean_dec(v_a_2541_);
v___y_2518_ = v___x_2539_;
v___y_2519_ = v_a_2525_;
v___y_2520_ = v___x_2542_;
goto v___jp_2517_;
}
}
else
{
lean_object* v_a_2549_; 
lean_dec(v___x_2419_);
v_a_2549_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2540_, 1);
v___y_2508_ = v___x_2539_;
v___y_2509_ = v_a_2525_;
v_a_2510_ = v_a_2549_;
goto v___jp_2507_;
}
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec_ref(v___f_2459_);
lean_dec(v_a_2457_);
lean_dec(v___x_2419_);
v_a_2550_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2524_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2524_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v___x_2419_);
v_a_2585_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2433_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2433_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v___x_2419_);
v___x_2593_ = lean_box(0);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2593_);
v___x_2595_ = v___x_2430_;
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
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v___x_2419_);
v_a_2598_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2427_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2427_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object* v___x_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object* v_as_2615_, size_t v_i_2616_, size_t v_stop_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v___x_2626_; 
v___x_2626_ = lean_usize_dec_eq(v_i_2616_, v_stop_2617_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_array_uget_borrowed(v_as_2615_, v_i_2616_);
lean_inc_n(v___x_2627_, 2);
v___f_2628_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed), 8, 1);
lean_closure_set(v___f_2628_, 0, v___x_2627_);
v___x_2629_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v___x_2627_, v___f_2628_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; size_t v___x_2631_; size_t v___x_2632_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = ((size_t)1ULL);
v___x_2632_ = lean_usize_add(v_i_2616_, v___x_2631_);
v_i_2616_ = v___x_2632_;
v_b_2618_ = v_a_2630_;
goto _start;
}
else
{
return v___x_2629_;
}
}
else
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_b_2618_);
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object* v_as_2635_, lean_object* v_i_2636_, lean_object* v_stop_2637_, lean_object* v_b_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
size_t v_i_boxed_2646_; size_t v_stop_boxed_2647_; lean_object* v_res_2648_; 
v_i_boxed_2646_ = lean_unbox_usize(v_i_2636_);
lean_dec(v_i_2636_);
v_stop_boxed_2647_ = lean_unbox_usize(v_stop_2637_);
lean_dec(v_stop_2637_);
v_res_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2635_, v_i_boxed_2646_, v_stop_boxed_2647_, v_b_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec_ref(v_as_2635_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object* v_e_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Meta_getMVarsNoDelayed(v_e_2649_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2679_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_array_get_size(v_a_2658_);
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_nat_dec_lt(v___x_2662_, v___x_2663_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2667_; 
lean_dec(v_a_2658_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2664_);
v___x_2667_ = v___x_2660_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2664_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
else
{
uint8_t v___x_2669_; 
v___x_2669_ = lean_nat_dec_le(v___x_2663_, v___x_2663_);
if (v___x_2669_ == 0)
{
if (v___x_2665_ == 0)
{
lean_object* v___x_2671_; 
lean_dec(v_a_2658_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2664_);
v___x_2671_ = v___x_2660_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2664_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
else
{
size_t v___x_2673_; size_t v___x_2674_; lean_object* v___x_2675_; 
lean_del_object(v___x_2660_);
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = lean_usize_of_nat(v___x_2663_);
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2658_, v___x_2673_, v___x_2674_, v___x_2664_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2658_);
return v___x_2675_;
}
}
else
{
size_t v___x_2676_; size_t v___x_2677_; lean_object* v___x_2678_; 
lean_del_object(v___x_2660_);
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = lean_usize_of_nat(v___x_2663_);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2658_, v___x_2676_, v___x_2677_, v___x_2664_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2658_);
return v___x_2678_;
}
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_a_2680_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2657_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2657_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object* v_e_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object* v_mvarId_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2697_, v___y_2701_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object* v_mvarId_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_mvarId_2706_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object* v_mvarId_2715_, lean_object* v_val_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2715_, v_val_2716_, v___y_2720_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object* v_mvarId_2725_, lean_object* v_val_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v_mvarId_2725_, v_val_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object* v_00_u03b1_2735_, lean_object* v_x_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_2736_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_x_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(v_00_u03b1_2745_, v_x_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
return v_res_2754_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object* v_00_u03b2_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
uint8_t v___x_2758_; 
v___x_2758_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2756_, v_x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2759_, lean_object* v_x_2760_, lean_object* v_x_2761_){
_start:
{
uint8_t v_res_2762_; lean_object* v_r_2763_; 
v_res_2762_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(v_00_u03b2_2759_, v_x_2760_, v_x_2761_);
lean_dec(v_x_2761_);
lean_dec_ref(v_x_2760_);
v_r_2763_ = lean_box(v_res_2762_);
return v_r_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object* v_00_u03b2_2764_, lean_object* v_x_2765_, lean_object* v_x_2766_, lean_object* v_x_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_x_2765_, v_x_2766_, v_x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object* v_oldTraces_2769_, lean_object* v_data_2770_, lean_object* v_ref_2771_, lean_object* v_msg_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2769_, v_data_2770_, v_ref_2771_, v_msg_2772_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object* v_oldTraces_2781_, lean_object* v_data_2782_, lean_object* v_ref_2783_, lean_object* v_msg_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_oldTraces_2781_, v_data_2782_, v_ref_2783_, v_msg_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
return v_res_2792_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2793_, lean_object* v_x_2794_, size_t v_x_2795_, lean_object* v_x_2796_){
_start:
{
uint8_t v___x_2797_; 
v___x_2797_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2794_, v_x_2795_, v_x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_){
_start:
{
size_t v_x_19766__boxed_2802_; uint8_t v_res_2803_; lean_object* v_r_2804_; 
v_x_19766__boxed_2802_ = lean_unbox_usize(v_x_2800_);
lean_dec(v_x_2800_);
v_res_2803_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(v_00_u03b2_2798_, v_x_2799_, v_x_19766__boxed_2802_, v_x_2801_);
lean_dec(v_x_2801_);
lean_dec_ref(v_x_2799_);
v_r_2804_ = lean_box(v_res_2803_);
return v_r_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2805_, lean_object* v_x_2806_, size_t v_x_2807_, size_t v_x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2806_, v_x_2807_, v_x_2808_, v_x_2809_, v_x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_){
_start:
{
size_t v_x_19777__boxed_2818_; size_t v_x_19778__boxed_2819_; lean_object* v_res_2820_; 
v_x_19777__boxed_2818_ = lean_unbox_usize(v_x_2814_);
lean_dec(v_x_2814_);
v_x_19778__boxed_2819_ = lean_unbox_usize(v_x_2815_);
lean_dec(v_x_2815_);
v_res_2820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(v_00_u03b2_2812_, v_x_2813_, v_x_19777__boxed_2818_, v_x_19778__boxed_2819_, v_x_2816_, v_x_2817_);
return v_res_2820_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_2821_, lean_object* v_keys_2822_, lean_object* v_vals_2823_, lean_object* v_heq_2824_, lean_object* v_i_2825_, lean_object* v_k_2826_){
_start:
{
uint8_t v___x_2827_; 
v___x_2827_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2822_, v_i_2825_, v_k_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_2828_, lean_object* v_keys_2829_, lean_object* v_vals_2830_, lean_object* v_heq_2831_, lean_object* v_i_2832_, lean_object* v_k_2833_){
_start:
{
uint8_t v_res_2834_; lean_object* v_r_2835_; 
v_res_2834_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2828_, v_keys_2829_, v_vals_2830_, v_heq_2831_, v_i_2832_, v_k_2833_);
lean_dec(v_k_2833_);
lean_dec_ref(v_vals_2830_);
lean_dec_ref(v_keys_2829_);
v_r_2835_ = lean_box(v_res_2834_);
return v_r_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_2836_, lean_object* v_n_2837_, lean_object* v_k_2838_, lean_object* v_v_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v_n_2837_, v_k_2838_, v_v_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b2_2841_, size_t v_depth_2842_, lean_object* v_keys_2843_, lean_object* v_vals_2844_, lean_object* v_heq_2845_, lean_object* v_i_2846_, lean_object* v_entries_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_2842_, v_keys_2843_, v_vals_2844_, v_i_2846_, v_entries_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b2_2849_, lean_object* v_depth_2850_, lean_object* v_keys_2851_, lean_object* v_vals_2852_, lean_object* v_heq_2853_, lean_object* v_i_2854_, lean_object* v_entries_2855_){
_start:
{
size_t v_depth_boxed_2856_; lean_object* v_res_2857_; 
v_depth_boxed_2856_ = lean_unbox_usize(v_depth_2850_);
lean_dec(v_depth_2850_);
v_res_2857_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(v_00_u03b2_2849_, v_depth_boxed_2856_, v_keys_2851_, v_vals_2852_, v_heq_2853_, v_i_2854_, v_entries_2855_);
lean_dec_ref(v_vals_2852_);
lean_dec_ref(v_keys_2851_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_2858_, lean_object* v_x_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_, lean_object* v_x_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_x_2859_, v_x_2860_, v_x_2861_, v_x_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object* v_e_2864_, lean_object* v___y_2865_){
_start:
{
uint8_t v___x_2867_; 
v___x_2867_ = l_Lean_Expr_hasMVar(v_e_2864_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; 
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v_e_2864_);
return v___x_2868_;
}
else
{
lean_object* v___x_2869_; lean_object* v_mctx_2870_; lean_object* v___x_2871_; lean_object* v_fst_2872_; lean_object* v_snd_2873_; lean_object* v___x_2874_; lean_object* v_cache_2875_; lean_object* v_zetaDeltaFVarIds_2876_; lean_object* v_postponed_2877_; lean_object* v_diag_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2887_; 
v___x_2869_ = lean_st_ref_get(v___y_2865_);
v_mctx_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc_ref(v_mctx_2870_);
lean_dec(v___x_2869_);
v___x_2871_ = l_Lean_instantiateMVarsCore(v_mctx_2870_, v_e_2864_);
v_fst_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_fst_2872_);
v_snd_2873_ = lean_ctor_get(v___x_2871_, 1);
lean_inc(v_snd_2873_);
lean_dec_ref(v___x_2871_);
v___x_2874_ = lean_st_ref_take(v___y_2865_);
v_cache_2875_ = lean_ctor_get(v___x_2874_, 1);
v_zetaDeltaFVarIds_2876_ = lean_ctor_get(v___x_2874_, 2);
v_postponed_2877_ = lean_ctor_get(v___x_2874_, 3);
v_diag_2878_ = lean_ctor_get(v___x_2874_, 4);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2874_, 0);
lean_dec(v_unused_2888_);
v___x_2880_ = v___x_2874_;
v_isShared_2881_ = v_isSharedCheck_2887_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_diag_2878_);
lean_inc(v_postponed_2877_);
lean_inc(v_zetaDeltaFVarIds_2876_);
lean_inc(v_cache_2875_);
lean_dec(v___x_2874_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2887_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v_snd_2873_);
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_snd_2873_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_cache_2875_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_zetaDeltaFVarIds_2876_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v_postponed_2877_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_diag_2878_);
v___x_2883_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_st_ref_put(v___y_2865_, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_fst_2872_);
return v___x_2885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object* v_e_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2889_, v___y_2890_);
lean_dec(v___y_2890_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object* v_e_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2893_, v___y_2897_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object* v_e_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
return v_res_2910_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object* v_msg_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_24913__overap_2921_; lean_object* v___x_2922_; 
v___x_2920_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_24913__overap_2921_ = lean_panic_fn_borrowed(v___x_2920_, v_msg_2912_);
lean_inc(v___y_2918_);
lean_inc_ref(v___y_2917_);
lean_inc(v___y_2916_);
lean_inc_ref(v___y_2915_);
lean_inc(v___y_2914_);
lean_inc_ref(v___y_2913_);
v___x_2922_ = lean_apply_7(v___x_24913__overap_2921_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, lean_box(0));
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object* v_msg_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(lean_object* v_a_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg___boxed(lean_object* v_a_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(v_a_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object* v_00_u03b1_2950_, lean_object* v_a_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object* v_00_u03b1_2960_, lean_object* v_a_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v_00_u03b1_2960_, v_a_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(lean_object* v_k_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v_b_2973_, lean_object* v_c_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___x_2980_; 
lean_inc(v___y_2978_);
lean_inc_ref(v___y_2977_);
lean_inc(v___y_2976_);
lean_inc_ref(v___y_2975_);
lean_inc(v___y_2972_);
lean_inc_ref(v___y_2971_);
v___x_2980_ = lean_apply_9(v_k_2970_, v_b_2973_, v_c_2974_, v___y_2971_, v___y_2972_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, lean_box(0));
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed(lean_object* v_k_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v_b_2984_, lean_object* v_c_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(v_k_2981_, v___y_2982_, v___y_2983_, v_b_2984_, v_c_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object* v_type_2992_, lean_object* v_k_2993_, uint8_t v_cleanupAnnotations_2994_, uint8_t v_whnfType_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___f_3003_; lean_object* v___x_3004_; 
lean_inc(v___y_2997_);
lean_inc_ref(v___y_2996_);
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3003_, 0, v_k_2993_);
lean_closure_set(v___f_3003_, 1, v___y_2996_);
lean_closure_set(v___f_3003_, 2, v___y_2997_);
v___x_3004_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2992_, v___f_3003_, v_cleanupAnnotations_2994_, v_whnfType_2995_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3004_) == 0)
{
return v___x_3004_;
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object* v_type_3013_, lean_object* v_k_3014_, lean_object* v_cleanupAnnotations_3015_, lean_object* v_whnfType_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3024_; uint8_t v_whnfType_boxed_3025_; lean_object* v_res_3026_; 
v_cleanupAnnotations_boxed_3024_ = lean_unbox(v_cleanupAnnotations_3015_);
v_whnfType_boxed_3025_ = lean_unbox(v_whnfType_3016_);
v_res_3026_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3013_, v_k_3014_, v_cleanupAnnotations_boxed_3024_, v_whnfType_boxed_3025_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object* v_00_u03b1_3027_, lean_object* v_type_3028_, lean_object* v_k_3029_, uint8_t v_cleanupAnnotations_3030_, uint8_t v_whnfType_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3028_, v_k_3029_, v_cleanupAnnotations_3030_, v_whnfType_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_type_3041_, lean_object* v_k_3042_, lean_object* v_cleanupAnnotations_3043_, lean_object* v_whnfType_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3052_; uint8_t v_whnfType_boxed_3053_; lean_object* v_res_3054_; 
v_cleanupAnnotations_boxed_3052_ = lean_unbox(v_cleanupAnnotations_3043_);
v_whnfType_boxed_3053_ = lean_unbox(v_whnfType_3044_);
v_res_3054_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(v_00_u03b1_3040_, v_type_3041_, v_k_3042_, v_cleanupAnnotations_boxed_3052_, v_whnfType_boxed_3053_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
return v_res_3054_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0));
v___x_3057_ = l_Lean_stringToMessageData(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object* v_x_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1);
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object* v_x_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec_ref(v_x_3068_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object* v___x_3077_, lean_object* v_fst_3078_, lean_object* v_____r_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = l_Lean_mkAppN(v___x_3077_, v_fst_3078_);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object* v___x_3089_, lean_object* v_fst_3090_, lean_object* v_____r_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3089_, v_fst_3090_, v_____r_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v_fst_3090_);
return v_res_3099_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0));
v___x_3102_ = l_Lean_stringToMessageData(v___x_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object* v_ctorName_3103_, uint8_t v___x_3104_, lean_object* v_x_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3113_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1);
v___x_3114_ = l_Lean_MessageData_ofConstName(v_ctorName_3103_, v___x_3104_);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object* v_ctorName_3119_, lean_object* v___x_3120_, lean_object* v_x_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v___x_29794__boxed_3129_; lean_object* v_res_3130_; 
v___x_29794__boxed_3129_ = lean_unbox(v___x_3120_);
v_res_3130_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3119_, v___x_29794__boxed_3129_, v_x_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec_ref(v_x_3121_);
return v_res_3130_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object* v_e_3131_){
_start:
{
if (lean_obj_tag(v_e_3131_) == 0)
{
uint8_t v___x_3132_; 
v___x_3132_ = 2;
return v___x_3132_;
}
else
{
lean_object* v_a_3133_; uint8_t v___x_3134_; 
v_a_3133_ = lean_ctor_get(v_e_3131_, 0);
v___x_3134_ = l_Lean_Expr_hasSyntheticSorry(v_a_3133_);
if (v___x_3134_ == 0)
{
uint8_t v___x_3135_; 
v___x_3135_ = 0;
return v___x_3135_;
}
else
{
uint8_t v___x_3136_; 
v___x_3136_ = 1;
return v___x_3136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object* v_e_3137_){
_start:
{
uint8_t v_res_3138_; lean_object* v_r_3139_; 
v_res_3138_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_e_3137_);
lean_dec_ref(v_e_3137_);
v_r_3139_ = lean_box(v_res_3138_);
return v_r_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object* v_cls_3140_, uint8_t v_collapsed_3141_, lean_object* v_tag_3142_, lean_object* v_opts_3143_, uint8_t v_clsEnabled_3144_, lean_object* v_oldTraces_3145_, lean_object* v_msg_3146_, lean_object* v_resStartStop_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_fst_3155_; lean_object* v_snd_3156_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v_data_3160_; lean_object* v_fst_3171_; lean_object* v_snd_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; lean_object* v___y_3176_; lean_object* v_a_3177_; uint8_t v___y_3192_; double v___y_3223_; 
v_fst_3155_ = lean_ctor_get(v_resStartStop_3147_, 0);
lean_inc(v_fst_3155_);
v_snd_3156_ = lean_ctor_get(v_resStartStop_3147_, 1);
lean_inc(v_snd_3156_);
lean_dec_ref(v_resStartStop_3147_);
v_fst_3171_ = lean_ctor_get(v_snd_3156_, 0);
lean_inc(v_fst_3171_);
v_snd_3172_ = lean_ctor_get(v_snd_3156_, 1);
lean_inc(v_snd_3172_);
lean_dec(v_snd_3156_);
v___x_3173_ = l_Lean_trace_profiler;
v___x_3174_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3143_, v___x_3173_);
if (v___x_3174_ == 0)
{
v___y_3192_ = v___x_3174_;
goto v___jp_3191_;
}
else
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
v___x_3228_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3229_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3143_, v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; double v___x_3232_; double v___x_3233_; double v___x_3234_; 
v___x_3230_ = l_Lean_trace_profiler_threshold;
v___x_3231_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3143_, v___x_3230_);
v___x_3232_ = lean_float_of_nat(v___x_3231_);
v___x_3233_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_3234_ = lean_float_div(v___x_3232_, v___x_3233_);
v___y_3223_ = v___x_3234_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; double v___x_3237_; 
v___x_3235_ = l_Lean_trace_profiler_threshold;
v___x_3236_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3143_, v___x_3235_);
v___x_3237_ = lean_float_of_nat(v___x_3236_);
v___y_3223_ = v___x_3237_;
goto v___jp_3222_;
}
}
v___jp_3157_:
{
lean_object* v___x_3161_; 
lean_inc(v___y_3158_);
v___x_3161_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_3145_, v_data_3160_, v___y_3158_, v___y_3159_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v___x_3162_; 
lean_dec_ref_known(v___x_3161_, 1);
v___x_3162_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3155_);
return v___x_3162_;
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v_fst_3155_);
v_a_3163_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3161_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3161_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
v___jp_3175_:
{
uint8_t v_result_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; double v___x_3181_; lean_object* v_data_3182_; 
v_result_3178_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_fst_3155_);
v___x_3179_ = lean_box(v_result_3178_);
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
v___x_3181_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3142_);
lean_inc_ref(v___x_3180_);
lean_inc(v_cls_3140_);
v_data_3182_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3182_, 0, v_cls_3140_);
lean_ctor_set(v_data_3182_, 1, v___x_3180_);
lean_ctor_set(v_data_3182_, 2, v_tag_3142_);
lean_ctor_set_float(v_data_3182_, sizeof(void*)*3, v___x_3181_);
lean_ctor_set_float(v_data_3182_, sizeof(void*)*3 + 8, v___x_3181_);
lean_ctor_set_uint8(v_data_3182_, sizeof(void*)*3 + 16, v_collapsed_3141_);
if (v___x_3174_ == 0)
{
lean_dec_ref_known(v___x_3180_, 1);
lean_dec(v_snd_3172_);
lean_dec(v_fst_3171_);
lean_dec_ref(v_tag_3142_);
lean_dec(v_cls_3140_);
v___y_3158_ = v___y_3176_;
v___y_3159_ = v_a_3177_;
v_data_3160_ = v_data_3182_;
goto v___jp_3157_;
}
else
{
lean_object* v_data_3183_; double v___x_3184_; double v___x_3185_; 
lean_dec_ref_known(v_data_3182_, 3);
v_data_3183_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3183_, 0, v_cls_3140_);
lean_ctor_set(v_data_3183_, 1, v___x_3180_);
lean_ctor_set(v_data_3183_, 2, v_tag_3142_);
v___x_3184_ = lean_unbox_float(v_fst_3171_);
lean_dec(v_fst_3171_);
lean_ctor_set_float(v_data_3183_, sizeof(void*)*3, v___x_3184_);
v___x_3185_ = lean_unbox_float(v_snd_3172_);
lean_dec(v_snd_3172_);
lean_ctor_set_float(v_data_3183_, sizeof(void*)*3 + 8, v___x_3185_);
lean_ctor_set_uint8(v_data_3183_, sizeof(void*)*3 + 16, v_collapsed_3141_);
v___y_3158_ = v___y_3176_;
v___y_3159_ = v_a_3177_;
v_data_3160_ = v_data_3183_;
goto v___jp_3157_;
}
}
v___jp_3186_:
{
lean_object* v_ref_3187_; lean_object* v___x_3188_; 
v_ref_3187_ = lean_ctor_get(v___y_3152_, 5);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
lean_inc(v___y_3151_);
lean_inc_ref(v___y_3150_);
lean_inc(v___y_3149_);
lean_inc_ref(v___y_3148_);
lean_inc(v_fst_3155_);
v___x_3188_ = lean_apply_8(v_msg_3146_, v_fst_3155_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, lean_box(0));
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___y_3176_ = v_ref_3187_;
v_a_3177_ = v_a_3189_;
goto v___jp_3175_;
}
else
{
lean_object* v___x_3190_; 
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_3176_ = v_ref_3187_;
v_a_3177_ = v___x_3190_;
goto v___jp_3175_;
}
}
v___jp_3191_:
{
if (v_clsEnabled_3144_ == 0)
{
if (v___y_3192_ == 0)
{
lean_object* v___x_3193_; lean_object* v_traceState_3194_; lean_object* v_env_3195_; lean_object* v_nextMacroScope_3196_; lean_object* v_ngen_3197_; lean_object* v_auxDeclNGen_3198_; lean_object* v_cache_3199_; lean_object* v_messages_3200_; lean_object* v_infoState_3201_; lean_object* v_snapshotTasks_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v_snd_3172_);
lean_dec(v_fst_3171_);
lean_dec_ref(v_msg_3146_);
lean_dec_ref(v_tag_3142_);
lean_dec(v_cls_3140_);
v___x_3193_ = lean_st_ref_take(v___y_3153_);
v_traceState_3194_ = lean_ctor_get(v___x_3193_, 4);
v_env_3195_ = lean_ctor_get(v___x_3193_, 0);
v_nextMacroScope_3196_ = lean_ctor_get(v___x_3193_, 1);
v_ngen_3197_ = lean_ctor_get(v___x_3193_, 2);
v_auxDeclNGen_3198_ = lean_ctor_get(v___x_3193_, 3);
v_cache_3199_ = lean_ctor_get(v___x_3193_, 5);
v_messages_3200_ = lean_ctor_get(v___x_3193_, 6);
v_infoState_3201_ = lean_ctor_get(v___x_3193_, 7);
v_snapshotTasks_3202_ = lean_ctor_get(v___x_3193_, 8);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3204_ = v___x_3193_;
v_isShared_3205_ = v_isSharedCheck_3221_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snapshotTasks_3202_);
lean_inc(v_infoState_3201_);
lean_inc(v_messages_3200_);
lean_inc(v_cache_3199_);
lean_inc(v_traceState_3194_);
lean_inc(v_auxDeclNGen_3198_);
lean_inc(v_ngen_3197_);
lean_inc(v_nextMacroScope_3196_);
lean_inc(v_env_3195_);
lean_dec(v___x_3193_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3221_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
uint64_t v_tid_3206_; lean_object* v_traces_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3220_; 
v_tid_3206_ = lean_ctor_get_uint64(v_traceState_3194_, sizeof(void*)*1);
v_traces_3207_ = lean_ctor_get(v_traceState_3194_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_traceState_3194_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3209_ = v_traceState_3194_;
v_isShared_3210_ = v_isSharedCheck_3220_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_traces_3207_);
lean_dec(v_traceState_3194_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3220_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3211_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3145_, v_traces_3207_);
lean_dec_ref(v_traces_3207_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3211_);
v___x_3213_ = v___x_3209_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3211_);
lean_ctor_set_uint64(v_reuseFailAlloc_3219_, sizeof(void*)*1, v_tid_3206_);
v___x_3213_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3215_; 
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 4, v___x_3213_);
v___x_3215_ = v___x_3204_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_env_3195_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_nextMacroScope_3196_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_ngen_3197_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_auxDeclNGen_3198_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3218_, 5, v_cache_3199_);
lean_ctor_set(v_reuseFailAlloc_3218_, 6, v_messages_3200_);
lean_ctor_set(v_reuseFailAlloc_3218_, 7, v_infoState_3201_);
lean_ctor_set(v_reuseFailAlloc_3218_, 8, v_snapshotTasks_3202_);
v___x_3215_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_st_ref_put(v___y_3153_, v___x_3215_);
v___x_3217_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3155_);
return v___x_3217_;
}
}
}
}
}
else
{
goto v___jp_3186_;
}
}
else
{
goto v___jp_3186_;
}
}
v___jp_3222_:
{
double v___x_3224_; double v___x_3225_; double v___x_3226_; uint8_t v___x_3227_; 
v___x_3224_ = lean_unbox_float(v_snd_3172_);
v___x_3225_ = lean_unbox_float(v_fst_3171_);
v___x_3226_ = lean_float_sub(v___x_3224_, v___x_3225_);
v___x_3227_ = lean_float_decLt(v___y_3223_, v___x_3226_);
v___y_3192_ = v___x_3227_;
goto v___jp_3191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object* v_cls_3238_, lean_object* v_collapsed_3239_, lean_object* v_tag_3240_, lean_object* v_opts_3241_, lean_object* v_clsEnabled_3242_, lean_object* v_oldTraces_3243_, lean_object* v_msg_3244_, lean_object* v_resStartStop_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
uint8_t v_collapsed_boxed_3253_; uint8_t v_clsEnabled_boxed_3254_; lean_object* v_res_3255_; 
v_collapsed_boxed_3253_ = lean_unbox(v_collapsed_3239_);
v_clsEnabled_boxed_3254_ = lean_unbox(v_clsEnabled_3242_);
v_res_3255_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v_cls_3238_, v_collapsed_boxed_3253_, v_tag_3240_, v_opts_3241_, v_clsEnabled_boxed_3254_, v_oldTraces_3243_, v_msg_3244_, v_resStartStop_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v_opts_3241_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object* v___x_3256_, lean_object* v_as_3257_, size_t v_i_3258_, size_t v_stop_3259_, lean_object* v_b_3260_){
_start:
{
lean_object* v___y_3262_; uint8_t v___x_3266_; 
v___x_3266_ = lean_usize_dec_eq(v_i_3258_, v_stop_3259_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3267_ = lean_array_uget_borrowed(v_as_3257_, v_i_3258_);
v___x_3268_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v___x_3256_, v___x_3267_);
if (v___x_3268_ == 0)
{
v___y_3262_ = v_b_3260_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3269_; 
lean_inc(v___x_3267_);
v___x_3269_ = lean_array_push(v_b_3260_, v___x_3267_);
v___y_3262_ = v___x_3269_;
goto v___jp_3261_;
}
}
else
{
return v_b_3260_;
}
v___jp_3261_:
{
size_t v___x_3263_; size_t v___x_3264_; 
v___x_3263_ = ((size_t)1ULL);
v___x_3264_ = lean_usize_add(v_i_3258_, v___x_3263_);
v_i_3258_ = v___x_3264_;
v_b_3260_ = v___y_3262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object* v___x_3270_, lean_object* v_as_3271_, lean_object* v_i_3272_, lean_object* v_stop_3273_, lean_object* v_b_3274_){
_start:
{
size_t v_i_boxed_3275_; size_t v_stop_boxed_3276_; lean_object* v_res_3277_; 
v_i_boxed_3275_ = lean_unbox_usize(v_i_3272_);
lean_dec(v_i_3272_);
v_stop_boxed_3276_ = lean_unbox_usize(v_stop_3273_);
lean_dec(v_stop_3273_);
v_res_3277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v___x_3270_, v_as_3271_, v_i_boxed_3275_, v_stop_boxed_3276_, v_b_3274_);
lean_dec_ref(v_as_3271_);
lean_dec_ref(v___x_3270_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object* v_a_3278_, lean_object* v_a_3279_){
_start:
{
if (lean_obj_tag(v_a_3278_) == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = l_List_reverse___redArg(v_a_3279_);
return v___x_3280_;
}
else
{
lean_object* v_head_3281_; lean_object* v_tail_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3291_; 
v_head_3281_ = lean_ctor_get(v_a_3278_, 0);
v_tail_3282_ = lean_ctor_get(v_a_3278_, 1);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_a_3278_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3284_ = v_a_3278_;
v_isShared_3285_ = v_isSharedCheck_3291_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_tail_3282_);
lean_inc(v_head_3281_);
lean_dec(v_a_3278_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3291_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3286_ = l_Lean_MessageData_ofExpr(v_head_3281_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v_a_3279_);
lean_ctor_set(v___x_3284_, 0, v___x_3286_);
v___x_3288_ = v___x_3284_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_a_3279_);
v___x_3288_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
v_a_3278_ = v_tail_3282_;
v_a_3279_ = v___x_3288_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2));
v___x_3296_ = lean_unsigned_to_nat(6u);
v___x_3297_ = lean_unsigned_to_nat(108u);
v___x_3298_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1));
v___x_3299_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0));
v___x_3300_ = l_mkPanicMessageWithDecl(v___x_3299_, v___x_3298_, v___x_3297_, v___x_3296_, v___x_3295_);
return v___x_3300_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4));
v___x_3303_ = l_Lean_stringToMessageData(v___x_3302_);
return v___x_3303_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6));
v___x_3306_ = l_Lean_stringToMessageData(v___x_3305_);
return v___x_3306_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_unsigned_to_nat(16u);
v___x_3314_ = lean_mk_array(v___x_3313_, v___x_3312_);
return v___x_3314_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14));
v___x_3320_ = l_Lean_stringToMessageData(v___x_3319_);
return v___x_3320_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16));
v___x_3323_ = l_Lean_stringToMessageData(v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3331_, lean_object* v_us_3332_, lean_object* v_xs_3333_, lean_object* v___x_3334_, lean_object* v___x_3335_, lean_object* v_ctorName_3336_, lean_object* v___x_3337_, lean_object* v___f_3338_, lean_object* v_insts_3339_, lean_object* v_localInst2Index_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; lean_object* v_env_3349_; lean_object* v___x_3350_; lean_object* v_type_3351_; lean_object* v___y_3353_; lean_object* v___y_3354_; uint8_t v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; uint8_t v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v_val_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3520_; lean_object* v___y_3531_; uint8_t v___x_3541_; uint8_t v___x_3542_; 
v___x_3348_ = lean_st_ref_get(v___y_3346_);
v_env_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc_ref(v_env_3349_);
lean_dec(v___x_3348_);
lean_inc(v_us_3332_);
lean_inc(v_inductiveTypeName_3331_);
v___x_3350_ = l_Lean_Expr_const___override(v_inductiveTypeName_3331_, v_us_3332_);
v_type_3351_ = l_Lean_mkAppN(v___x_3350_, v_xs_3333_);
v___x_3541_ = l_Lean_isStructure(v_env_3349_, v_inductiveTypeName_3331_);
v___x_3542_ = 1;
if (v___x_3541_ == 0)
{
lean_object* v_options_3543_; lean_object* v_inheritedTraceOptions_3544_; uint8_t v_hasTrace_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_dec_ref(v___f_3338_);
v_options_3543_ = lean_ctor_get(v___y_3345_, 2);
v_inheritedTraceOptions_3544_ = lean_ctor_get(v___y_3345_, 13);
v_hasTrace_3545_ = lean_ctor_get_uint8(v_options_3543_, sizeof(void*)*1);
lean_inc(v_ctorName_3336_);
v___x_3546_ = l_Lean_Expr_const___override(v_ctorName_3336_, v_us_3332_);
v___x_3547_ = l_Lean_mkAppN(v___x_3546_, v___x_3337_);
if (v_hasTrace_3545_ == 0)
{
lean_object* v___x_3548_; 
lean_dec(v_ctorName_3336_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___x_3547_);
v___x_3548_ = lean_infer_type(v___x_3547_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; lean_object* v___x_3552_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3550_ = lean_box(0);
v___x_3551_ = 0;
v___x_3552_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3549_, v___x_3550_, v___x_3551_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v_snd_3554_; lean_object* v_fst_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3598_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
v_snd_3554_ = lean_ctor_get(v_a_3553_, 1);
v_fst_3555_ = lean_ctor_get(v_a_3553_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_a_3553_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3557_ = v_a_3553_;
v_isShared_3558_ = v_isSharedCheck_3598_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_snd_3554_);
lean_inc(v_fst_3555_);
lean_dec(v_a_3553_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3598_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v_snd_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3596_; 
v_snd_3559_ = lean_ctor_get(v_snd_3554_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_snd_3554_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; 
v_unused_3597_ = lean_ctor_get(v_snd_3554_, 0);
lean_dec(v_unused_3597_);
v___x_3561_ = v_snd_3554_;
v_isShared_3562_ = v_isSharedCheck_3596_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_snd_3559_);
lean_dec(v_snd_3554_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3596_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; 
lean_inc(v_snd_3559_);
lean_inc_ref(v_type_3351_);
v___x_3563_ = l_Lean_Meta_isExprDefEq(v_type_3351_, v_snd_3559_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; uint8_t v___x_3565_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v___x_3565_ = lean_unbox(v_a_3564_);
lean_dec(v_a_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
lean_dec(v_fst_3555_);
lean_dec_ref(v___x_3547_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v___x_3566_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3567_ = l_Lean_indentExpr(v_type_3351_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 7);
lean_ctor_set(v___x_3561_, 1, v___x_3567_);
lean_ctor_set(v___x_3561_, 0, v___x_3566_);
v___x_3569_ = v___x_3561_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3570_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 7);
lean_ctor_set(v___x_3557_, 1, v___x_3570_);
lean_ctor_set(v___x_3557_, 0, v___x_3569_);
v___x_3572_ = v___x_3557_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
v___x_3573_ = l_Lean_indentExpr(v_snd_3559_);
v___x_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3574_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_del_object(v___x_3561_);
lean_dec(v_snd_3559_);
lean_del_object(v___x_3557_);
v___x_3586_ = lean_box(0);
v___x_3587_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3547_, v_fst_3555_, v___x_3586_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v_fst_3555_);
v___y_3520_ = v___x_3587_;
goto v___jp_3519_;
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_del_object(v___x_3561_);
lean_dec(v_snd_3559_);
lean_del_object(v___x_3557_);
lean_dec(v_fst_3555_);
lean_dec_ref(v___x_3547_);
lean_dec_ref(v_type_3351_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v_a_3588_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3563_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3563_);
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
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref(v___x_3547_);
lean_dec_ref(v_type_3351_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v_a_3599_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3552_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3552_);
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
else
{
lean_dec_ref(v___x_3547_);
v___y_3520_ = v___x_3548_;
goto v___jp_3519_;
}
}
else
{
lean_object* v___x_3607_; lean_object* v___f_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v_a_3616_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v_a_3631_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v_a_3649_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v_a_3661_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; 
v___x_3607_ = lean_box(v___x_3541_);
v___f_3608_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed), 10, 2);
lean_closure_set(v___f_3608_, 0, v_ctorName_3336_);
lean_closure_set(v___f_3608_, 1, v___x_3607_);
v___x_3609_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3610_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3611_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3544_, v_options_3543_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3759_; uint8_t v___x_3760_; 
v___x_3759_ = l_Lean_trace_profiler;
v___x_3760_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3543_, v___x_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3761_; 
lean_dec_ref(v___f_3608_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___x_3547_);
v___x_3761_ = lean_infer_type(v___x_3547_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; lean_object* v___x_3765_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3761_, 1);
v___x_3763_ = lean_box(0);
v___x_3764_ = 0;
v___x_3765_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3762_, v___x_3763_, v___x_3764_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v_snd_3767_; lean_object* v_fst_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3811_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref_known(v___x_3765_, 1);
v_snd_3767_ = lean_ctor_get(v_a_3766_, 1);
v_fst_3768_ = lean_ctor_get(v_a_3766_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_a_3766_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3770_ = v_a_3766_;
v_isShared_3771_ = v_isSharedCheck_3811_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_snd_3767_);
lean_inc(v_fst_3768_);
lean_dec(v_a_3766_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3811_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v_snd_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3809_; 
v_snd_3772_ = lean_ctor_get(v_snd_3767_, 1);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_snd_3767_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v_snd_3767_, 0);
lean_dec(v_unused_3810_);
v___x_3774_ = v_snd_3767_;
v_isShared_3775_ = v_isSharedCheck_3809_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_snd_3772_);
lean_dec(v_snd_3767_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3809_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3776_; 
lean_inc(v_snd_3772_);
lean_inc_ref(v_type_3351_);
v___x_3776_ = l_Lean_Meta_isExprDefEq(v_type_3351_, v_snd_3772_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; uint8_t v___x_3778_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3776_, 1);
v___x_3778_ = lean_unbox(v_a_3777_);
lean_dec(v_a_3777_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_dec(v_fst_3768_);
lean_dec_ref(v___x_3547_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v___x_3779_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3780_ = l_Lean_indentExpr(v_type_3351_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set_tag(v___x_3774_, 7);
lean_ctor_set(v___x_3774_, 1, v___x_3780_);
lean_ctor_set(v___x_3774_, 0, v___x_3779_);
v___x_3782_ = v___x_3774_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3771_ == 0)
{
lean_ctor_set_tag(v___x_3770_, 7);
lean_ctor_set(v___x_3770_, 1, v___x_3783_);
lean_ctor_set(v___x_3770_, 0, v___x_3782_);
v___x_3785_ = v___x_3770_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
v___x_3786_ = l_Lean_indentExpr(v_snd_3772_);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3787_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
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
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_del_object(v___x_3774_);
lean_dec(v_snd_3772_);
lean_del_object(v___x_3770_);
v___x_3799_ = lean_box(0);
v___x_3800_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3547_, v_fst_3768_, v___x_3799_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v_fst_3768_);
v___y_3520_ = v___x_3800_;
goto v___jp_3519_;
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_del_object(v___x_3774_);
lean_dec(v_snd_3772_);
lean_del_object(v___x_3770_);
lean_dec(v_fst_3768_);
lean_dec_ref(v___x_3547_);
lean_dec_ref(v_type_3351_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v_a_3801_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3776_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3776_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
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
return v___x_3806_;
}
}
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v___x_3547_);
lean_dec_ref(v_type_3351_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v_a_3812_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3765_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3765_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_dec_ref(v___x_3547_);
v___y_3520_ = v___x_3761_;
goto v___jp_3519_;
}
}
else
{
goto v___jp_3676_;
}
}
else
{
goto v___jp_3676_;
}
v___jp_3613_:
{
lean_object* v___x_3617_; double v___x_3618_; double v___x_3619_; double v___x_3620_; double v___x_3621_; double v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3617_ = lean_io_mono_nanos_now();
v___x_3618_ = lean_float_of_nat(v___y_3615_);
v___x_3619_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3620_ = lean_float_div(v___x_3618_, v___x_3619_);
v___x_3621_ = lean_float_of_nat(v___x_3617_);
v___x_3622_ = lean_float_div(v___x_3621_, v___x_3619_);
v___x_3623_ = lean_box_float(v___x_3620_);
v___x_3624_ = lean_box_float(v___x_3622_);
v___x_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3623_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v_a_3616_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3609_, v___x_3542_, v___x_3610_, v_options_3543_, v___x_3612_, v___y_3614_, v___f_3608_, v___x_3626_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3520_ = v___x_3627_;
goto v___jp_3519_;
}
v___jp_3628_:
{
lean_object* v___x_3632_; 
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_a_3631_);
v___y_3614_ = v___y_3629_;
v___y_3615_ = v___y_3630_;
v_a_3616_ = v___x_3632_;
goto v___jp_3613_;
}
v___jp_3633_:
{
if (lean_obj_tag(v___y_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
v_a_3637_ = lean_ctor_get(v___y_3636_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___y_3636_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___y_3636_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___y_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 1);
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
v___y_3614_ = v___y_3634_;
v___y_3615_ = v___y_3635_;
v_a_3616_ = v___x_3642_;
goto v___jp_3613_;
}
}
}
else
{
lean_object* v_a_3645_; 
v_a_3645_ = lean_ctor_get(v___y_3636_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___y_3636_, 1);
v___y_3629_ = v___y_3634_;
v___y_3630_ = v___y_3635_;
v_a_3631_ = v_a_3645_;
goto v___jp_3628_;
}
}
v___jp_3646_:
{
lean_object* v___x_3650_; double v___x_3651_; double v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3650_ = lean_io_get_num_heartbeats();
v___x_3651_ = lean_float_of_nat(v___y_3648_);
v___x_3652_ = lean_float_of_nat(v___x_3650_);
v___x_3653_ = lean_box_float(v___x_3651_);
v___x_3654_ = lean_box_float(v___x_3652_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3656_, 0, v_a_3649_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3609_, v___x_3542_, v___x_3610_, v_options_3543_, v___x_3612_, v___y_3647_, v___f_3608_, v___x_3656_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3520_ = v___x_3657_;
goto v___jp_3519_;
}
v___jp_3658_:
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3662_, 0, v_a_3661_);
v___y_3647_ = v___y_3659_;
v___y_3648_ = v___y_3660_;
v_a_3649_ = v___x_3662_;
goto v___jp_3646_;
}
v___jp_3663_:
{
if (lean_obj_tag(v___y_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
v_a_3667_ = lean_ctor_get(v___y_3666_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___y_3666_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___y_3666_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___y_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set_tag(v___x_3669_, 1);
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
v___y_3647_ = v___y_3664_;
v___y_3648_ = v___y_3665_;
v_a_3649_ = v___x_3672_;
goto v___jp_3646_;
}
}
}
else
{
lean_object* v_a_3675_; 
v_a_3675_ = lean_ctor_get(v___y_3666_, 0);
lean_inc(v_a_3675_);
lean_dec_ref_known(v___y_3666_, 1);
v___y_3659_ = v___y_3664_;
v___y_3660_ = v___y_3665_;
v_a_3661_ = v_a_3675_;
goto v___jp_3658_;
}
}
v___jp_3676_:
{
lean_object* v___x_3677_; lean_object* v_a_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3677_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3346_);
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3677_);
v___x_3679_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3680_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3543_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = lean_io_mono_nanos_now();
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___x_3547_);
v___x_3682_ = lean_infer_type(v___x_3547_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; lean_object* v___x_3686_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v___x_3684_ = lean_box(0);
v___x_3685_ = 0;
v___x_3686_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3683_, v___x_3684_, v___x_3685_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v_snd_3688_; lean_object* v_fst_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3718_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v_snd_3688_ = lean_ctor_get(v_a_3687_, 1);
v_fst_3689_ = lean_ctor_get(v_a_3687_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_a_3687_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3691_ = v_a_3687_;
v_isShared_3692_ = v_isSharedCheck_3718_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_snd_3688_);
lean_inc(v_fst_3689_);
lean_dec(v_a_3687_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3718_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_snd_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3716_; 
v_snd_3693_ = lean_ctor_get(v_snd_3688_, 1);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_snd_3688_);
if (v_isSharedCheck_3716_ == 0)
{
lean_object* v_unused_3717_; 
v_unused_3717_ = lean_ctor_get(v_snd_3688_, 0);
lean_dec(v_unused_3717_);
v___x_3695_ = v_snd_3688_;
v_isShared_3696_ = v_isSharedCheck_3716_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_snd_3693_);
lean_dec(v_snd_3688_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3716_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; 
lean_inc(v_snd_3693_);
lean_inc_ref(v_type_3351_);
v___x_3697_ = l_Lean_Meta_isExprDefEq(v_type_3351_, v_snd_3693_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
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
lean_dec_ref(v___x_3547_);
v___x_3700_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3351_);
v___x_3701_ = l_Lean_indentExpr(v_type_3351_);
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
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
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
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v_a_3710_; 
v___x_3707_ = l_Lean_indentExpr(v_snd_3693_);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3708_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref(v___x_3709_);
v___y_3629_ = v_a_3678_;
v___y_3630_ = v___x_3681_;
v_a_3631_ = v_a_3710_;
goto v___jp_3628_;
}
}
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_del_object(v___x_3695_);
lean_dec(v_snd_3693_);
lean_del_object(v___x_3691_);
v___x_3713_ = lean_box(0);
v___x_3714_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3547_, v_fst_3689_, v___x_3713_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v_fst_3689_);
v___y_3634_ = v_a_3678_;
v___y_3635_ = v___x_3681_;
v___y_3636_ = v___x_3714_;
goto v___jp_3633_;
}
}
else
{
lean_object* v_a_3715_; 
lean_del_object(v___x_3695_);
lean_dec(v_snd_3693_);
lean_del_object(v___x_3691_);
lean_dec(v_fst_3689_);
lean_dec_ref(v___x_3547_);
v_a_3715_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3715_);
lean_dec_ref_known(v___x_3697_, 1);
v___y_3629_ = v_a_3678_;
v___y_3630_ = v___x_3681_;
v_a_3631_ = v_a_3715_;
goto v___jp_3628_;
}
}
}
}
else
{
lean_object* v_a_3719_; 
lean_dec_ref(v___x_3547_);
v_a_3719_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3686_, 1);
v___y_3629_ = v_a_3678_;
v___y_3630_ = v___x_3681_;
v_a_3631_ = v_a_3719_;
goto v___jp_3628_;
}
}
else
{
lean_dec_ref(v___x_3547_);
v___y_3634_ = v_a_3678_;
v___y_3635_ = v___x_3681_;
v___y_3636_ = v___x_3682_;
goto v___jp_3633_;
}
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___x_3547_);
v___x_3721_ = lean_infer_type(v___x_3547_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; lean_object* v___x_3725_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v___x_3723_ = lean_box(0);
v___x_3724_ = 0;
v___x_3725_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3722_, v___x_3723_, v___x_3724_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v_snd_3727_; lean_object* v_fst_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3757_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
v_snd_3727_ = lean_ctor_get(v_a_3726_, 1);
v_fst_3728_ = lean_ctor_get(v_a_3726_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_a_3726_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3730_ = v_a_3726_;
v_isShared_3731_ = v_isSharedCheck_3757_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_snd_3727_);
lean_inc(v_fst_3728_);
lean_dec(v_a_3726_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3757_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v_snd_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3755_; 
v_snd_3732_ = lean_ctor_get(v_snd_3727_, 1);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_snd_3727_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v_snd_3727_, 0);
lean_dec(v_unused_3756_);
v___x_3734_ = v_snd_3727_;
v_isShared_3735_ = v_isSharedCheck_3755_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_snd_3732_);
lean_dec(v_snd_3727_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3755_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; 
lean_inc(v_snd_3732_);
lean_inc_ref(v_type_3351_);
v___x_3736_ = l_Lean_Meta_isExprDefEq(v_type_3351_, v_snd_3732_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; uint8_t v___x_3738_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3736_, 1);
v___x_3738_ = lean_unbox(v_a_3737_);
lean_dec(v_a_3737_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_dec(v_fst_3728_);
lean_dec_ref(v___x_3547_);
v___x_3739_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3351_);
v___x_3740_ = l_Lean_indentExpr(v_type_3351_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set_tag(v___x_3734_, 7);
lean_ctor_set(v___x_3734_, 1, v___x_3740_);
lean_ctor_set(v___x_3734_, 0, v___x_3739_);
v___x_3742_ = v___x_3734_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3745_; 
v___x_3743_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3731_ == 0)
{
lean_ctor_set_tag(v___x_3730_, 7);
lean_ctor_set(v___x_3730_, 1, v___x_3743_);
lean_ctor_set(v___x_3730_, 0, v___x_3742_);
v___x_3745_ = v___x_3730_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v_a_3749_; 
v___x_3746_ = l_Lean_indentExpr(v_snd_3732_);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3747_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref(v___x_3748_);
v___y_3659_ = v_a_3678_;
v___y_3660_ = v___x_3720_;
v_a_3661_ = v_a_3749_;
goto v___jp_3658_;
}
}
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_del_object(v___x_3734_);
lean_dec(v_snd_3732_);
lean_del_object(v___x_3730_);
v___x_3752_ = lean_box(0);
v___x_3753_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3547_, v_fst_3728_, v___x_3752_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v_fst_3728_);
v___y_3664_ = v_a_3678_;
v___y_3665_ = v___x_3720_;
v___y_3666_ = v___x_3753_;
goto v___jp_3663_;
}
}
else
{
lean_object* v_a_3754_; 
lean_del_object(v___x_3734_);
lean_dec(v_snd_3732_);
lean_del_object(v___x_3730_);
lean_dec(v_fst_3728_);
lean_dec_ref(v___x_3547_);
v_a_3754_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3736_, 1);
v___y_3659_ = v_a_3678_;
v___y_3660_ = v___x_3720_;
v_a_3661_ = v_a_3754_;
goto v___jp_3658_;
}
}
}
}
else
{
lean_object* v_a_3758_; 
lean_dec_ref(v___x_3547_);
v_a_3758_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3725_, 1);
v___y_3659_ = v_a_3678_;
v___y_3660_ = v___x_3720_;
v_a_3661_ = v_a_3758_;
goto v___jp_3658_;
}
}
else
{
lean_dec_ref(v___x_3547_);
v___y_3664_ = v_a_3678_;
v___y_3665_ = v___x_3720_;
v___y_3666_ = v___x_3721_;
goto v___jp_3663_;
}
}
}
}
}
else
{
lean_object* v_options_3820_; uint8_t v_hasTrace_3821_; 
lean_dec(v_ctorName_3336_);
lean_dec(v_us_3332_);
v_options_3820_ = lean_ctor_get(v___y_3345_, 2);
v_hasTrace_3821_ = lean_ctor_get_uint8(v_options_3820_, sizeof(void*)*1);
if (v_hasTrace_3821_ == 0)
{
lean_object* v_ref_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_dec_ref(v___f_3338_);
v_ref_3822_ = lean_ctor_get(v___y_3345_, 5);
v___x_3823_ = l_Lean_SourceInfo_fromRef(v_ref_3822_, v_hasTrace_3821_);
v___x_3824_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3825_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3823_);
v___x_3826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3823_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = l_Lean_Syntax_node1(v___x_3823_, v___x_3824_, v___x_3826_);
lean_inc_ref(v_type_3351_);
v___x_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_type_3351_);
v___x_3829_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3829_, 0, v___x_3827_);
lean_closure_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3829_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3531_ = v___x_3830_;
goto v___jp_3530_;
}
else
{
lean_object* v_ref_3831_; lean_object* v_inheritedTraceOptions_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v_a_3840_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v_a_3855_; 
v_ref_3831_ = lean_ctor_get(v___y_3345_, 5);
v_inheritedTraceOptions_3832_ = lean_ctor_get(v___y_3345_, 13);
v___x_3833_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3834_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3835_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3836_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3832_, v_options_3820_, v___x_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3928_; uint8_t v___x_3929_; 
v___x_3928_ = l_Lean_trace_profiler;
v___x_3929_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3820_, v___x_3928_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec_ref(v___f_3338_);
v___x_3930_ = l_Lean_SourceInfo_fromRef(v_ref_3831_, v___x_3929_);
v___x_3931_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3932_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3930_);
v___x_3933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3930_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3934_ = l_Lean_Syntax_node1(v___x_3930_, v___x_3931_, v___x_3933_);
lean_inc_ref(v_type_3351_);
v___x_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3935_, 0, v_type_3351_);
v___x_3936_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3936_, 0, v___x_3934_);
lean_closure_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3936_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3531_ = v___x_3937_;
goto v___jp_3530_;
}
else
{
goto v___jp_3864_;
}
}
else
{
goto v___jp_3864_;
}
v___jp_3837_:
{
lean_object* v___x_3841_; double v___x_3842_; double v___x_3843_; double v___x_3844_; double v___x_3845_; double v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3841_ = lean_io_mono_nanos_now();
v___x_3842_ = lean_float_of_nat(v___y_3839_);
v___x_3843_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3844_ = lean_float_div(v___x_3842_, v___x_3843_);
v___x_3845_ = lean_float_of_nat(v___x_3841_);
v___x_3846_ = lean_float_div(v___x_3845_, v___x_3843_);
v___x_3847_ = lean_box_float(v___x_3844_);
v___x_3848_ = lean_box_float(v___x_3846_);
v___x_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3847_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v_a_3840_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3833_, v___x_3542_, v___x_3834_, v_options_3820_, v___x_3836_, v___y_3838_, v___f_3338_, v___x_3850_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3531_ = v___x_3851_;
goto v___jp_3530_;
}
v___jp_3852_:
{
lean_object* v___x_3856_; double v___x_3857_; double v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3856_ = lean_io_get_num_heartbeats();
v___x_3857_ = lean_float_of_nat(v___y_3853_);
v___x_3858_ = lean_float_of_nat(v___x_3856_);
v___x_3859_ = lean_box_float(v___x_3857_);
v___x_3860_ = lean_box_float(v___x_3858_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3859_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v_a_3855_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___x_3863_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3833_, v___x_3542_, v___x_3834_, v_options_3820_, v___x_3836_, v___y_3854_, v___f_3338_, v___x_3862_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
v___y_3531_ = v___x_3863_;
goto v___jp_3530_;
}
v___jp_3864_:
{
lean_object* v___x_3865_; lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3927_; 
v___x_3865_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3346_);
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3927_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3927_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; uint8_t v___x_3871_; 
v___x_3870_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3871_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3820_, v___x_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3872_ = lean_io_mono_nanos_now();
v___x_3873_ = l_Lean_SourceInfo_fromRef(v_ref_3831_, v___x_3871_);
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3875_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3873_);
v___x_3876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3873_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
v___x_3877_ = l_Lean_Syntax_node1(v___x_3873_, v___x_3874_, v___x_3876_);
lean_inc_ref(v_type_3351_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 1);
lean_ctor_set(v___x_3868_, 0, v_type_3351_);
v___x_3879_ = v___x_3868_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_type_3351_);
v___x_3879_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3880_, 0, v___x_3877_);
lean_closure_set(v___x_3880_, 1, v___x_3879_);
v___x_3881_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3880_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 1);
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
v___y_3838_ = v_a_3866_;
v___y_3839_ = v___x_3872_;
v_a_3840_ = v___x_3887_;
goto v___jp_3837_;
}
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
v_a_3890_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3881_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3881_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
lean_ctor_set_tag(v___x_3892_, 0);
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
v___y_3838_ = v_a_3866_;
v___y_3839_ = v___x_3872_;
v_a_3840_ = v___x_3895_;
goto v___jp_3837_;
}
}
}
}
}
else
{
lean_object* v___x_3899_; uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3899_ = lean_io_get_num_heartbeats();
v___x_3900_ = 0;
v___x_3901_ = l_Lean_SourceInfo_fromRef(v_ref_3831_, v___x_3900_);
v___x_3902_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3903_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3901_);
v___x_3904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3901_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = l_Lean_Syntax_node1(v___x_3901_, v___x_3902_, v___x_3904_);
lean_inc_ref(v_type_3351_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 1);
lean_ctor_set(v___x_3868_, 0, v_type_3351_);
v___x_3907_ = v___x_3868_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_type_3351_);
v___x_3907_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3908_, 0, v___x_3905_);
lean_closure_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3908_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3909_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3909_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set_tag(v___x_3912_, 1);
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
v___y_3853_ = v___x_3899_;
v___y_3854_ = v_a_3866_;
v_a_3855_ = v___x_3915_;
goto v___jp_3852_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
v_a_3918_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3909_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3909_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set_tag(v___x_3920_, 0);
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
v___y_3853_ = v___x_3899_;
v___y_3854_ = v_a_3866_;
v_a_3855_ = v___x_3923_;
goto v___jp_3852_;
}
}
}
}
}
}
}
}
}
v___jp_3352_:
{
lean_object* v___x_3361_; uint8_t v___x_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; 
v___x_3361_ = l_Array_append___redArg(v_xs_3333_, v___y_3356_);
lean_dec_ref(v___y_3356_);
v___x_3362_ = 0;
v___x_3363_ = 1;
v___x_3364_ = l_Lean_Meta_mkForallFVars(v___x_3361_, v_type_3351_, v___x_3362_, v___y_3355_, v___y_3355_, v___x_3363_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___x_3366_ = l_Lean_Meta_mkLambdaFVars(v___x_3361_, v___y_3353_, v___x_3362_, v___y_3355_, v___x_3362_, v___y_3355_, v___x_3363_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec_ref(v___x_3361_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3376_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3376_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3376_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_a_3367_);
lean_ctor_set(v___x_3371_, 1, v___y_3354_);
v___x_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3372_, 0, v_a_3365_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3372_);
v___x_3374_ = v___x_3369_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v_a_3365_);
lean_dec(v___y_3354_);
v_a_3377_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3366_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3366_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v___x_3361_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
v_a_3385_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3364_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3364_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
v___jp_3393_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___y_3399_);
lean_ctor_set(v___x_3405_, 1, v___y_3404_);
lean_inc(v___y_3397_);
v___x_3406_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3397_, v___x_3405_, v___y_3394_, v___y_3400_, v___y_3396_, v___y_3401_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref_known(v___x_3406_, 1);
v___y_3353_ = v___y_3395_;
v___y_3354_ = v___y_3398_;
v___y_3355_ = v___y_3402_;
v___y_3356_ = v___y_3403_;
v___y_3357_ = v___y_3394_;
v___y_3358_ = v___y_3400_;
v___y_3359_ = v___y_3396_;
v___y_3360_ = v___y_3401_;
goto v___jp_3352_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v_type_3351_);
lean_dec_ref(v_xs_3333_);
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
v___jp_3415_:
{
uint8_t v___x_3427_; 
v___x_3427_ = lean_nat_dec_eq(v___y_3419_, v___y_3426_);
lean_dec(v___y_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3422_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v_type_3351_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v___x_3428_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3429_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3428_, v___y_3421_, v___y_3417_, v___y_3416_, v___y_3423_, v___y_3420_, v___y_3424_);
return v___x_3429_;
}
else
{
lean_object* v_options_3430_; uint8_t v_hasTrace_3431_; 
v_options_3430_ = lean_ctor_get(v___y_3420_, 2);
v_hasTrace_3431_ = lean_ctor_get_uint8(v_options_3430_, sizeof(void*)*1);
if (v_hasTrace_3431_ == 0)
{
lean_dec(v___y_3419_);
lean_dec(v___x_3334_);
v___y_3353_ = v___y_3418_;
v___y_3354_ = v___y_3422_;
v___y_3355_ = v___x_3427_;
v___y_3356_ = v___y_3425_;
v___y_3357_ = v___y_3416_;
v___y_3358_ = v___y_3423_;
v___y_3359_ = v___y_3420_;
v___y_3360_ = v___y_3424_;
goto v___jp_3352_;
}
else
{
lean_object* v_inheritedTraceOptions_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v_inheritedTraceOptions_3432_ = lean_ctor_get(v___y_3420_, 13);
v___x_3433_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3434_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3435_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3432_, v_options_3430_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_dec(v___y_3419_);
lean_dec(v___x_3334_);
v___y_3353_ = v___y_3418_;
v___y_3354_ = v___y_3422_;
v___y_3355_ = v___x_3427_;
v___y_3356_ = v___y_3425_;
v___y_3357_ = v___y_3416_;
v___y_3358_ = v___y_3423_;
v___y_3359_ = v___y_3420_;
v___y_3360_ = v___y_3424_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3436_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3437_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3418_);
v___x_3438_ = l_Lean_inlineExpr(v___y_3418_, v___x_3437_);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3436_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = lean_nat_dec_eq(v___y_3419_, v___x_3334_);
lean_dec(v___x_3334_);
lean_dec(v___y_3419_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3441_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3425_);
v___x_3442_ = lean_array_to_list(v___y_3425_);
v___x_3443_ = lean_box(0);
v___x_3444_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3442_, v___x_3443_);
v___x_3445_ = l_Lean_MessageData_ofList(v___x_3444_);
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3441_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___y_3394_ = v___y_3416_;
v___y_3395_ = v___y_3418_;
v___y_3396_ = v___y_3420_;
v___y_3397_ = v___x_3433_;
v___y_3398_ = v___y_3422_;
v___y_3399_ = v___x_3439_;
v___y_3400_ = v___y_3423_;
v___y_3401_ = v___y_3424_;
v___y_3402_ = v___x_3427_;
v___y_3403_ = v___y_3425_;
v___y_3404_ = v___x_3448_;
goto v___jp_3393_;
}
else
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3394_ = v___y_3416_;
v___y_3395_ = v___y_3418_;
v___y_3396_ = v___y_3420_;
v___y_3397_ = v___x_3433_;
v___y_3398_ = v___y_3422_;
v___y_3399_ = v___x_3439_;
v___y_3400_ = v___y_3423_;
v___y_3401_ = v___y_3424_;
v___y_3402_ = v___x_3427_;
v___y_3403_ = v___y_3425_;
v___y_3404_ = v___x_3449_;
goto v___jp_3393_;
}
}
}
}
}
v___jp_3450_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3459_ = lean_box(1);
lean_inc_ref(v___y_3453_);
v___x_3460_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3459_, v_localInst2Index_3340_, v___y_3453_);
v___x_3461_ = lean_array_get_size(v___y_3458_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_size_3462_; 
v_size_3462_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_size_3462_);
v___y_3416_ = v___y_3451_;
v___y_3417_ = v___y_3452_;
v___y_3418_ = v___y_3453_;
v___y_3419_ = v___x_3461_;
v___y_3420_ = v___y_3454_;
v___y_3421_ = v___y_3455_;
v___y_3422_ = v___x_3460_;
v___y_3423_ = v___y_3456_;
v___y_3424_ = v___y_3457_;
v___y_3425_ = v___y_3458_;
v___y_3426_ = v_size_3462_;
goto v___jp_3415_;
}
else
{
lean_inc(v___x_3334_);
v___y_3416_ = v___y_3451_;
v___y_3417_ = v___y_3452_;
v___y_3418_ = v___y_3453_;
v___y_3419_ = v___x_3461_;
v___y_3420_ = v___y_3454_;
v___y_3421_ = v___y_3455_;
v___y_3422_ = v___x_3460_;
v___y_3423_ = v___y_3456_;
v___y_3424_ = v___y_3457_;
v___y_3425_ = v___y_3458_;
v___y_3426_ = v___x_3334_;
goto v___jp_3415_;
}
}
v___jp_3463_:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3471_ = lean_array_get_size(v_insts_3339_);
v___x_3472_ = lean_mk_empty_array_with_capacity(v___x_3334_);
v___x_3473_ = lean_nat_dec_lt(v___x_3334_, v___x_3471_);
if (v___x_3473_ == 0)
{
lean_dec(v___x_3335_);
v___y_3451_ = v___y_3467_;
v___y_3452_ = v___y_3466_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3469_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3468_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___x_3472_;
goto v___jp_3450_;
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v_visitedExpr_3478_; uint8_t v___x_3479_; 
v___x_3474_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11);
lean_inc(v___x_3334_);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3334_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
lean_inc_ref(v___x_3472_);
v___x_3476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
lean_ctor_set(v___x_3476_, 1, v___x_3335_);
lean_ctor_set(v___x_3476_, 2, v___x_3472_);
lean_inc_ref(v___y_3464_);
v___x_3477_ = l_Lean_collectFVars(v___x_3476_, v___y_3464_);
v_visitedExpr_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc_ref(v_visitedExpr_3478_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = lean_nat_dec_le(v___x_3471_, v___x_3471_);
if (v___x_3479_ == 0)
{
if (v___x_3473_ == 0)
{
lean_dec_ref(v_visitedExpr_3478_);
v___y_3451_ = v___y_3467_;
v___y_3452_ = v___y_3466_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3469_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3468_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___x_3472_;
goto v___jp_3450_;
}
else
{
size_t v___x_3480_; size_t v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = ((size_t)0ULL);
v___x_3481_ = lean_usize_of_nat(v___x_3471_);
v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3478_, v_insts_3339_, v___x_3480_, v___x_3481_, v___x_3472_);
lean_dec_ref(v_visitedExpr_3478_);
v___y_3451_ = v___y_3467_;
v___y_3452_ = v___y_3466_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3469_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3468_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___x_3482_;
goto v___jp_3450_;
}
}
else
{
size_t v___x_3483_; size_t v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = ((size_t)0ULL);
v___x_3484_ = lean_usize_of_nat(v___x_3471_);
v___x_3485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3478_, v_insts_3339_, v___x_3483_, v___x_3484_, v___x_3472_);
lean_dec_ref(v_visitedExpr_3478_);
v___y_3451_ = v___y_3467_;
v___y_3452_ = v___y_3466_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3469_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3468_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___x_3485_;
goto v___jp_3450_;
}
}
}
v___jp_3486_:
{
lean_object* v___x_3494_; 
lean_inc_ref(v_val_3487_);
v___x_3494_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v___x_3495_; lean_object* v_a_3496_; uint8_t v___x_3497_; 
lean_dec_ref_known(v___x_3494_, 1);
v___x_3495_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3487_, v___y_3491_);
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref(v___x_3495_);
v___x_3497_ = l_Lean_Expr_hasMVar(v_a_3496_);
if (v___x_3497_ == 0)
{
v___y_3464_ = v_a_3496_;
v___y_3465_ = v___y_3488_;
v___y_3466_ = v___y_3489_;
v___y_3467_ = v___y_3490_;
v___y_3468_ = v___y_3491_;
v___y_3469_ = v___y_3492_;
v___y_3470_ = v___y_3493_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v_type_3351_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v___x_3498_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13);
v___x_3499_ = lean_unsigned_to_nat(30u);
v___x_3500_ = l_Lean_inlineExprTrailing(v_a_3496_, v___x_3499_);
v___x_3501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3498_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v___x_3502_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3501_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec_ref(v_val_3487_);
lean_dec_ref(v_type_3351_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v_a_3511_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3494_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3494_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
v___jp_3519_:
{
if (lean_obj_tag(v___y_3520_) == 0)
{
lean_object* v_a_3521_; 
v_a_3521_ = lean_ctor_get(v___y_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___y_3520_, 1);
v_val_3487_ = v_a_3521_;
v___y_3488_ = v___y_3341_;
v___y_3489_ = v___y_3342_;
v___y_3490_ = v___y_3343_;
v___y_3491_ = v___y_3344_;
v___y_3492_ = v___y_3345_;
v___y_3493_ = v___y_3346_;
goto v___jp_3486_;
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec_ref(v_type_3351_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v_a_3522_ = lean_ctor_get(v___y_3520_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___y_3520_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___y_3520_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___y_3520_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
v___jp_3530_:
{
if (lean_obj_tag(v___y_3531_) == 0)
{
lean_object* v_a_3532_; 
v_a_3532_ = lean_ctor_get(v___y_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___y_3531_, 1);
v_val_3487_ = v_a_3532_;
v___y_3488_ = v___y_3341_;
v___y_3489_ = v___y_3342_;
v___y_3490_ = v___y_3343_;
v___y_3491_ = v___y_3344_;
v___y_3492_ = v___y_3345_;
v___y_3493_ = v___y_3346_;
goto v___jp_3486_;
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v_type_3351_);
lean_dec(v_localInst2Index_3340_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec_ref(v_xs_3333_);
v_a_3533_ = lean_ctor_get(v___y_3531_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___y_3531_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___y_3531_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___y_3531_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object** _args){
lean_object* v_inductiveTypeName_3938_ = _args[0];
lean_object* v_us_3939_ = _args[1];
lean_object* v_xs_3940_ = _args[2];
lean_object* v___x_3941_ = _args[3];
lean_object* v___x_3942_ = _args[4];
lean_object* v_ctorName_3943_ = _args[5];
lean_object* v___x_3944_ = _args[6];
lean_object* v___f_3945_ = _args[7];
lean_object* v_insts_3946_ = _args[8];
lean_object* v_localInst2Index_3947_ = _args[9];
lean_object* v___y_3948_ = _args[10];
lean_object* v___y_3949_ = _args[11];
lean_object* v___y_3950_ = _args[12];
lean_object* v___y_3951_ = _args[13];
lean_object* v___y_3952_ = _args[14];
lean_object* v___y_3953_ = _args[15];
lean_object* v___y_3954_ = _args[16];
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_3938_, v_us_3939_, v_xs_3940_, v___x_3941_, v___x_3942_, v_ctorName_3943_, v___x_3944_, v___f_3945_, v_insts_3946_, v_localInst2Index_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec_ref(v_insts_3946_);
lean_dec_ref(v___x_3944_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t v_sz_3956_, size_t v_i_3957_, lean_object* v_bs_3958_){
_start:
{
uint8_t v___x_3959_; 
v___x_3959_ = lean_usize_dec_lt(v_i_3957_, v_sz_3956_);
if (v___x_3959_ == 0)
{
return v_bs_3958_;
}
else
{
lean_object* v_v_3960_; lean_object* v___x_3961_; lean_object* v_bs_x27_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; size_t v___x_3967_; size_t v___x_3968_; lean_object* v___x_3969_; 
v_v_3960_ = lean_array_uget(v_bs_3958_, v_i_3957_);
v___x_3961_ = lean_unsigned_to_nat(0u);
v_bs_x27_3962_ = lean_array_uset(v_bs_3958_, v_i_3957_, v___x_3961_);
v___x_3963_ = l_Lean_Expr_fvarId_x21(v_v_3960_);
lean_dec(v_v_3960_);
v___x_3964_ = 1;
v___x_3965_ = lean_box(v___x_3964_);
v___x_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3963_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
v___x_3967_ = ((size_t)1ULL);
v___x_3968_ = lean_usize_add(v_i_3957_, v___x_3967_);
v___x_3969_ = lean_array_uset(v_bs_x27_3962_, v_i_3957_, v___x_3966_);
v_i_3957_ = v___x_3968_;
v_bs_3958_ = v___x_3969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object* v_sz_3971_, lean_object* v_i_3972_, lean_object* v_bs_3973_){
_start:
{
size_t v_sz_boxed_3974_; size_t v_i_boxed_3975_; lean_object* v_res_3976_; 
v_sz_boxed_3974_ = lean_unbox_usize(v_sz_3971_);
lean_dec(v_sz_3971_);
v_i_boxed_3975_ = lean_unbox_usize(v_i_3972_);
lean_dec(v_i_3972_);
v_res_3976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_boxed_3974_, v_i_boxed_3975_, v_bs_3973_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object* v_k_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; 
lean_inc(v___y_3979_);
lean_inc_ref(v___y_3978_);
v___x_3985_ = lean_apply_7(v_k_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, lean_box(0));
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object* v_bs_3995_, lean_object* v_k_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v___f_4004_; lean_object* v___x_4005_; 
lean_inc(v___y_3998_);
lean_inc_ref(v___y_3997_);
v___f_4004_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4004_, 0, v_k_3996_);
lean_closure_set(v___f_4004_, 1, v___y_3997_);
lean_closure_set(v___f_4004_, 2, v___y_3998_);
v___x_4005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3995_, v___f_4004_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
if (lean_obj_tag(v___x_4005_) == 0)
{
return v___x_4005_;
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object* v_bs_4014_, lean_object* v_k_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4014_, v_k_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec_ref(v_bs_4014_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_bs_4024_, lean_object* v_k_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
size_t v_sz_4033_; size_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_sz_4033_ = lean_array_size(v_bs_4024_);
v___x_4034_ = ((size_t)0ULL);
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4033_, v___x_4034_, v_bs_4024_);
v___x_4036_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v___x_4035_, v_k_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec_ref(v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_bs_4037_, lean_object* v_k_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4037_, v_k_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4047_, lean_object* v_inductiveTypeName_4048_, lean_object* v_us_4049_, lean_object* v___x_4050_, lean_object* v_ctorName_4051_, lean_object* v___f_4052_, uint8_t v_addHypotheses_4053_, lean_object* v_xs_4054_, lean_object* v_x_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___f_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4063_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4054_, 2);
v___x_4064_ = l_Array_toSubarray___redArg(v_xs_4054_, v___x_4063_, v_numParams_4047_);
v___x_4065_ = l_Subarray_copy___redArg(v___x_4064_);
lean_inc_ref(v___x_4065_);
v___f_4066_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 17, 8);
lean_closure_set(v___f_4066_, 0, v_inductiveTypeName_4048_);
lean_closure_set(v___f_4066_, 1, v_us_4049_);
lean_closure_set(v___f_4066_, 2, v_xs_4054_);
lean_closure_set(v___f_4066_, 3, v___x_4063_);
lean_closure_set(v___f_4066_, 4, v___x_4050_);
lean_closure_set(v___f_4066_, 5, v_ctorName_4051_);
lean_closure_set(v___f_4066_, 6, v___x_4065_);
lean_closure_set(v___f_4066_, 7, v___f_4052_);
v___x_4067_ = lean_box(v_addHypotheses_4053_);
v___x_4068_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4068_, 0, v___x_4067_);
lean_closure_set(v___x_4068_, 1, lean_box(0));
lean_closure_set(v___x_4068_, 2, v___x_4065_);
lean_closure_set(v___x_4068_, 3, v___f_4066_);
v___x_4069_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_xs_4054_, v___x_4068_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4070_, lean_object* v_inductiveTypeName_4071_, lean_object* v_us_4072_, lean_object* v___x_4073_, lean_object* v_ctorName_4074_, lean_object* v___f_4075_, lean_object* v_addHypotheses_4076_, lean_object* v_xs_4077_, lean_object* v_x_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
uint8_t v_addHypotheses_boxed_4086_; lean_object* v_res_4087_; 
v_addHypotheses_boxed_4086_ = lean_unbox(v_addHypotheses_4076_);
v_res_4087_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4070_, v_inductiveTypeName_4071_, v_us_4072_, v___x_4073_, v_ctorName_4074_, v___f_4075_, v_addHypotheses_boxed_4086_, v_xs_4077_, v_x_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec_ref(v_x_4078_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4088_, lean_object* v_a_4089_){
_start:
{
if (lean_obj_tag(v_a_4088_) == 0)
{
lean_object* v___x_4090_; 
v___x_4090_ = l_List_reverse___redArg(v_a_4089_);
return v___x_4090_;
}
else
{
lean_object* v_head_4091_; lean_object* v_tail_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4101_; 
v_head_4091_ = lean_ctor_get(v_a_4088_, 0);
v_tail_4092_ = lean_ctor_get(v_a_4088_, 1);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_a_4088_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4094_ = v_a_4088_;
v_isShared_4095_ = v_isSharedCheck_4101_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_tail_4092_);
lean_inc(v_head_4091_);
lean_dec(v_a_4088_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4101_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4096_ = l_Lean_Level_param___override(v_head_4091_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v_a_4089_);
lean_ctor_set(v___x_4094_, 0, v___x_4096_);
v___x_4098_ = v___x_4094_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4096_);
lean_ctor_set(v_reuseFailAlloc_4100_, 1, v_a_4089_);
v___x_4098_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
v_a_4088_ = v_tail_4092_;
v_a_4089_ = v___x_4098_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4103_, lean_object* v_ctorName_4104_, uint8_t v_addHypotheses_4105_, lean_object* v_indVal_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v_toConstantVal_4114_; lean_object* v_numParams_4115_; lean_object* v_levelParams_4116_; lean_object* v_type_4117_; lean_object* v___f_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v_us_4121_; lean_object* v___x_4122_; lean_object* v___f_4123_; uint8_t v___x_4124_; lean_object* v___x_4125_; 
v_toConstantVal_4114_ = lean_ctor_get(v_indVal_4106_, 0);
lean_inc_ref(v_toConstantVal_4114_);
v_numParams_4115_ = lean_ctor_get(v_indVal_4106_, 1);
lean_inc(v_numParams_4115_);
lean_dec_ref(v_indVal_4106_);
v_levelParams_4116_ = lean_ctor_get(v_toConstantVal_4114_, 1);
lean_inc(v_levelParams_4116_);
v_type_4117_ = lean_ctor_get(v_toConstantVal_4114_, 2);
lean_inc_ref(v_type_4117_);
lean_dec_ref(v_toConstantVal_4114_);
v___f_4118_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4119_ = lean_box(1);
v___x_4120_ = lean_box(0);
v_us_4121_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4116_, v___x_4120_);
v___x_4122_ = lean_box(v_addHypotheses_4105_);
v___f_4123_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 16, 7);
lean_closure_set(v___f_4123_, 0, v_numParams_4115_);
lean_closure_set(v___f_4123_, 1, v_inductiveTypeName_4103_);
lean_closure_set(v___f_4123_, 2, v_us_4121_);
lean_closure_set(v___f_4123_, 3, v___x_4119_);
lean_closure_set(v___f_4123_, 4, v_ctorName_4104_);
lean_closure_set(v___f_4123_, 5, v___f_4118_);
lean_closure_set(v___f_4123_, 6, v___x_4122_);
v___x_4124_ = 0;
v___x_4125_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_4117_, v___f_4123_, v___x_4124_, v___x_4124_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4126_, lean_object* v_ctorName_4127_, lean_object* v_addHypotheses_4128_, lean_object* v_indVal_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
uint8_t v_addHypotheses_boxed_4137_; lean_object* v_res_4138_; 
v_addHypotheses_boxed_4137_ = lean_unbox(v_addHypotheses_4128_);
v_res_4138_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4126_, v_ctorName_4127_, v_addHypotheses_boxed_4137_, v_indVal_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec(v_a_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object* v_00_u03b1_4139_, lean_object* v_bs_4140_, lean_object* v_k_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4140_, v_k_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4150_, lean_object* v_bs_4151_, lean_object* v_k_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(v_00_u03b1_4150_, v_bs_4151_, v_k_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v_bs_4151_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_4161_, lean_object* v_bs_4162_, lean_object* v_k_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4162_, v_k_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_4172_, lean_object* v_bs_4173_, lean_object* v_k_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_4172_, v_bs_4173_, v_k_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4183_, lean_object* v_levelParams_4184_, lean_object* v_type_4185_, lean_object* v_value_4186_, lean_object* v_hints_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v___x_4190_; uint8_t v___y_4192_; uint8_t v___y_4199_; lean_object* v_env_4202_; uint8_t v___x_4203_; 
v___x_4190_ = lean_st_ref_get(v___y_4188_);
v_env_4202_ = lean_ctor_get(v___x_4190_, 0);
lean_inc_ref_n(v_env_4202_, 2);
lean_dec(v___x_4190_);
v___x_4203_ = l_Lean_Environment_hasUnsafe(v_env_4202_, v_type_4185_);
if (v___x_4203_ == 0)
{
uint8_t v___x_4204_; 
v___x_4204_ = l_Lean_Environment_hasUnsafe(v_env_4202_, v_value_4186_);
v___y_4199_ = v___x_4204_;
goto v___jp_4198_;
}
else
{
lean_dec_ref(v_env_4202_);
v___y_4199_ = v___x_4203_;
goto v___jp_4198_;
}
v___jp_4191_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
lean_inc(v_name_4183_);
v___x_4193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4193_, 0, v_name_4183_);
lean_ctor_set(v___x_4193_, 1, v_levelParams_4184_);
lean_ctor_set(v___x_4193_, 2, v_type_4185_);
v___x_4194_ = lean_box(0);
v___x_4195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4195_, 0, v_name_4183_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4196_, 0, v___x_4193_);
lean_ctor_set(v___x_4196_, 1, v_value_4186_);
lean_ctor_set(v___x_4196_, 2, v_hints_4187_);
lean_ctor_set(v___x_4196_, 3, v___x_4195_);
lean_ctor_set_uint8(v___x_4196_, sizeof(void*)*4, v___y_4192_);
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
v___jp_4198_:
{
if (v___y_4199_ == 0)
{
uint8_t v___x_4200_; 
v___x_4200_ = 1;
v___y_4192_ = v___x_4200_;
goto v___jp_4191_;
}
else
{
uint8_t v___x_4201_; 
v___x_4201_ = 0;
v___y_4192_ = v___x_4201_;
goto v___jp_4191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4205_, lean_object* v_levelParams_4206_, lean_object* v_type_4207_, lean_object* v_value_4208_, lean_object* v_hints_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4205_, v_levelParams_4206_, v_type_4207_, v_value_4208_, v_hints_4209_, v___y_4210_);
lean_dec(v___y_4210_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4213_, lean_object* v_levelParams_4214_, lean_object* v_type_4215_, lean_object* v_value_4216_, lean_object* v_hints_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4213_, v_levelParams_4214_, v_type_4215_, v_value_4216_, v_hints_4217_, v___y_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4226_, lean_object* v_levelParams_4227_, lean_object* v_type_4228_, lean_object* v_value_4229_, lean_object* v_hints_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4226_, v_levelParams_4227_, v_type_4228_, v_value_4229_, v_hints_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object* v___y_4239_, uint8_t v_isExporting_4240_, lean_object* v___x_4241_, lean_object* v___y_4242_, lean_object* v___x_4243_, lean_object* v_a_x3f_4244_){
_start:
{
lean_object* v___x_4246_; lean_object* v_env_4247_; lean_object* v_nextMacroScope_4248_; lean_object* v_ngen_4249_; lean_object* v_auxDeclNGen_4250_; lean_object* v_traceState_4251_; lean_object* v_messages_4252_; lean_object* v_infoState_4253_; lean_object* v_snapshotTasks_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4279_; 
v___x_4246_ = lean_st_ref_take(v___y_4239_);
v_env_4247_ = lean_ctor_get(v___x_4246_, 0);
v_nextMacroScope_4248_ = lean_ctor_get(v___x_4246_, 1);
v_ngen_4249_ = lean_ctor_get(v___x_4246_, 2);
v_auxDeclNGen_4250_ = lean_ctor_get(v___x_4246_, 3);
v_traceState_4251_ = lean_ctor_get(v___x_4246_, 4);
v_messages_4252_ = lean_ctor_get(v___x_4246_, 6);
v_infoState_4253_ = lean_ctor_get(v___x_4246_, 7);
v_snapshotTasks_4254_ = lean_ctor_get(v___x_4246_, 8);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4279_ == 0)
{
lean_object* v_unused_4280_; 
v_unused_4280_ = lean_ctor_get(v___x_4246_, 5);
lean_dec(v_unused_4280_);
v___x_4256_ = v___x_4246_;
v_isShared_4257_ = v_isSharedCheck_4279_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_snapshotTasks_4254_);
lean_inc(v_infoState_4253_);
lean_inc(v_messages_4252_);
lean_inc(v_traceState_4251_);
lean_inc(v_auxDeclNGen_4250_);
lean_inc(v_ngen_4249_);
lean_inc(v_nextMacroScope_4248_);
lean_inc(v_env_4247_);
lean_dec(v___x_4246_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4279_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4258_; lean_object* v___x_4260_; 
v___x_4258_ = l_Lean_Environment_setExporting(v_env_4247_, v_isExporting_4240_);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 5, v___x_4241_);
lean_ctor_set(v___x_4256_, 0, v___x_4258_);
v___x_4260_ = v___x_4256_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4258_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v_nextMacroScope_4248_);
lean_ctor_set(v_reuseFailAlloc_4278_, 2, v_ngen_4249_);
lean_ctor_set(v_reuseFailAlloc_4278_, 3, v_auxDeclNGen_4250_);
lean_ctor_set(v_reuseFailAlloc_4278_, 4, v_traceState_4251_);
lean_ctor_set(v_reuseFailAlloc_4278_, 5, v___x_4241_);
lean_ctor_set(v_reuseFailAlloc_4278_, 6, v_messages_4252_);
lean_ctor_set(v_reuseFailAlloc_4278_, 7, v_infoState_4253_);
lean_ctor_set(v_reuseFailAlloc_4278_, 8, v_snapshotTasks_4254_);
v___x_4260_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v_mctx_4263_; lean_object* v_zetaDeltaFVarIds_4264_; lean_object* v_postponed_4265_; lean_object* v_diag_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4276_; 
v___x_4261_ = lean_st_ref_put(v___y_4239_, v___x_4260_);
v___x_4262_ = lean_st_ref_take(v___y_4242_);
v_mctx_4263_ = lean_ctor_get(v___x_4262_, 0);
v_zetaDeltaFVarIds_4264_ = lean_ctor_get(v___x_4262_, 2);
v_postponed_4265_ = lean_ctor_get(v___x_4262_, 3);
v_diag_4266_ = lean_ctor_get(v___x_4262_, 4);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4276_ == 0)
{
lean_object* v_unused_4277_; 
v_unused_4277_ = lean_ctor_get(v___x_4262_, 1);
lean_dec(v_unused_4277_);
v___x_4268_ = v___x_4262_;
v_isShared_4269_ = v_isSharedCheck_4276_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_diag_4266_);
lean_inc(v_postponed_4265_);
lean_inc(v_zetaDeltaFVarIds_4264_);
lean_inc(v_mctx_4263_);
lean_dec(v___x_4262_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4276_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 1, v___x_4243_);
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_mctx_4263_);
lean_ctor_set(v_reuseFailAlloc_4275_, 1, v___x_4243_);
lean_ctor_set(v_reuseFailAlloc_4275_, 2, v_zetaDeltaFVarIds_4264_);
lean_ctor_set(v_reuseFailAlloc_4275_, 3, v_postponed_4265_);
lean_ctor_set(v_reuseFailAlloc_4275_, 4, v_diag_4266_);
v___x_4271_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4272_ = lean_st_ref_put(v___y_4242_, v___x_4271_);
v___x_4273_ = lean_box(0);
v___x_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
return v___x_4274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object* v___y_4281_, lean_object* v_isExporting_4282_, lean_object* v___x_4283_, lean_object* v___y_4284_, lean_object* v___x_4285_, lean_object* v_a_x3f_4286_, lean_object* v___y_4287_){
_start:
{
uint8_t v_isExporting_boxed_4288_; lean_object* v_res_4289_; 
v_isExporting_boxed_4288_ = lean_unbox(v_isExporting_4282_);
v_res_4289_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4281_, v_isExporting_boxed_4288_, v___x_4283_, v___y_4284_, v___x_4285_, v_a_x3f_4286_);
lean_dec(v_a_x3f_4286_);
lean_dec(v___y_4284_);
lean_dec(v___y_4281_);
return v_res_4289_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4290_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4291_);
return v___x_4292_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
return v___x_4294_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4296_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
lean_ctor_set(v___x_4296_, 2, v___x_4295_);
lean_ctor_set(v___x_4296_, 3, v___x_4295_);
lean_ctor_set(v___x_4296_, 4, v___x_4295_);
lean_ctor_set(v___x_4296_, 5, v___x_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object* v_x_4297_, uint8_t v_isExporting_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v___x_4306_; lean_object* v_env_4307_; uint8_t v_isExporting_4308_; lean_object* v___x_4374_; uint8_t v_isModule_4375_; 
v___x_4306_ = lean_st_ref_get(v___y_4304_);
v_env_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc_ref(v_env_4307_);
lean_dec(v___x_4306_);
v_isExporting_4308_ = lean_ctor_get_uint8(v_env_4307_, sizeof(void*)*8);
v___x_4374_ = l_Lean_Environment_header(v_env_4307_);
lean_dec_ref(v_env_4307_);
v_isModule_4375_ = lean_ctor_get_uint8(v___x_4374_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4374_);
if (v_isModule_4375_ == 0)
{
lean_object* v___x_4376_; 
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc_ref(v___y_4299_);
v___x_4376_ = lean_apply_7(v_x_4297_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, lean_box(0));
return v___x_4376_;
}
else
{
if (v_isExporting_4308_ == 0)
{
if (v_isExporting_4298_ == 0)
{
lean_object* v___x_4377_; 
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc_ref(v___y_4299_);
v___x_4377_ = lean_apply_7(v_x_4297_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, lean_box(0));
return v___x_4377_;
}
else
{
goto v___jp_4309_;
}
}
else
{
if (v_isExporting_4298_ == 0)
{
goto v___jp_4309_;
}
else
{
lean_object* v___x_4378_; 
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc_ref(v___y_4299_);
v___x_4378_ = lean_apply_7(v_x_4297_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, lean_box(0));
return v___x_4378_;
}
}
}
v___jp_4309_:
{
lean_object* v___x_4310_; lean_object* v_env_4311_; lean_object* v_nextMacroScope_4312_; lean_object* v_ngen_4313_; lean_object* v_auxDeclNGen_4314_; lean_object* v_traceState_4315_; lean_object* v_messages_4316_; lean_object* v_infoState_4317_; lean_object* v_snapshotTasks_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4372_; 
v___x_4310_ = lean_st_ref_take(v___y_4304_);
v_env_4311_ = lean_ctor_get(v___x_4310_, 0);
v_nextMacroScope_4312_ = lean_ctor_get(v___x_4310_, 1);
v_ngen_4313_ = lean_ctor_get(v___x_4310_, 2);
v_auxDeclNGen_4314_ = lean_ctor_get(v___x_4310_, 3);
v_traceState_4315_ = lean_ctor_get(v___x_4310_, 4);
v_messages_4316_ = lean_ctor_get(v___x_4310_, 6);
v_infoState_4317_ = lean_ctor_get(v___x_4310_, 7);
v_snapshotTasks_4318_ = lean_ctor_get(v___x_4310_, 8);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4372_ == 0)
{
lean_object* v_unused_4373_; 
v_unused_4373_ = lean_ctor_get(v___x_4310_, 5);
lean_dec(v_unused_4373_);
v___x_4320_ = v___x_4310_;
v_isShared_4321_ = v_isSharedCheck_4372_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_snapshotTasks_4318_);
lean_inc(v_infoState_4317_);
lean_inc(v_messages_4316_);
lean_inc(v_traceState_4315_);
lean_inc(v_auxDeclNGen_4314_);
lean_inc(v_ngen_4313_);
lean_inc(v_nextMacroScope_4312_);
lean_inc(v_env_4311_);
lean_dec(v___x_4310_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4372_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4325_; 
v___x_4322_ = l_Lean_Environment_setExporting(v_env_4311_, v_isExporting_4298_);
v___x_4323_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4321_ == 0)
{
lean_ctor_set(v___x_4320_, 5, v___x_4323_);
lean_ctor_set(v___x_4320_, 0, v___x_4322_);
v___x_4325_ = v___x_4320_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4322_);
lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_nextMacroScope_4312_);
lean_ctor_set(v_reuseFailAlloc_4371_, 2, v_ngen_4313_);
lean_ctor_set(v_reuseFailAlloc_4371_, 3, v_auxDeclNGen_4314_);
lean_ctor_set(v_reuseFailAlloc_4371_, 4, v_traceState_4315_);
lean_ctor_set(v_reuseFailAlloc_4371_, 5, v___x_4323_);
lean_ctor_set(v_reuseFailAlloc_4371_, 6, v_messages_4316_);
lean_ctor_set(v_reuseFailAlloc_4371_, 7, v_infoState_4317_);
lean_ctor_set(v_reuseFailAlloc_4371_, 8, v_snapshotTasks_4318_);
v___x_4325_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v_mctx_4328_; lean_object* v_zetaDeltaFVarIds_4329_; lean_object* v_postponed_4330_; lean_object* v_diag_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4369_; 
v___x_4326_ = lean_st_ref_put(v___y_4304_, v___x_4325_);
v___x_4327_ = lean_st_ref_take(v___y_4302_);
v_mctx_4328_ = lean_ctor_get(v___x_4327_, 0);
v_zetaDeltaFVarIds_4329_ = lean_ctor_get(v___x_4327_, 2);
v_postponed_4330_ = lean_ctor_get(v___x_4327_, 3);
v_diag_4331_ = lean_ctor_get(v___x_4327_, 4);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4369_ == 0)
{
lean_object* v_unused_4370_; 
v_unused_4370_ = lean_ctor_get(v___x_4327_, 1);
lean_dec(v_unused_4370_);
v___x_4333_ = v___x_4327_;
v_isShared_4334_ = v_isSharedCheck_4369_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_diag_4331_);
lean_inc(v_postponed_4330_);
lean_inc(v_zetaDeltaFVarIds_4329_);
lean_inc(v_mctx_4328_);
lean_dec(v___x_4327_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4369_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4335_; lean_object* v___x_4337_; 
v___x_4335_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 1, v___x_4335_);
v___x_4337_ = v___x_4333_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_mctx_4328_);
lean_ctor_set(v_reuseFailAlloc_4368_, 1, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4368_, 2, v_zetaDeltaFVarIds_4329_);
lean_ctor_set(v_reuseFailAlloc_4368_, 3, v_postponed_4330_);
lean_ctor_set(v_reuseFailAlloc_4368_, 4, v_diag_4331_);
v___x_4337_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4338_; lean_object* v_r_4339_; 
v___x_4338_ = lean_st_ref_put(v___y_4302_, v___x_4337_);
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc_ref(v___y_4299_);
v_r_4339_ = lean_apply_7(v_x_4297_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, lean_box(0));
if (lean_obj_tag(v_r_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4356_; 
v_a_4340_ = lean_ctor_get(v_r_4339_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_r_4339_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4342_ = v_r_4339_;
v_isShared_4343_ = v_isSharedCheck_4356_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v_r_4339_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4356_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
lean_inc(v_a_4340_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set_tag(v___x_4342_, 1);
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
v___x_4346_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4304_, v_isExporting_4308_, v___x_4323_, v___y_4302_, v___x_4335_, v___x_4345_);
lean_dec_ref(v___x_4345_);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v___x_4346_, 0);
lean_dec(v_unused_4354_);
v___x_4348_ = v___x_4346_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_dec(v___x_4346_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 0, v_a_4340_);
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4340_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
v_a_4357_ = lean_ctor_get(v_r_4339_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v_r_4339_, 1);
v___x_4358_ = lean_box(0);
v___x_4359_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4304_, v_isExporting_4308_, v___x_4323_, v___y_4302_, v___x_4335_, v___x_4358_);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4366_ == 0)
{
lean_object* v_unused_4367_; 
v_unused_4367_ = lean_ctor_get(v___x_4359_, 0);
lean_dec(v_unused_4367_);
v___x_4361_ = v___x_4359_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_dec(v___x_4359_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
lean_ctor_set_tag(v___x_4361_, 1);
lean_ctor_set(v___x_4361_, 0, v_a_4357_);
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4357_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v_x_4379_, lean_object* v_isExporting_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
uint8_t v_isExporting_boxed_4388_; lean_object* v_res_4389_; 
v_isExporting_boxed_4388_ = lean_unbox(v_isExporting_4380_);
v_res_4389_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4379_, v_isExporting_boxed_4388_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b1_4390_, lean_object* v_x_4391_, uint8_t v_isExporting_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4391_, v_isExporting_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object* v_00_u03b1_4401_, lean_object* v_x_4402_, lean_object* v_isExporting_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
uint8_t v_isExporting_boxed_4411_; lean_object* v_res_4412_; 
v_isExporting_boxed_4411_ = lean_unbox(v_isExporting_4403_);
v_res_4412_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(v_00_u03b1_4401_, v_x_4402_, v_isExporting_boxed_4411_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4423_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4423_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
return v_res_4433_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4435_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4436_ = l_Lean_stringToMessageData(v___x_4435_);
return v___x_4436_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4438_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4439_ = l_Lean_stringToMessageData(v___x_4438_);
return v___x_4439_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4441_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4));
v___x_4442_ = l_Lean_stringToMessageData(v___x_4441_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4443_, lean_object* v___x_4444_, lean_object* v_inductiveTypeName_4445_, uint8_t v___x_4446_, lean_object* v___x_4447_, lean_object* v_ctorName_4448_, uint8_t v_addHypotheses_4449_, lean_object* v___f_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___y_4459_; lean_object* v___x_4462_; 
lean_inc(v_inductiveTypeName_4445_);
v___x_4462_ = l_Lean_Elab_Deriving_mkContext(v___x_4443_, v___x_4444_, v_inductiveTypeName_4445_, v___x_4446_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_object* v_a_4463_; lean_object* v_options_4464_; lean_object* v_currNamespace_4465_; lean_object* v_inheritedTraceOptions_4466_; lean_object* v___x_4467_; 
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_a_4463_);
lean_dec_ref_known(v___x_4462_, 1);
v_options_4464_ = lean_ctor_get(v___y_4455_, 2);
v_currNamespace_4465_ = lean_ctor_get(v___y_4455_, 6);
v_inheritedTraceOptions_4466_ = lean_ctor_get(v___y_4455_, 13);
lean_inc(v_inductiveTypeName_4445_);
v___x_4467_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4445_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v_instName_4469_; lean_object* v_auxFunNames_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; uint8_t v___y_4522_; lean_object* v___y_4523_; uint8_t v___y_4524_; uint8_t v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v_a_4578_; lean_object* v___y_4649_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc_n(v_a_4468_, 2);
lean_dec_ref_known(v___x_4467_, 1);
v_instName_4469_ = lean_ctor_get(v_a_4463_, 0);
lean_inc(v_instName_4469_);
v_auxFunNames_4470_ = lean_ctor_get(v_a_4463_, 2);
lean_inc_ref(v_auxFunNames_4470_);
lean_dec(v_a_4463_);
v___x_4471_ = lean_unsigned_to_nat(0u);
v___x_4472_ = lean_array_get(v___x_4447_, v_auxFunNames_4470_, v___x_4471_);
lean_dec_ref(v_auxFunNames_4470_);
lean_inc(v_currNamespace_4465_);
v___x_4473_ = l_Lean_Name_append(v_currNamespace_4465_, v___x_4472_);
v___x_4668_ = lean_box(v_addHypotheses_4449_);
lean_inc(v_inductiveTypeName_4445_);
v___x_4669_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4669_, 0, v_inductiveTypeName_4445_);
lean_closure_set(v___x_4669_, 1, v_ctorName_4448_);
lean_closure_set(v___x_4669_, 2, v___x_4668_);
lean_closure_set(v___x_4669_, 3, v_a_4468_);
lean_inc(v___x_4473_);
v___x_4670_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4473_, v___x_4669_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; 
lean_dec_ref(v___f_4450_);
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
v_a_4578_ = v_a_4671_;
goto v___jp_4577_;
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4704_; 
v_a_4672_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4674_ = v___x_4670_;
v_isShared_4675_ = v_isSharedCheck_4704_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4670_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4704_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
uint8_t v___y_4680_; uint8_t v___x_4702_; 
v___x_4702_ = l_Lean_Exception_isInterrupt(v_a_4672_);
if (v___x_4702_ == 0)
{
uint8_t v___x_4703_; 
lean_inc(v_a_4672_);
v___x_4703_ = l_Lean_Exception_isRuntime(v_a_4672_);
v___y_4680_ = v___x_4703_;
goto v___jp_4679_;
}
else
{
v___y_4680_ = v___x_4702_;
goto v___jp_4679_;
}
v___jp_4676_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4677_ = lean_box(0);
lean_inc(v___y_4456_);
lean_inc_ref(v___y_4455_);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
v___x_4678_ = lean_apply_8(v___f_4450_, v___x_4677_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, lean_box(0));
v___y_4649_ = v___x_4678_;
goto v___jp_4648_;
}
v___jp_4679_:
{
if (v___y_4680_ == 0)
{
uint8_t v_hasTrace_4681_; 
lean_del_object(v___x_4674_);
v_hasTrace_4681_ = lean_ctor_get_uint8(v_options_4464_, sizeof(void*)*1);
if (v_hasTrace_4681_ == 0)
{
lean_dec(v_a_4672_);
goto v___jp_4676_;
}
else
{
lean_object* v___x_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; 
v___x_4682_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4683_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4684_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4466_, v_options_4464_, v___x_4683_);
if (v___x_4684_ == 0)
{
lean_dec(v_a_4672_);
goto v___jp_4676_;
}
else
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4685_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
v___x_4686_ = l_Lean_Exception_toMessageData(v_a_4672_);
v___x_4687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4685_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4682_, v___x_4687_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4690_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4689_);
lean_dec_ref_known(v___x_4688_, 1);
lean_inc(v___y_4456_);
lean_inc_ref(v___y_4455_);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
v___x_4690_ = lean_apply_8(v___f_4450_, v_a_4689_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, lean_box(0));
v___y_4649_ = v___x_4690_;
goto v___jp_4648_;
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
lean_dec(v___x_4473_);
lean_dec(v_instName_4469_);
lean_dec(v_a_4468_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v___f_4450_);
lean_dec(v_inductiveTypeName_4445_);
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
lean_dec(v___x_4473_);
lean_dec(v_instName_4469_);
lean_dec(v_a_4468_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v___f_4450_);
lean_dec(v_inductiveTypeName_4445_);
if (v_isShared_4675_ == 0)
{
v___x_4700_ = v___x_4674_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4672_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
}
v___jp_4474_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4483_ = l_Lean_mkIdent(v_instName_4469_);
v___x_4484_ = l_Lean_mkCIdent(v___x_4473_);
v___x_4485_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4445_, v___x_4483_, v___y_4476_, v___x_4484_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_options_4486_; uint8_t v_hasTrace_4487_; 
v_options_4486_ = lean_ctor_get(v___y_4481_, 2);
v_hasTrace_4487_ = lean_ctor_get_uint8(v_options_4486_, sizeof(void*)*1);
if (v_hasTrace_4487_ == 0)
{
lean_object* v_a_4488_; 
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4475_);
v_a_4488_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4488_);
lean_dec_ref_known(v___x_4485_, 1);
v___y_4459_ = v_a_4488_;
goto v___jp_4458_;
}
else
{
lean_object* v_a_4489_; lean_object* v_inheritedTraceOptions_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v_a_4489_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4485_, 1);
v_inheritedTraceOptions_4490_ = lean_ctor_get(v___y_4481_, 13);
v___x_4491_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4475_);
v___x_4492_ = l_Lean_Name_append(v___x_4491_, v___y_4475_);
v___x_4493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4490_, v_options_4486_, v___x_4492_);
lean_dec(v___x_4492_);
if (v___x_4493_ == 0)
{
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4475_);
v___y_4459_ = v_a_4489_;
goto v___jp_4458_;
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4494_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4489_);
v___x_4495_ = l_Lean_MessageData_ofSyntax(v_a_4489_);
v___x_4496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4494_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
v___x_4497_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4475_, v___x_4496_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_dec_ref_known(v___x_4497_, 1);
v___y_4459_ = v_a_4489_;
goto v___jp_4458_;
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec(v_a_4489_);
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4497_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4497_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4475_);
v_a_4506_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4485_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4485_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
v___jp_4514_:
{
lean_object* v___x_4525_; 
v___x_4525_ = l_Lean_compileDecls(v___y_4517_, v___y_4524_, v___y_4520_, v___y_4516_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v___x_4526_; 
lean_dec_ref_known(v___x_4525_, 1);
lean_inc(v___x_4473_);
v___x_4526_ = l_Lean_enableRealizationsForConst(v___x_4473_, v___y_4520_, v___y_4516_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_options_4527_; lean_object* v_inheritedTraceOptions_4528_; uint8_t v_hasTrace_4529_; lean_object* v___x_4530_; 
lean_dec_ref_known(v___x_4526_, 1);
v_options_4527_ = lean_ctor_get(v___y_4520_, 2);
v_inheritedTraceOptions_4528_ = lean_ctor_get(v___y_4520_, 13);
v_hasTrace_4529_ = lean_ctor_get_uint8(v_options_4527_, sizeof(void*)*1);
v___x_4530_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4529_ == 0)
{
v___y_4475_ = v___x_4530_;
v___y_4476_ = v___y_4523_;
v___y_4477_ = v___y_4515_;
v___y_4478_ = v___y_4518_;
v___y_4479_ = v___y_4519_;
v___y_4480_ = v___y_4521_;
v___y_4481_ = v___y_4520_;
v___y_4482_ = v___y_4516_;
goto v___jp_4474_;
}
else
{
lean_object* v___x_4531_; uint8_t v___x_4532_; 
v___x_4531_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4532_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4528_, v_options_4527_, v___x_4531_);
if (v___x_4532_ == 0)
{
v___y_4475_ = v___x_4530_;
v___y_4476_ = v___y_4523_;
v___y_4477_ = v___y_4515_;
v___y_4478_ = v___y_4518_;
v___y_4479_ = v___y_4519_;
v___y_4480_ = v___y_4521_;
v___y_4481_ = v___y_4520_;
v___y_4482_ = v___y_4516_;
goto v___jp_4474_;
}
else
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4533_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4473_);
v___x_4534_ = l_Lean_MessageData_ofConstName(v___x_4473_, v___y_4522_);
v___x_4535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4533_);
lean_ctor_set(v___x_4535_, 1, v___x_4534_);
v___x_4536_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4530_, v___x_4535_, v___y_4519_, v___y_4521_, v___y_4520_, v___y_4516_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_dec_ref_known(v___x_4536_, 1);
v___y_4475_ = v___x_4530_;
v___y_4476_ = v___y_4523_;
v___y_4477_ = v___y_4515_;
v___y_4478_ = v___y_4518_;
v___y_4479_ = v___y_4519_;
v___y_4480_ = v___y_4521_;
v___y_4481_ = v___y_4520_;
v___y_4482_ = v___y_4516_;
goto v___jp_4474_;
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
lean_dec(v___y_4523_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___x_4473_);
lean_dec(v_instName_4469_);
lean_dec(v_inductiveTypeName_4445_);
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4536_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4536_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec(v___y_4523_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___x_4473_);
lean_dec(v_instName_4469_);
lean_dec(v_inductiveTypeName_4445_);
v_a_4545_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4526_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4526_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v___y_4523_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___x_4473_);
lean_dec(v_instName_4469_);
lean_dec(v_inductiveTypeName_4445_);
v_a_4553_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4525_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4525_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
v___jp_4561_:
{
lean_object* v___x_4570_; lean_object* v_env_4571_; uint8_t v_isNoncomputableSection_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4570_ = lean_st_ref_get(v___y_4569_);
v_env_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc_ref(v_env_4571_);
lean_dec(v___x_4570_);
v_isNoncomputableSection_4572_ = lean_ctor_get_uint8(v___y_4564_, sizeof(void*)*8 + 4);
v___x_4573_ = lean_unsigned_to_nat(1u);
v___x_4574_ = lean_mk_empty_array_with_capacity(v___x_4573_);
lean_inc(v___x_4473_);
v___x_4575_ = lean_array_push(v___x_4574_, v___x_4473_);
if (v_isNoncomputableSection_4572_ == 0)
{
lean_dec_ref(v_env_4571_);
v___y_4515_ = v___y_4564_;
v___y_4516_ = v___y_4569_;
v___y_4517_ = v___x_4575_;
v___y_4518_ = v___y_4565_;
v___y_4519_ = v___y_4566_;
v___y_4520_ = v___y_4568_;
v___y_4521_ = v___y_4567_;
v___y_4522_ = v___y_4562_;
v___y_4523_ = v___y_4563_;
v___y_4524_ = v___x_4446_;
goto v___jp_4514_;
}
else
{
uint8_t v___x_4576_; 
lean_inc(v___x_4473_);
v___x_4576_ = l_Lean_isMarkedMeta(v_env_4571_, v___x_4473_);
v___y_4515_ = v___y_4564_;
v___y_4516_ = v___y_4569_;
v___y_4517_ = v___x_4575_;
v___y_4518_ = v___y_4565_;
v___y_4519_ = v___y_4566_;
v___y_4520_ = v___y_4568_;
v___y_4521_ = v___y_4567_;
v___y_4522_ = v___y_4562_;
v___y_4523_ = v___y_4563_;
v___y_4524_ = v___x_4576_;
goto v___jp_4514_;
}
}
v___jp_4577_:
{
lean_object* v_snd_4579_; lean_object* v_fst_4580_; lean_object* v_fst_4581_; lean_object* v_snd_4582_; lean_object* v___x_4583_; lean_object* v_toConstantVal_4584_; lean_object* v_env_4585_; lean_object* v_levelParams_4586_; uint32_t v___x_4587_; uint32_t v___x_4588_; uint32_t v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4647_; 
v_snd_4579_ = lean_ctor_get(v_a_4578_, 1);
lean_inc(v_snd_4579_);
v_fst_4580_ = lean_ctor_get(v_a_4578_, 0);
lean_inc(v_fst_4580_);
lean_dec_ref(v_a_4578_);
v_fst_4581_ = lean_ctor_get(v_snd_4579_, 0);
lean_inc_n(v_fst_4581_, 2);
v_snd_4582_ = lean_ctor_get(v_snd_4579_, 1);
lean_inc(v_snd_4582_);
lean_dec(v_snd_4579_);
v___x_4583_ = lean_st_ref_get(v___y_4456_);
v_toConstantVal_4584_ = lean_ctor_get(v_a_4468_, 0);
lean_inc_ref(v_toConstantVal_4584_);
lean_dec(v_a_4468_);
v_env_4585_ = lean_ctor_get(v___x_4583_, 0);
lean_inc_ref(v_env_4585_);
lean_dec(v___x_4583_);
v_levelParams_4586_ = lean_ctor_get(v_toConstantVal_4584_, 1);
lean_inc(v_levelParams_4586_);
lean_dec_ref(v_toConstantVal_4584_);
v___x_4587_ = l_Lean_getMaxHeight(v_env_4585_, v_fst_4581_);
v___x_4588_ = 1;
v___x_4589_ = lean_uint32_add(v___x_4587_, v___x_4588_);
v___x_4590_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4590_, 0, v___x_4589_);
lean_inc(v___x_4473_);
v___x_4591_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4473_, v_levelParams_4586_, v_fst_4580_, v_fst_4581_, v___x_4590_, v___y_4456_);
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4647_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4647_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
lean_ctor_set_tag(v___x_4594_, 1);
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
uint8_t v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = 0;
v___x_4599_ = l_Lean_addDecl(v___x_4597_, v___x_4598_, v___y_4455_, v___y_4456_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v___x_4600_; lean_object* v_env_4601_; uint8_t v___x_4602_; 
lean_dec_ref_known(v___x_4599_, 1);
v___x_4600_ = lean_st_ref_get(v___y_4456_);
v_env_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc_ref(v_env_4601_);
lean_dec(v___x_4600_);
lean_inc(v_inductiveTypeName_4445_);
v___x_4602_ = l_Lean_isMarkedMeta(v_env_4601_, v_inductiveTypeName_4445_);
if (v___x_4602_ == 0)
{
v___y_4562_ = v___x_4598_;
v___y_4563_ = v_snd_4582_;
v___y_4564_ = v___y_4451_;
v___y_4565_ = v___y_4452_;
v___y_4566_ = v___y_4453_;
v___y_4567_ = v___y_4454_;
v___y_4568_ = v___y_4455_;
v___y_4569_ = v___y_4456_;
goto v___jp_4561_;
}
else
{
lean_object* v___x_4603_; lean_object* v_env_4604_; lean_object* v_nextMacroScope_4605_; lean_object* v_ngen_4606_; lean_object* v_auxDeclNGen_4607_; lean_object* v_traceState_4608_; lean_object* v_messages_4609_; lean_object* v_infoState_4610_; lean_object* v_snapshotTasks_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4636_; 
v___x_4603_ = lean_st_ref_take(v___y_4456_);
v_env_4604_ = lean_ctor_get(v___x_4603_, 0);
v_nextMacroScope_4605_ = lean_ctor_get(v___x_4603_, 1);
v_ngen_4606_ = lean_ctor_get(v___x_4603_, 2);
v_auxDeclNGen_4607_ = lean_ctor_get(v___x_4603_, 3);
v_traceState_4608_ = lean_ctor_get(v___x_4603_, 4);
v_messages_4609_ = lean_ctor_get(v___x_4603_, 6);
v_infoState_4610_ = lean_ctor_get(v___x_4603_, 7);
v_snapshotTasks_4611_ = lean_ctor_get(v___x_4603_, 8);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4636_ == 0)
{
lean_object* v_unused_4637_; 
v_unused_4637_ = lean_ctor_get(v___x_4603_, 5);
lean_dec(v_unused_4637_);
v___x_4613_ = v___x_4603_;
v_isShared_4614_ = v_isSharedCheck_4636_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_snapshotTasks_4611_);
lean_inc(v_infoState_4610_);
lean_inc(v_messages_4609_);
lean_inc(v_traceState_4608_);
lean_inc(v_auxDeclNGen_4607_);
lean_inc(v_ngen_4606_);
lean_inc(v_nextMacroScope_4605_);
lean_inc(v_env_4604_);
lean_dec(v___x_4603_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4636_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
lean_inc(v___x_4473_);
v___x_4615_ = l_Lean_markMeta(v_env_4604_, v___x_4473_);
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
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v_nextMacroScope_4605_);
lean_ctor_set(v_reuseFailAlloc_4635_, 2, v_ngen_4606_);
lean_ctor_set(v_reuseFailAlloc_4635_, 3, v_auxDeclNGen_4607_);
lean_ctor_set(v_reuseFailAlloc_4635_, 4, v_traceState_4608_);
lean_ctor_set(v_reuseFailAlloc_4635_, 5, v___x_4616_);
lean_ctor_set(v_reuseFailAlloc_4635_, 6, v_messages_4609_);
lean_ctor_set(v_reuseFailAlloc_4635_, 7, v_infoState_4610_);
lean_ctor_set(v_reuseFailAlloc_4635_, 8, v_snapshotTasks_4611_);
v___x_4618_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v_mctx_4621_; lean_object* v_zetaDeltaFVarIds_4622_; lean_object* v_postponed_4623_; lean_object* v_diag_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4633_; 
v___x_4619_ = lean_st_ref_put(v___y_4456_, v___x_4618_);
v___x_4620_ = lean_st_ref_take(v___y_4454_);
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
v___x_4631_ = lean_st_ref_put(v___y_4454_, v___x_4630_);
v___y_4562_ = v___x_4598_;
v___y_4563_ = v_snd_4582_;
v___y_4564_ = v___y_4451_;
v___y_4565_ = v___y_4452_;
v___y_4566_ = v___y_4453_;
v___y_4567_ = v___y_4454_;
v___y_4568_ = v___y_4455_;
v___y_4569_ = v___y_4456_;
goto v___jp_4561_;
}
}
}
}
}
}
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
lean_dec(v_snd_4582_);
lean_dec(v___x_4473_);
lean_dec(v_instName_4469_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v_inductiveTypeName_4445_);
v_a_4638_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4599_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4599_);
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
lean_dec(v___x_4473_);
lean_dec(v_instName_4469_);
lean_dec(v_a_4468_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v_inductiveTypeName_4445_);
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
v_a_4578_ = v_a_4658_;
goto v___jp_4577_;
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec(v___x_4473_);
lean_dec(v_instName_4469_);
lean_dec(v_a_4468_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v_inductiveTypeName_4445_);
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
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec(v_a_4463_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v___f_4450_);
lean_dec(v_ctorName_4448_);
lean_dec(v_inductiveTypeName_4445_);
v_a_4705_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4467_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4467_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v___f_4450_);
lean_dec(v_ctorName_4448_);
lean_dec(v_inductiveTypeName_4445_);
v_a_4713_ = lean_ctor_get(v___x_4462_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4462_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4462_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
v___jp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___y_4459_);
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
return v___x_4461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4721_, lean_object* v___x_4722_, lean_object* v_inductiveTypeName_4723_, lean_object* v___x_4724_, lean_object* v___x_4725_, lean_object* v_ctorName_4726_, lean_object* v_addHypotheses_4727_, lean_object* v___f_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
uint8_t v___x_17618__boxed_4736_; uint8_t v_addHypotheses_boxed_4737_; lean_object* v_res_4738_; 
v___x_17618__boxed_4736_ = lean_unbox(v___x_4724_);
v_addHypotheses_boxed_4737_ = lean_unbox(v_addHypotheses_4727_);
v_res_4738_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4721_, v___x_4722_, v_inductiveTypeName_4723_, v___x_17618__boxed_4736_, v___x_4725_, v_ctorName_4726_, v_addHypotheses_boxed_4737_, v___f_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
lean_dec(v___x_4725_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4741_, lean_object* v_ctorName_4742_, uint8_t v_addHypotheses_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v___f_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; uint8_t v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___f_4758_; uint8_t v___x_4759_; 
v___f_4751_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4752_ = lean_box(0);
v___x_4753_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4754_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4755_ = 1;
v___x_4756_ = lean_box(v___x_4755_);
v___x_4757_ = lean_box(v_addHypotheses_4743_);
lean_inc(v_ctorName_4742_);
v___f_4758_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4758_, 0, v___x_4753_);
lean_closure_set(v___f_4758_, 1, v___x_4754_);
lean_closure_set(v___f_4758_, 2, v_inductiveTypeName_4741_);
lean_closure_set(v___f_4758_, 3, v___x_4756_);
lean_closure_set(v___f_4758_, 4, v___x_4752_);
lean_closure_set(v___f_4758_, 5, v_ctorName_4742_);
lean_closure_set(v___f_4758_, 6, v___x_4757_);
lean_closure_set(v___f_4758_, 7, v___f_4751_);
v___x_4759_ = l_Lean_isPrivateName(v_ctorName_4742_);
lean_dec(v_ctorName_4742_);
if (v___x_4759_ == 0)
{
lean_object* v___x_4760_; 
v___x_4760_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4758_, v___x_4755_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
return v___x_4760_;
}
else
{
uint8_t v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = 0;
v___x_4762_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4758_, v___x_4761_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
return v___x_4762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4763_, lean_object* v_ctorName_4764_, lean_object* v_addHypotheses_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
uint8_t v_addHypotheses_boxed_4773_; lean_object* v_res_4774_; 
v_addHypotheses_boxed_4773_ = lean_unbox(v_addHypotheses_4765_);
v_res_4774_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4763_, v_ctorName_4764_, v_addHypotheses_boxed_4773_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4775_, lean_object* v_ctorName_4776_, uint8_t v_addHypotheses_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4781_ = lean_box(v_addHypotheses_4777_);
v___x_4782_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4782_, 0, v_inductiveTypeName_4775_);
lean_closure_set(v___x_4782_, 1, v_ctorName_4776_);
lean_closure_set(v___x_4782_, 2, v___x_4781_);
v___x_4783_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4782_, v_a_4778_, v_a_4779_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4813_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4786_ = v___x_4783_;
v_isShared_4787_ = v_isSharedCheck_4813_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4813_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
if (lean_obj_tag(v_a_4784_) == 0)
{
uint8_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4791_; 
v___x_4788_ = 0;
v___x_4789_ = lean_box(v___x_4788_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set(v___x_4786_, 0, v___x_4789_);
v___x_4791_ = v___x_4786_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
else
{
lean_object* v_val_4793_; lean_object* v___x_4794_; 
lean_del_object(v___x_4786_);
v_val_4793_ = lean_ctor_get(v_a_4784_, 0);
lean_inc(v_val_4793_);
lean_dec_ref_known(v_a_4784_, 1);
v___x_4794_ = l_Lean_Elab_Command_elabCommand(v_val_4793_, v_a_4778_, v_a_4779_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4803_; 
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4803_ == 0)
{
lean_object* v_unused_4804_; 
v_unused_4804_ = lean_ctor_get(v___x_4794_, 0);
lean_dec(v_unused_4804_);
v___x_4796_ = v___x_4794_;
v_isShared_4797_ = v_isSharedCheck_4803_;
goto v_resetjp_4795_;
}
else
{
lean_dec(v___x_4794_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4803_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
uint8_t v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4798_ = 1;
v___x_4799_ = lean_box(v___x_4798_);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 0, v___x_4799_);
v___x_4801_ = v___x_4796_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4799_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
v_a_4805_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4794_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4794_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
}
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
v_a_4814_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4783_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4783_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4822_, lean_object* v_ctorName_4823_, lean_object* v_addHypotheses_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_){
_start:
{
uint8_t v_addHypotheses_boxed_4828_; lean_object* v_res_4829_; 
v_addHypotheses_boxed_4828_ = lean_unbox(v_addHypotheses_4824_);
v_res_4829_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4822_, v_ctorName_4823_, v_addHypotheses_boxed_4828_, v_a_4825_, v_a_4826_);
lean_dec(v_a_4826_);
lean_dec_ref(v_a_4825_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4833_, uint8_t v_addHypotheses_4834_, lean_object* v_as_x27_4835_, lean_object* v_b_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
if (lean_obj_tag(v_as_x27_4835_) == 0)
{
lean_object* v___x_4840_; 
lean_dec(v_declName_4833_);
v___x_4840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4840_, 0, v_b_4836_);
return v___x_4840_;
}
else
{
lean_object* v_head_4841_; lean_object* v_tail_4842_; lean_object* v___x_4843_; 
lean_dec_ref(v_b_4836_);
v_head_4841_ = lean_ctor_get(v_as_x27_4835_, 0);
v_tail_4842_ = lean_ctor_get(v_as_x27_4835_, 1);
lean_inc(v_head_4841_);
lean_inc(v_declName_4833_);
v___x_4843_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4833_, v_head_4841_, v_addHypotheses_4834_, v___y_4837_, v___y_4838_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4857_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4846_ = v___x_4843_;
v_isShared_4847_ = v_isSharedCheck_4857_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4843_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4857_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4848_; uint8_t v___x_4849_; 
v___x_4848_ = lean_box(0);
v___x_4849_ = lean_unbox(v_a_4844_);
if (v___x_4849_ == 0)
{
lean_object* v___x_4850_; 
lean_del_object(v___x_4846_);
lean_dec(v_a_4844_);
v___x_4850_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v_as_x27_4835_ = v_tail_4842_;
v_b_4836_ = v___x_4850_;
goto _start;
}
else
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4855_; 
lean_dec(v_declName_4833_);
v___x_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4852_, 0, v_a_4844_);
v___x_4853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4852_);
lean_ctor_set(v___x_4853_, 1, v___x_4848_);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 0, v___x_4853_);
v___x_4855_ = v___x_4846_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
else
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4865_; 
lean_dec(v_declName_4833_);
v_a_4858_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4860_ = v___x_4843_;
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4843_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4863_; 
if (v_isShared_4861_ == 0)
{
v___x_4863_ = v___x_4860_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_4866_, lean_object* v_addHypotheses_4867_, lean_object* v_as_x27_4868_, lean_object* v_b_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
uint8_t v_addHypotheses_boxed_4873_; lean_object* v_res_4874_; 
v_addHypotheses_boxed_4873_ = lean_unbox(v_addHypotheses_4867_);
v_res_4874_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4866_, v_addHypotheses_boxed_4873_, v_as_x27_4868_, v_b_4869_, v___y_4870_, v___y_4871_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v_as_x27_4868_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_4875_, lean_object* v_declName_4876_, uint8_t v_addHypotheses_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v_ctors_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v_ctors_4881_ = lean_ctor_get(v_a_4875_, 4);
v___x_4882_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_4883_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4876_, v_addHypotheses_4877_, v_ctors_4881_, v___x_4882_, v___y_4878_, v___y_4879_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4898_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4886_ = v___x_4883_;
v_isShared_4887_ = v_isSharedCheck_4898_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4883_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4898_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v_fst_4888_; 
v_fst_4888_ = lean_ctor_get(v_a_4884_, 0);
lean_inc(v_fst_4888_);
lean_dec(v_a_4884_);
if (lean_obj_tag(v_fst_4888_) == 0)
{
uint8_t v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4892_; 
v___x_4889_ = 0;
v___x_4890_ = lean_box(v___x_4889_);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 0, v___x_4890_);
v___x_4892_ = v___x_4886_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4890_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
else
{
lean_object* v_val_4894_; lean_object* v___x_4896_; 
v_val_4894_ = lean_ctor_get(v_fst_4888_, 0);
lean_inc(v_val_4894_);
lean_dec_ref_known(v_fst_4888_, 1);
if (v_isShared_4887_ == 0)
{
lean_ctor_set(v___x_4886_, 0, v_val_4894_);
v___x_4896_ = v___x_4886_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_val_4894_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
v_a_4899_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4883_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4883_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_4907_, lean_object* v_declName_4908_, lean_object* v_addHypotheses_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
uint8_t v_addHypotheses_boxed_4913_; lean_object* v_res_4914_; 
v_addHypotheses_boxed_4913_ = lean_unbox(v_addHypotheses_4909_);
v_res_4914_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_4907_, v_declName_4908_, v_addHypotheses_boxed_4913_, v___y_4910_, v___y_4911_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec_ref(v_a_4907_);
return v_res_4914_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4915_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4916_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4916_);
return v___x_4917_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4918_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4919_ = lean_unsigned_to_nat(0u);
v___x_4920_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4919_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
lean_ctor_set(v___x_4920_, 2, v___x_4919_);
lean_ctor_set(v___x_4920_, 3, v___x_4919_);
lean_ctor_set(v___x_4920_, 4, v___x_4918_);
lean_ctor_set(v___x_4920_, 5, v___x_4918_);
lean_ctor_set(v___x_4920_, 6, v___x_4918_);
lean_ctor_set(v___x_4920_, 7, v___x_4918_);
lean_ctor_set(v___x_4920_, 8, v___x_4918_);
lean_ctor_set(v___x_4920_, 9, v___x_4918_);
lean_ctor_set(v___x_4920_, 10, v___x_4918_);
return v___x_4920_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4921_ = lean_unsigned_to_nat(32u);
v___x_4922_ = lean_mk_empty_array_with_capacity(v___x_4921_);
v___x_4923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4922_);
return v___x_4923_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4924_ = ((size_t)5ULL);
v___x_4925_ = lean_unsigned_to_nat(0u);
v___x_4926_ = lean_unsigned_to_nat(32u);
v___x_4927_ = lean_mk_empty_array_with_capacity(v___x_4926_);
v___x_4928_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_4929_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
lean_ctor_set(v___x_4929_, 1, v___x_4927_);
lean_ctor_set(v___x_4929_, 2, v___x_4925_);
lean_ctor_set(v___x_4929_, 3, v___x_4925_);
lean_ctor_set_usize(v___x_4929_, 4, v___x_4924_);
return v___x_4929_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4930_ = lean_box(1);
v___x_4931_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_4932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4932_);
lean_ctor_set(v___x_4933_, 1, v___x_4931_);
lean_ctor_set(v___x_4933_, 2, v___x_4930_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_4934_, lean_object* v___y_4935_){
_start:
{
lean_object* v___x_4937_; lean_object* v_env_4938_; lean_object* v___x_4939_; lean_object* v_scopes_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v_opts_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4937_ = lean_st_ref_get(v___y_4935_);
v_env_4938_ = lean_ctor_get(v___x_4937_, 0);
lean_inc_ref(v_env_4938_);
lean_dec(v___x_4937_);
v___x_4939_ = lean_st_ref_get(v___y_4935_);
v_scopes_4940_ = lean_ctor_get(v___x_4939_, 2);
lean_inc(v_scopes_4940_);
lean_dec(v___x_4939_);
v___x_4941_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4942_ = l_List_head_x21___redArg(v___x_4941_, v_scopes_4940_);
lean_dec(v_scopes_4940_);
v_opts_4943_ = lean_ctor_get(v___x_4942_, 1);
lean_inc_ref(v_opts_4943_);
lean_dec(v___x_4942_);
v___x_4944_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_4945_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5);
v___x_4946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4946_, 0, v_env_4938_);
lean_ctor_set(v___x_4946_, 1, v___x_4944_);
lean_ctor_set(v___x_4946_, 2, v___x_4945_);
lean_ctor_set(v___x_4946_, 3, v_opts_4943_);
v___x_4947_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
lean_ctor_set(v___x_4947_, 1, v_msgData_4934_);
v___x_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_4949_, v___y_4950_);
lean_dec(v___y_4950_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_4953_, lean_object* v_macroStack_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v_scopes_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v_opts_4961_; lean_object* v___x_4962_; uint8_t v___x_4963_; 
v___x_4957_ = lean_st_ref_get(v___y_4955_);
v_scopes_4958_ = lean_ctor_get(v___x_4957_, 2);
lean_inc(v_scopes_4958_);
lean_dec(v___x_4957_);
v___x_4959_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4960_ = l_List_head_x21___redArg(v___x_4959_, v_scopes_4958_);
lean_dec(v_scopes_4958_);
v_opts_4961_ = lean_ctor_get(v___x_4960_, 1);
lean_inc_ref(v_opts_4961_);
lean_dec(v___x_4960_);
v___x_4962_ = l_Lean_Elab_pp_macroStack;
v___x_4963_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_4961_, v___x_4962_);
lean_dec_ref(v_opts_4961_);
if (v___x_4963_ == 0)
{
lean_object* v___x_4964_; 
lean_dec(v_macroStack_4954_);
v___x_4964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4964_, 0, v_msgData_4953_);
return v___x_4964_;
}
else
{
if (lean_obj_tag(v_macroStack_4954_) == 0)
{
lean_object* v___x_4965_; 
v___x_4965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4965_, 0, v_msgData_4953_);
return v___x_4965_;
}
else
{
lean_object* v_head_4966_; lean_object* v_after_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4982_; 
v_head_4966_ = lean_ctor_get(v_macroStack_4954_, 0);
lean_inc(v_head_4966_);
v_after_4967_ = lean_ctor_get(v_head_4966_, 1);
v_isSharedCheck_4982_ = !lean_is_exclusive(v_head_4966_);
if (v_isSharedCheck_4982_ == 0)
{
lean_object* v_unused_4983_; 
v_unused_4983_ = lean_ctor_get(v_head_4966_, 0);
lean_dec(v_unused_4983_);
v___x_4969_ = v_head_4966_;
v_isShared_4970_ = v_isSharedCheck_4982_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_after_4967_);
lean_dec(v_head_4966_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4982_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4971_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 7);
lean_ctor_set(v___x_4969_, 1, v___x_4971_);
lean_ctor_set(v___x_4969_, 0, v_msgData_4953_);
v___x_4973_ = v___x_4969_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_msgData_4953_);
lean_ctor_set(v_reuseFailAlloc_4981_, 1, v___x_4971_);
v___x_4973_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v_msgData_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4974_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_4975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4973_);
lean_ctor_set(v___x_4975_, 1, v___x_4974_);
v___x_4976_ = l_Lean_MessageData_ofSyntax(v_after_4967_);
v___x_4977_ = l_Lean_indentD(v___x_4976_);
v_msgData_4978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4978_, 0, v___x_4975_);
lean_ctor_set(v_msgData_4978_, 1, v___x_4977_);
v___x_4979_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_4978_, v_macroStack_4954_);
v___x_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4979_);
return v___x_4980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_4984_, lean_object* v_macroStack_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_4984_, v_macroStack_4985_, v___y_4986_);
lean_dec(v___y_4986_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v___x_4993_; 
v___x_4993_ = l_Lean_Elab_Command_getRef___redArg(v___y_4990_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v_macroStack_4995_; lean_object* v___x_4996_; lean_object* v_a_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5008_; 
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___x_4993_, 1);
v_macroStack_4995_ = lean_ctor_get(v___y_4990_, 4);
v___x_4996_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_4989_, v___y_4991_);
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
lean_inc(v_a_4997_);
lean_dec_ref(v___x_4996_);
v___x_4998_ = l_Lean_Elab_getBetterRef(v_a_4994_, v_macroStack_4995_);
lean_dec(v_a_4994_);
lean_inc(v_macroStack_4995_);
v___x_4999_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_4997_, v_macroStack_4995_, v___y_4991_);
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5002_ = v___x_4999_;
v_isShared_5003_ = v_isSharedCheck_5008_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4999_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5008_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5004_; lean_object* v___x_5006_; 
v___x_5004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5004_, 0, v___x_4998_);
lean_ctor_set(v___x_5004_, 1, v_a_5000_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set_tag(v___x_5002_, 1);
lean_ctor_set(v___x_5002_, 0, v___x_5004_);
v___x_5006_ = v___x_5002_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
lean_dec_ref(v_msg_4989_);
v_a_5009_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v___x_4993_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_4993_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5017_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v___x_5026_; lean_object* v_env_5027_; lean_object* v___x_5028_; 
v___x_5026_ = lean_st_ref_get(v___y_5024_);
v_env_5027_ = lean_ctor_get(v___x_5026_, 0);
lean_inc_ref(v_env_5027_);
lean_dec(v___x_5026_);
lean_inc(v_constName_5022_);
v___x_5028_ = l_Lean_isInductiveCore_x3f(v_env_5027_, v_constName_5022_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v___x_5029_; uint8_t v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5029_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5030_ = 0;
v___x_5031_ = l_Lean_MessageData_ofConstName(v_constName_5022_, v___x_5030_);
v___x_5032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5029_);
lean_ctor_set(v___x_5032_, 1, v___x_5031_);
v___x_5033_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5032_);
lean_ctor_set(v___x_5034_, 1, v___x_5033_);
v___x_5035_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5034_, v___y_5023_, v___y_5024_);
return v___x_5035_;
}
else
{
lean_object* v_val_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
lean_dec(v_constName_5022_);
v_val_5036_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v___x_5028_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_val_5036_);
lean_dec(v___x_5028_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
lean_ctor_set_tag(v___x_5038_, 0);
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_val_5036_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v_res_5048_; 
v_res_5048_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5044_, v___y_5045_, v___y_5046_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
return v_res_5048_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5051_ = l_Lean_stringToMessageData(v___x_5050_);
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v___x_5059_; 
lean_inc(v_declName_5052_);
v___x_5059_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5060_; uint8_t v___x_5061_; lean_object* v___x_5062_; 
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
lean_inc(v_a_5060_);
lean_dec_ref_known(v___x_5059_, 1);
v___x_5061_ = 0;
lean_inc(v_declName_5052_);
v___x_5062_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5060_, v_declName_5052_, v___x_5061_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; uint8_t v___x_5064_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref_known(v___x_5062_, 1);
v___x_5064_ = lean_unbox(v_a_5063_);
lean_dec(v_a_5063_);
if (v___x_5064_ == 0)
{
uint8_t v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = 1;
lean_inc(v_declName_5052_);
v___x_5066_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5060_, v_declName_5052_, v___x_5065_, v___y_5053_, v___y_5054_);
lean_dec(v_a_5060_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; uint8_t v___x_5068_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5066_, 1);
v___x_5068_ = lean_unbox(v_a_5067_);
lean_dec(v_a_5067_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5069_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5070_ = l_Lean_MessageData_ofConstName(v_declName_5052_, v___x_5061_);
v___x_5071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5069_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5071_);
lean_ctor_set(v___x_5073_, 1, v___x_5072_);
v___x_5074_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5073_, v___y_5053_, v___y_5054_);
return v___x_5074_;
}
else
{
lean_dec(v_declName_5052_);
goto v___jp_5056_;
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
lean_dec(v_declName_5052_);
v_a_5075_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_5066_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5066_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
else
{
lean_dec(v_a_5060_);
lean_dec(v_declName_5052_);
goto v___jp_5056_;
}
}
else
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5090_; 
lean_dec(v_a_5060_);
lean_dec(v_declName_5052_);
v_a_5083_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_5062_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5062_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5086_ == 0)
{
v___x_5088_ = v___x_5085_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5083_);
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
else
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
lean_dec(v_declName_5052_);
v_a_5091_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5093_ = v___x_5059_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5059_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5096_; 
if (v_isShared_5094_ == 0)
{
v___x_5096_ = v___x_5093_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
v___jp_5056_:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5057_ = lean_box(0);
v___x_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
return v___x_5058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_){
_start:
{
lean_object* v_res_5103_; 
v_res_5103_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5099_, v___y_5100_, v___y_5101_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_){
_start:
{
lean_object* v___f_5108_; lean_object* v___x_5109_; 
lean_inc(v_declName_5104_);
v___f_5108_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5108_, 0, v_declName_5104_);
v___x_5109_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5104_, v___f_5108_, v_a_5105_, v_a_5106_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5110_, v_a_5111_, v_a_5112_);
lean_dec(v_a_5112_);
lean_dec_ref(v_a_5111_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5115_, uint8_t v_addHypotheses_5116_, lean_object* v_as_5117_, lean_object* v_as_x27_5118_, lean_object* v_b_5119_, lean_object* v_a_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5115_, v_addHypotheses_5116_, v_as_x27_5118_, v_b_5119_, v___y_5121_, v___y_5122_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5125_, lean_object* v_addHypotheses_5126_, lean_object* v_as_5127_, lean_object* v_as_x27_5128_, lean_object* v_b_5129_, lean_object* v_a_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
uint8_t v_addHypotheses_boxed_5134_; lean_object* v_res_5135_; 
v_addHypotheses_boxed_5134_ = lean_unbox(v_addHypotheses_5126_);
v_res_5135_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5125_, v_addHypotheses_boxed_5134_, v_as_5127_, v_as_x27_5128_, v_b_5129_, v_a_5130_, v___y_5131_, v___y_5132_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
lean_dec(v_as_x27_5128_);
lean_dec(v_as_5127_);
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5136_, v___y_5138_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5141_, v___y_5142_, v___y_5143_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5146_, lean_object* v_msg_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
lean_object* v___x_5151_; 
v___x_5151_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5147_, v___y_5148_, v___y_5149_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5152_, lean_object* v_msg_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5152_, v_msg_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5158_, lean_object* v_macroStack_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
lean_object* v___x_5163_; 
v___x_5163_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5158_, v_macroStack_5159_, v___y_5161_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5164_, lean_object* v_macroStack_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_){
_start:
{
lean_object* v_res_5169_; 
v_res_5169_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5164_, v_macroStack_5165_, v___y_5166_, v___y_5167_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v___x_5173_; lean_object* v_env_5174_; uint8_t v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; 
v___x_5173_ = lean_st_ref_get(v___y_5171_);
v_env_5174_ = lean_ctor_get(v___x_5173_, 0);
lean_inc_ref(v_env_5174_);
lean_dec(v___x_5173_);
v___x_5175_ = l_Lean_isInductiveCore(v_env_5174_, v_declName_5170_);
v___x_5176_ = lean_box(v___x_5175_);
v___x_5177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5176_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5178_, v___y_5179_);
lean_dec(v___y_5179_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5182_, v___y_5184_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5187_, v___y_5188_, v___y_5189_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
if (v_____do__lift_5192_ == 0)
{
uint8_t v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5196_ = 1;
v___x_5197_ = lean_box(v___x_5196_);
v___x_5198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
return v___x_5198_;
}
else
{
uint8_t v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5199_ = 0;
v___x_5200_ = lean_box(v___x_5199_);
v___x_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
return v___x_5201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
uint8_t v_____do__lift_1704__boxed_5206_; lean_object* v_res_5207_; 
v_____do__lift_1704__boxed_5206_ = lean_unbox(v_____do__lift_5202_);
v_res_5207_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1704__boxed_5206_, v___y_5203_, v___y_5204_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5208_, size_t v_i_5209_, size_t v_stop_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_){
_start:
{
uint8_t v___x_5214_; 
v___x_5214_ = lean_usize_dec_eq(v_i_5209_, v_stop_5210_);
if (v___x_5214_ == 0)
{
uint8_t v___x_5215_; uint8_t v_a_5217_; lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5215_ = 1;
v___x_5223_ = lean_array_uget_borrowed(v_as_5208_, v_i_5209_);
lean_inc(v___x_5223_);
v___x_5224_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5223_, v___y_5212_);
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5234_; 
v_a_5225_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5227_ = v___x_5224_;
v_isShared_5228_ = v_isSharedCheck_5234_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5224_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5234_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
uint8_t v___x_5229_; 
v___x_5229_ = lean_unbox(v_a_5225_);
lean_dec(v_a_5225_);
if (v___x_5229_ == 0)
{
lean_object* v___x_5230_; lean_object* v___x_5232_; 
v___x_5230_ = lean_box(v___x_5215_);
if (v_isShared_5228_ == 0)
{
lean_ctor_set(v___x_5227_, 0, v___x_5230_);
v___x_5232_ = v___x_5227_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5230_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
else
{
lean_del_object(v___x_5227_);
v_a_5217_ = v___x_5214_;
goto v___jp_5216_;
}
}
}
else
{
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5235_; uint8_t v___x_5236_; 
v_a_5235_ = lean_ctor_get(v___x_5224_, 0);
lean_inc(v_a_5235_);
lean_dec_ref_known(v___x_5224_, 1);
v___x_5236_ = lean_unbox(v_a_5235_);
lean_dec(v_a_5235_);
v_a_5217_ = v___x_5236_;
goto v___jp_5216_;
}
else
{
return v___x_5224_;
}
}
v___jp_5216_:
{
if (v_a_5217_ == 0)
{
size_t v___x_5218_; size_t v___x_5219_; 
v___x_5218_ = ((size_t)1ULL);
v___x_5219_ = lean_usize_add(v_i_5209_, v___x_5218_);
v_i_5209_ = v___x_5219_;
goto _start;
}
else
{
lean_object* v___x_5221_; lean_object* v___x_5222_; 
v___x_5221_ = lean_box(v___x_5215_);
v___x_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5221_);
return v___x_5222_;
}
}
}
else
{
uint8_t v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; 
v___x_5237_ = 0;
v___x_5238_ = lean_box(v___x_5237_);
v___x_5239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5238_);
return v___x_5239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object* v_as_5240_, lean_object* v_i_5241_, lean_object* v_stop_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
size_t v_i_boxed_5246_; size_t v_stop_boxed_5247_; lean_object* v_res_5248_; 
v_i_boxed_5246_ = lean_unbox_usize(v_i_5241_);
lean_dec(v_i_5241_);
v_stop_boxed_5247_ = lean_unbox_usize(v_stop_5242_);
lean_dec(v_stop_5242_);
v_res_5248_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5240_, v_i_boxed_5246_, v_stop_boxed_5247_, v___y_5243_, v___y_5244_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec_ref(v_as_5240_);
return v_res_5248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object* v_as_5249_, size_t v_i_5250_, size_t v_stop_5251_, lean_object* v_b_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
uint8_t v___x_5256_; 
v___x_5256_ = lean_usize_dec_eq(v_i_5250_, v_stop_5251_);
if (v___x_5256_ == 0)
{
lean_object* v___x_5257_; lean_object* v___x_5258_; 
v___x_5257_ = lean_array_uget_borrowed(v_as_5249_, v_i_5250_);
lean_inc(v___x_5257_);
v___x_5258_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v___x_5257_, v___y_5253_, v___y_5254_);
if (lean_obj_tag(v___x_5258_) == 0)
{
lean_object* v_a_5259_; size_t v___x_5260_; size_t v___x_5261_; 
v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
lean_inc(v_a_5259_);
lean_dec_ref_known(v___x_5258_, 1);
v___x_5260_ = ((size_t)1ULL);
v___x_5261_ = lean_usize_add(v_i_5250_, v___x_5260_);
v_i_5250_ = v___x_5261_;
v_b_5252_ = v_a_5259_;
goto _start;
}
else
{
return v___x_5258_;
}
}
else
{
lean_object* v___x_5263_; 
v___x_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5263_, 0, v_b_5252_);
return v___x_5263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object* v_as_5264_, lean_object* v_i_5265_, lean_object* v_stop_5266_, lean_object* v_b_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
size_t v_i_boxed_5271_; size_t v_stop_boxed_5272_; lean_object* v_res_5273_; 
v_i_boxed_5271_ = lean_unbox_usize(v_i_5265_);
lean_dec(v_i_5265_);
v_stop_boxed_5272_ = lean_unbox_usize(v_stop_5266_);
lean_dec(v_stop_5266_);
v_res_5273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5264_, v_i_boxed_5271_, v_stop_boxed_5272_, v_b_5267_, v___y_5268_, v___y_5269_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec_ref(v_as_5264_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object* v_declNames_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_){
_start:
{
uint8_t v___y_5279_; lean_object* v___y_5280_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___y_5316_; uint8_t v___x_5319_; 
v___x_5298_ = lean_unsigned_to_nat(0u);
v___x_5299_ = lean_array_get_size(v_declNames_5274_);
v___x_5319_ = lean_nat_dec_lt(v___x_5298_, v___x_5299_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; 
v___x_5320_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5319_, v_a_5275_, v_a_5276_);
v___y_5316_ = v___x_5320_;
goto v___jp_5315_;
}
else
{
if (v___x_5319_ == 0)
{
goto v___jp_5300_;
}
else
{
size_t v___x_5321_; size_t v___x_5322_; lean_object* v___x_5323_; 
v___x_5321_ = ((size_t)0ULL);
v___x_5322_ = lean_usize_of_nat(v___x_5299_);
v___x_5323_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5274_, v___x_5321_, v___x_5322_, v_a_5275_, v_a_5276_);
if (lean_obj_tag(v___x_5323_) == 0)
{
lean_object* v_a_5324_; uint8_t v___x_5325_; lean_object* v___x_5326_; 
v_a_5324_ = lean_ctor_get(v___x_5323_, 0);
lean_inc(v_a_5324_);
lean_dec_ref_known(v___x_5323_, 1);
v___x_5325_ = lean_unbox(v_a_5324_);
lean_dec(v_a_5324_);
v___x_5326_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5325_, v_a_5275_, v_a_5276_);
v___y_5316_ = v___x_5326_;
goto v___jp_5315_;
}
else
{
v___y_5316_ = v___x_5323_;
goto v___jp_5315_;
}
}
}
v___jp_5278_:
{
if (lean_obj_tag(v___y_5280_) == 0)
{
lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5288_; 
v_isSharedCheck_5288_ = !lean_is_exclusive(v___y_5280_);
if (v_isSharedCheck_5288_ == 0)
{
lean_object* v_unused_5289_; 
v_unused_5289_ = lean_ctor_get(v___y_5280_, 0);
lean_dec(v_unused_5289_);
v___x_5282_ = v___y_5280_;
v_isShared_5283_ = v_isSharedCheck_5288_;
goto v_resetjp_5281_;
}
else
{
lean_dec(v___y_5280_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5288_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5284_; lean_object* v___x_5286_; 
v___x_5284_ = lean_box(v___y_5279_);
if (v_isShared_5283_ == 0)
{
lean_ctor_set(v___x_5282_, 0, v___x_5284_);
v___x_5286_ = v___x_5282_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5284_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
else
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5297_; 
v_a_5290_ = lean_ctor_get(v___y_5280_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___y_5280_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5292_ = v___y_5280_;
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___y_5280_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5295_; 
if (v_isShared_5293_ == 0)
{
v___x_5295_ = v___x_5292_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
v___jp_5300_:
{
uint8_t v___x_5301_; uint8_t v___x_5302_; 
v___x_5301_ = 1;
v___x_5302_ = lean_nat_dec_lt(v___x_5298_, v___x_5299_);
if (v___x_5302_ == 0)
{
lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5303_ = lean_box(v___x_5301_);
v___x_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5304_, 0, v___x_5303_);
return v___x_5304_;
}
else
{
lean_object* v___x_5305_; uint8_t v___x_5306_; 
v___x_5305_ = lean_box(0);
v___x_5306_ = lean_nat_dec_le(v___x_5299_, v___x_5299_);
if (v___x_5306_ == 0)
{
if (v___x_5302_ == 0)
{
lean_object* v___x_5307_; lean_object* v___x_5308_; 
v___x_5307_ = lean_box(v___x_5301_);
v___x_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5307_);
return v___x_5308_;
}
else
{
size_t v___x_5309_; size_t v___x_5310_; lean_object* v___x_5311_; 
v___x_5309_ = ((size_t)0ULL);
v___x_5310_ = lean_usize_of_nat(v___x_5299_);
v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5274_, v___x_5309_, v___x_5310_, v___x_5305_, v_a_5275_, v_a_5276_);
v___y_5279_ = v___x_5301_;
v___y_5280_ = v___x_5311_;
goto v___jp_5278_;
}
}
else
{
size_t v___x_5312_; size_t v___x_5313_; lean_object* v___x_5314_; 
v___x_5312_ = ((size_t)0ULL);
v___x_5313_ = lean_usize_of_nat(v___x_5299_);
v___x_5314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5274_, v___x_5312_, v___x_5313_, v___x_5305_, v_a_5275_, v_a_5276_);
v___y_5279_ = v___x_5301_;
v___y_5280_ = v___x_5314_;
goto v___jp_5278_;
}
}
}
v___jp_5315_:
{
if (lean_obj_tag(v___y_5316_) == 0)
{
lean_object* v_a_5317_; uint8_t v___x_5318_; 
v_a_5317_ = lean_ctor_get(v___y_5316_, 0);
v___x_5318_ = lean_unbox(v_a_5317_);
if (v___x_5318_ == 0)
{
return v___y_5316_;
}
else
{
lean_dec_ref_known(v___y_5316_, 1);
goto v___jp_5300_;
}
}
else
{
return v___y_5316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5327_, v_a_5328_, v_a_5329_);
lean_dec(v_a_5329_);
lean_dec_ref(v_a_5328_);
lean_dec_ref(v_declNames_5327_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5396_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5397_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5398_ = l_Lean_Elab_registerDerivingHandler(v___x_5396_, v___x_5397_);
if (lean_obj_tag(v___x_5398_) == 0)
{
lean_object* v___x_5399_; uint8_t v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
lean_dec_ref_known(v___x_5398_, 1);
v___x_5399_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5400_ = 0;
v___x_5401_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5402_ = l_Lean_registerTraceClass(v___x_5399_, v___x_5400_, v___x_5401_);
return v___x_5402_;
}
else
{
return v___x_5398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5404_;
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
