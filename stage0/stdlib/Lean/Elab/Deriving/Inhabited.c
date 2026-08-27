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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
v___x_494_ = lean_nat_add(v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec(v___y_492_);
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
lean_ctor_set(v___x_474_, 3, v___y_491_);
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
lean_ctor_set(v_reuseFailAlloc_499_, 3, v___y_491_);
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
v___y_491_ = v___x_505_;
v___y_492_ = v___x_506_;
v___y_493_ = v_size_507_;
goto v___jp_490_;
}
else
{
lean_object* v___x_508_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___y_491_ = v___x_505_;
v___y_492_ = v___x_506_;
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
v___x_632_ = lean_nat_add(v___y_629_, v___y_631_);
lean_dec(v___y_631_);
lean_dec(v___y_629_);
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
lean_ctor_set(v___x_612_, 3, v___y_630_);
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
lean_ctor_set(v_reuseFailAlloc_637_, 3, v___y_630_);
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
v___y_629_ = v___x_645_;
v___y_630_ = v___x_644_;
v___y_631_ = v_size_646_;
goto v___jp_628_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___y_629_ = v___x_645_;
v___y_630_ = v___x_644_;
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
uint8_t v___x_6828__boxed_1047_; lean_object* v_res_1048_; 
v___x_6828__boxed_1047_ = lean_unbox(v___x_1044_);
v_res_1048_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts___lam__1(v_usedInstIdxs_1041_, v___f_1042_, v_e_1043_, v___x_6828__boxed_1047_, v_x_1045_);
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
lean_object* v_ks_2244_; lean_object* v_vs_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2263_; 
v_ks_2244_ = lean_ctor_get(v_x_2193_, 0);
v_vs_2245_ = lean_ctor_get(v_x_2193_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_x_2193_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2247_ = v_x_2193_;
v_isShared_2248_ = v_isSharedCheck_2263_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_vs_2245_);
lean_inc(v_ks_2244_);
lean_dec(v_x_2193_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2263_;
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
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_ks_2244_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_vs_2245_);
v___x_2250_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v_newNode_2251_; size_t v___x_2252_; uint8_t v___x_2253_; 
v_newNode_2251_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v___x_2250_, v_x_2196_, v_x_2197_);
v___x_2252_ = ((size_t)7ULL);
v___x_2253_ = lean_usize_dec_le(v___x_2252_, v_x_2195_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2254_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2251_);
v___x_2255_ = lean_unsigned_to_nat(4u);
v___x_2256_ = lean_nat_dec_lt(v___x_2254_, v___x_2255_);
lean_dec(v___x_2254_);
if (v___x_2256_ == 0)
{
lean_object* v_ks_2257_; lean_object* v_vs_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_ks_2257_ = lean_ctor_get(v_newNode_2251_, 0);
lean_inc_ref(v_ks_2257_);
v_vs_2258_ = lean_ctor_get(v_newNode_2251_, 1);
lean_inc_ref(v_vs_2258_);
lean_dec_ref(v_newNode_2251_);
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_2261_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_x_2195_, v_ks_2257_, v_vs_2258_, v___x_2259_, v___x_2260_);
lean_dec_ref(v_vs_2258_);
lean_dec_ref(v_ks_2257_);
return v___x_2261_;
}
else
{
return v_newNode_2251_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(size_t v_depth_2264_, lean_object* v_keys_2265_, lean_object* v_vals_2266_, lean_object* v_i_2267_, lean_object* v_entries_2268_){
_start:
{
lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = lean_array_get_size(v_keys_2265_);
v___x_2270_ = lean_nat_dec_lt(v_i_2267_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_dec(v_i_2267_);
return v_entries_2268_;
}
else
{
lean_object* v_k_2271_; lean_object* v_v_2272_; uint64_t v___x_2273_; size_t v_h_2274_; size_t v___x_2275_; lean_object* v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; size_t v___x_2279_; size_t v_h_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_k_2271_ = lean_array_fget_borrowed(v_keys_2265_, v_i_2267_);
v_v_2272_ = lean_array_fget_borrowed(v_vals_2266_, v_i_2267_);
v___x_2273_ = l_Lean_instHashableMVarId_hash(v_k_2271_);
v_h_2274_ = lean_uint64_to_usize(v___x_2273_);
v___x_2275_ = ((size_t)5ULL);
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_sub(v_depth_2264_, v___x_2277_);
v___x_2279_ = lean_usize_mul(v___x_2275_, v___x_2278_);
v_h_2280_ = lean_usize_shift_right(v_h_2274_, v___x_2279_);
v___x_2281_ = lean_nat_add(v_i_2267_, v___x_2276_);
lean_dec(v_i_2267_);
lean_inc(v_v_2272_);
lean_inc(v_k_2271_);
v___x_2282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_entries_2268_, v_h_2280_, v_depth_2264_, v_k_2271_, v_v_2272_);
v_i_2267_ = v___x_2281_;
v_entries_2268_ = v___x_2282_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg___boxed(lean_object* v_depth_2284_, lean_object* v_keys_2285_, lean_object* v_vals_2286_, lean_object* v_i_2287_, lean_object* v_entries_2288_){
_start:
{
size_t v_depth_boxed_2289_; lean_object* v_res_2290_; 
v_depth_boxed_2289_ = lean_unbox_usize(v_depth_2284_);
lean_dec(v_depth_2284_);
v_res_2290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_boxed_2289_, v_keys_2285_, v_vals_2286_, v_i_2287_, v_entries_2288_);
lean_dec_ref(v_vals_2286_);
lean_dec_ref(v_keys_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_){
_start:
{
size_t v_x_17316__boxed_2296_; size_t v_x_17317__boxed_2297_; lean_object* v_res_2298_; 
v_x_17316__boxed_2296_ = lean_unbox_usize(v_x_2292_);
lean_dec(v_x_2292_);
v_x_17317__boxed_2297_ = lean_unbox_usize(v_x_2293_);
lean_dec(v_x_2293_);
v_res_2298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2291_, v_x_17316__boxed_2296_, v_x_17317__boxed_2297_, v_x_2294_, v_x_2295_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(lean_object* v_x_2299_, lean_object* v_x_2300_, lean_object* v_x_2301_){
_start:
{
uint64_t v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; 
v___x_2302_ = l_Lean_instHashableMVarId_hash(v_x_2300_);
v___x_2303_ = lean_uint64_to_usize(v___x_2302_);
v___x_2304_ = ((size_t)1ULL);
v___x_2305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2299_, v___x_2303_, v___x_2304_, v_x_2300_, v_x_2301_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(lean_object* v_mvarId_2306_, lean_object* v_val_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v_mctx_2311_; lean_object* v_cache_2312_; lean_object* v_zetaDeltaFVarIds_2313_; lean_object* v_postponed_2314_; lean_object* v_diag_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2344_; 
v___x_2310_ = lean_st_ref_take(v___y_2308_);
v_mctx_2311_ = lean_ctor_get(v___x_2310_, 0);
v_cache_2312_ = lean_ctor_get(v___x_2310_, 1);
v_zetaDeltaFVarIds_2313_ = lean_ctor_get(v___x_2310_, 2);
v_postponed_2314_ = lean_ctor_get(v___x_2310_, 3);
v_diag_2315_ = lean_ctor_get(v___x_2310_, 4);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2317_ = v___x_2310_;
v_isShared_2318_ = v_isSharedCheck_2344_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_diag_2315_);
lean_inc(v_postponed_2314_);
lean_inc(v_zetaDeltaFVarIds_2313_);
lean_inc(v_cache_2312_);
lean_inc(v_mctx_2311_);
lean_dec(v___x_2310_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2344_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v_depth_2319_; lean_object* v_levelAssignDepth_2320_; lean_object* v_lmvarCounter_2321_; lean_object* v_mvarCounter_2322_; lean_object* v_lDecls_2323_; lean_object* v_decls_2324_; lean_object* v_userNames_2325_; lean_object* v_lAssignment_2326_; lean_object* v_eAssignment_2327_; lean_object* v_dAssignment_2328_; lean_object* v_instanceTypedMVars_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2343_; 
v_depth_2319_ = lean_ctor_get(v_mctx_2311_, 0);
v_levelAssignDepth_2320_ = lean_ctor_get(v_mctx_2311_, 1);
v_lmvarCounter_2321_ = lean_ctor_get(v_mctx_2311_, 2);
v_mvarCounter_2322_ = lean_ctor_get(v_mctx_2311_, 3);
v_lDecls_2323_ = lean_ctor_get(v_mctx_2311_, 4);
v_decls_2324_ = lean_ctor_get(v_mctx_2311_, 5);
v_userNames_2325_ = lean_ctor_get(v_mctx_2311_, 6);
v_lAssignment_2326_ = lean_ctor_get(v_mctx_2311_, 7);
v_eAssignment_2327_ = lean_ctor_get(v_mctx_2311_, 8);
v_dAssignment_2328_ = lean_ctor_get(v_mctx_2311_, 9);
v_instanceTypedMVars_2329_ = lean_ctor_get(v_mctx_2311_, 10);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_mctx_2311_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2331_ = v_mctx_2311_;
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_instanceTypedMVars_2329_);
lean_inc(v_dAssignment_2328_);
lean_inc(v_eAssignment_2327_);
lean_inc(v_lAssignment_2326_);
lean_inc(v_userNames_2325_);
lean_inc(v_decls_2324_);
lean_inc(v_lDecls_2323_);
lean_inc(v_mvarCounter_2322_);
lean_inc(v_lmvarCounter_2321_);
lean_inc(v_levelAssignDepth_2320_);
lean_inc(v_depth_2319_);
lean_dec(v_mctx_2311_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_eAssignment_2327_, v_mvarId_2306_, v_val_2307_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 8, v___x_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_depth_2319_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_levelAssignDepth_2320_);
lean_ctor_set(v_reuseFailAlloc_2342_, 2, v_lmvarCounter_2321_);
lean_ctor_set(v_reuseFailAlloc_2342_, 3, v_mvarCounter_2322_);
lean_ctor_set(v_reuseFailAlloc_2342_, 4, v_lDecls_2323_);
lean_ctor_set(v_reuseFailAlloc_2342_, 5, v_decls_2324_);
lean_ctor_set(v_reuseFailAlloc_2342_, 6, v_userNames_2325_);
lean_ctor_set(v_reuseFailAlloc_2342_, 7, v_lAssignment_2326_);
lean_ctor_set(v_reuseFailAlloc_2342_, 8, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2342_, 9, v_dAssignment_2328_);
lean_ctor_set(v_reuseFailAlloc_2342_, 10, v_instanceTypedMVars_2329_);
v___x_2335_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2335_);
v___x_2337_ = v___x_2317_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_cache_2312_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_zetaDeltaFVarIds_2313_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_postponed_2314_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_diag_2315_);
v___x_2337_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = lean_st_ref_put(v___y_2308_, v___x_2337_);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
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
size_t v_x_17538__boxed_2387_; uint8_t v_res_2388_; lean_object* v_r_2389_; 
v_x_17538__boxed_2387_ = lean_unbox_usize(v_x_2385_);
lean_dec(v_x_2385_);
v_res_2388_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2384_, v_x_17538__boxed_2387_, v_x_2386_);
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
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2595_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2595_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2595_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_unbox(v_a_2426_);
lean_dec(v_a_2426_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
lean_del_object(v___x_2428_);
lean_inc(v___x_2417_);
v___x_2431_ = l_Lean_MVarId_getType(v___x_2417_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_options_2432_; uint8_t v_hasTrace_2433_; 
v_options_2432_ = lean_ctor_get(v___y_2422_, 2);
v_hasTrace_2433_ = lean_ctor_get_uint8(v_options_2432_, sizeof(void*)*1);
if (v_hasTrace_2433_ == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2435_; 
v_a_2434_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2431_, 1);
v___x_2435_ = l_Lean_Meta_mkDefault(v_a_2434_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2417_, v_a_2436_, v___y_2421_);
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
lean_dec(v___x_2417_);
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
lean_object* v_a_2455_; lean_object* v_inheritedTraceOptions_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v_a_2465_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v_a_2480_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v_a_2485_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v_a_2496_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v_a_2508_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v_a_2513_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; 
v_a_2455_ = lean_ctor_get(v___x_2431_, 0);
lean_inc_n(v_a_2455_, 2);
lean_dec_ref_known(v___x_2431_, 1);
v_inheritedTraceOptions_2456_ = lean_ctor_get(v___y_2422_, 13);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2457_, 0, v_a_2455_);
v___x_2458_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_2459_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_2460_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_2461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2456_, v_options_2432_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = l_Lean_trace_profiler;
v___x_2557_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2432_, v___x_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
lean_dec_ref(v___f_2457_);
v___x_2558_ = l_Lean_Meta_mkDefault(v_a_2455_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_n(v_a_2559_, 2);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2417_, v_a_2559_, v___y_2421_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2573_; 
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v___x_2560_, 0);
lean_dec(v_unused_2574_);
v___x_2562_ = v___x_2560_;
v_isShared_2563_ = v_isSharedCheck_2573_;
goto v_resetjp_2561_;
}
else
{
lean_dec(v___x_2560_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2573_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
if (v___x_2461_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
lean_dec(v_a_2559_);
v___x_2564_ = lean_box(0);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2564_);
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_del_object(v___x_2562_);
v___x_2568_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2569_ = lean_unsigned_to_nat(30u);
v___x_2570_ = l_Lean_inlineExprTrailing(v_a_2559_, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2568_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2458_, v___x_2571_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2572_;
}
}
}
else
{
lean_dec(v_a_2559_);
return v___x_2560_;
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec(v___x_2417_);
v_a_2575_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2558_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2558_);
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
goto v___jp_2521_;
}
}
else
{
goto v___jp_2521_;
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
v___x_2476_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2458_, v_hasTrace_2433_, v___x_2459_, v_options_2432_, v___x_2461_, v___y_2463_, v___f_2457_, v___x_2475_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
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
if (lean_obj_tag(v___y_2490_) == 0)
{
lean_object* v_a_2491_; 
v_a_2491_ = lean_ctor_get(v___y_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___y_2490_, 1);
v___y_2483_ = v___y_2488_;
v___y_2484_ = v___y_2489_;
v_a_2485_ = v_a_2491_;
goto v___jp_2482_;
}
else
{
lean_object* v_a_2492_; 
v_a_2492_ = lean_ctor_get(v___y_2490_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___y_2490_, 1);
v___y_2478_ = v___y_2488_;
v___y_2479_ = v___y_2489_;
v_a_2480_ = v_a_2492_;
goto v___jp_2477_;
}
}
v___jp_2493_:
{
lean_object* v___x_2497_; double v___x_2498_; double v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2497_ = lean_io_get_num_heartbeats();
v___x_2498_ = lean_float_of_nat(v___y_2495_);
v___x_2499_ = lean_float_of_nat(v___x_2497_);
v___x_2500_ = lean_box_float(v___x_2498_);
v___x_2501_ = lean_box_float(v___x_2499_);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2496_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3(v___x_2458_, v_hasTrace_2433_, v___x_2459_, v_options_2432_, v___x_2461_, v___y_2494_, v___f_2457_, v___x_2503_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2504_;
}
v___jp_2505_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_a_2508_);
v___y_2494_ = v___y_2506_;
v___y_2495_ = v___y_2507_;
v_a_2496_ = v___x_2509_;
goto v___jp_2493_;
}
v___jp_2510_:
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_a_2513_);
v___y_2494_ = v___y_2511_;
v___y_2495_ = v___y_2512_;
v_a_2496_ = v___x_2514_;
goto v___jp_2493_;
}
v___jp_2515_:
{
if (lean_obj_tag(v___y_2518_) == 0)
{
lean_object* v_a_2519_; 
v_a_2519_ = lean_ctor_get(v___y_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___y_2518_, 1);
v___y_2511_ = v___y_2516_;
v___y_2512_ = v___y_2517_;
v_a_2513_ = v_a_2519_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2520_; 
v_a_2520_ = lean_ctor_get(v___y_2518_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___y_2518_, 1);
v___y_2506_ = v___y_2516_;
v___y_2507_ = v___y_2517_;
v_a_2508_ = v_a_2520_;
goto v___jp_2505_;
}
}
v___jp_2521_:
{
lean_object* v___x_2522_; 
v___x_2522_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_2423_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2522_, 1);
v___x_2524_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2525_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_2432_, v___x_2524_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_io_mono_nanos_now();
v___x_2527_ = l_Lean_Meta_mkDefault(v_a_2455_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc_n(v_a_2528_, 2);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2417_, v_a_2528_, v___y_2421_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_dec_ref_known(v___x_2529_, 1);
if (v___x_2461_ == 0)
{
lean_object* v___x_2530_; 
lean_dec(v_a_2528_);
v___x_2530_ = lean_box(0);
v___y_2483_ = v_a_2523_;
v___y_2484_ = v___x_2526_;
v_a_2485_ = v___x_2530_;
goto v___jp_2482_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2532_ = lean_unsigned_to_nat(30u);
v___x_2533_ = l_Lean_inlineExprTrailing(v_a_2528_, v___x_2532_);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2531_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2458_, v___x_2534_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
v___y_2488_ = v_a_2523_;
v___y_2489_ = v___x_2526_;
v___y_2490_ = v___x_2535_;
goto v___jp_2487_;
}
}
else
{
lean_dec(v_a_2528_);
v___y_2488_ = v_a_2523_;
v___y_2489_ = v___x_2526_;
v___y_2490_ = v___x_2529_;
goto v___jp_2487_;
}
}
else
{
lean_object* v_a_2536_; 
lean_dec(v___x_2417_);
v_a_2536_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2527_, 1);
v___y_2478_ = v_a_2523_;
v___y_2479_ = v___x_2526_;
v_a_2480_ = v_a_2536_;
goto v___jp_2477_;
}
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_io_get_num_heartbeats();
v___x_2538_ = l_Lean_Meta_mkDefault(v_a_2455_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc_n(v_a_2539_, 2);
lean_dec_ref_known(v___x_2538_, 1);
v___x_2540_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v___x_2417_, v_a_2539_, v___y_2421_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_dec_ref_known(v___x_2540_, 1);
if (v___x_2461_ == 0)
{
lean_object* v___x_2541_; 
lean_dec(v_a_2539_);
v___x_2541_ = lean_box(0);
v___y_2511_ = v_a_2523_;
v___y_2512_ = v___x_2537_;
v_a_2513_ = v___x_2541_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2542_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__2);
v___x_2543_ = lean_unsigned_to_nat(30u);
v___x_2544_ = l_Lean_inlineExprTrailing(v_a_2539_, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2542_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_2458_, v___x_2545_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
v___y_2516_ = v_a_2523_;
v___y_2517_ = v___x_2537_;
v___y_2518_ = v___x_2546_;
goto v___jp_2515_;
}
}
else
{
lean_dec(v_a_2539_);
v___y_2516_ = v_a_2523_;
v___y_2517_ = v___x_2537_;
v___y_2518_ = v___x_2540_;
goto v___jp_2515_;
}
}
else
{
lean_object* v_a_2547_; 
lean_dec(v___x_2417_);
v_a_2547_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2538_, 1);
v___y_2506_ = v_a_2523_;
v___y_2507_ = v___x_2537_;
v_a_2508_ = v_a_2547_;
goto v___jp_2505_;
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec_ref(v___f_2457_);
lean_dec(v_a_2455_);
lean_dec(v___x_2417_);
v_a_2548_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2522_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2522_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec(v___x_2417_);
v_a_2583_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2431_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2431_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_dec(v___x_2417_);
v___x_2591_ = lean_box(0);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2591_);
v___x_2593_ = v___x_2428_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v___x_2417_);
v_a_2596_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2425_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2425_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed(lean_object* v___x_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1(v___x_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(lean_object* v_as_2613_, size_t v_i_2614_, size_t v_stop_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = lean_usize_dec_eq(v_i_2614_, v_stop_2615_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_array_uget_borrowed(v_as_2613_, v_i_2614_);
lean_inc_n(v___x_2625_, 2);
v___f_2626_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___boxed), 8, 1);
lean_closure_set(v___f_2626_, 0, v___x_2625_);
v___x_2627_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__4___redArg(v___x_2625_, v___f_2626_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; size_t v___x_2629_; size_t v___x_2630_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = ((size_t)1ULL);
v___x_2630_ = lean_usize_add(v_i_2614_, v___x_2629_);
v_i_2614_ = v___x_2630_;
v_b_2616_ = v_a_2628_;
goto _start;
}
else
{
return v___x_2627_;
}
}
else
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_b_2616_);
return v___x_2632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___boxed(lean_object* v_as_2633_, lean_object* v_i_2634_, lean_object* v_stop_2635_, lean_object* v_b_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
size_t v_i_boxed_2644_; size_t v_stop_boxed_2645_; lean_object* v_res_2646_; 
v_i_boxed_2644_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_stop_boxed_2645_ = lean_unbox_usize(v_stop_2635_);
lean_dec(v_stop_2635_);
v_res_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_as_2633_, v_i_boxed_2644_, v_stop_boxed_2645_, v_b_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec_ref(v_as_2633_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(lean_object* v_e_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Meta_getMVarsNoDelayed(v_e_2647_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2677_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2677_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2677_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2660_ = lean_unsigned_to_nat(0u);
v___x_2661_ = lean_array_get_size(v_a_2656_);
v___x_2662_ = lean_box(0);
v___x_2663_ = lean_nat_dec_lt(v___x_2660_, v___x_2661_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2665_; 
lean_dec(v_a_2656_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2662_);
v___x_2665_ = v___x_2658_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2662_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
else
{
uint8_t v___x_2667_; 
v___x_2667_ = lean_nat_dec_le(v___x_2661_, v___x_2661_);
if (v___x_2667_ == 0)
{
if (v___x_2663_ == 0)
{
lean_object* v___x_2669_; 
lean_dec(v_a_2656_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2662_);
v___x_2669_ = v___x_2658_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2662_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
else
{
size_t v___x_2671_; size_t v___x_2672_; lean_object* v___x_2673_; 
lean_del_object(v___x_2658_);
v___x_2671_ = ((size_t)0ULL);
v___x_2672_ = lean_usize_of_nat(v___x_2661_);
v___x_2673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2656_, v___x_2671_, v___x_2672_, v___x_2662_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
lean_dec(v_a_2656_);
return v___x_2673_;
}
}
else
{
size_t v___x_2674_; size_t v___x_2675_; lean_object* v___x_2676_; 
lean_del_object(v___x_2658_);
v___x_2674_ = ((size_t)0ULL);
v___x_2675_ = lean_usize_of_nat(v___x_2661_);
v___x_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5(v_a_2656_, v___x_2674_, v___x_2675_, v___x_2662_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_);
lean_dec(v_a_2656_);
return v___x_2676_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_a_2678_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2655_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2655_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault___boxed(lean_object* v_e_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_e_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(lean_object* v_mvarId_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___redArg(v_mvarId_2695_, v___y_2699_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0___boxed(lean_object* v_mvarId_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0(v_mvarId_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v_mvarId_2704_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(lean_object* v_mvarId_2713_, lean_object* v_val_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___redArg(v_mvarId_2713_, v_val_2714_, v___y_2718_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1___boxed(lean_object* v_mvarId_2723_, lean_object* v_val_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1(v_mvarId_2723_, v_val_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(lean_object* v_00_u03b1_2733_, lean_object* v_x_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_x_2734_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6(v_00_u03b1_2743_, v_x_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2752_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(lean_object* v_00_u03b2_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
uint8_t v___x_2756_; 
v___x_2756_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___redArg(v_x_2754_, v_x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_){
_start:
{
uint8_t v_res_2760_; lean_object* v_r_2761_; 
v_res_2760_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0(v_00_u03b2_2757_, v_x_2758_, v_x_2759_);
lean_dec(v_x_2759_);
lean_dec_ref(v_x_2758_);
v_r_2761_ = lean_box(v_res_2760_);
return v_r_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2(lean_object* v_00_u03b2_2762_, lean_object* v_x_2763_, lean_object* v_x_2764_, lean_object* v_x_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2___redArg(v_x_2763_, v_x_2764_, v_x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(lean_object* v_oldTraces_2767_, lean_object* v_data_2768_, lean_object* v_ref_2769_, lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_2767_, v_data_2768_, v_ref_2769_, v_msg_2770_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___boxed(lean_object* v_oldTraces_2779_, lean_object* v_data_2780_, lean_object* v_ref_2781_, lean_object* v_msg_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5(v_oldTraces_2779_, v_data_2780_, v_ref_2781_, v_msg_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
return v_res_2790_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2791_, lean_object* v_x_2792_, size_t v_x_2793_, lean_object* v_x_2794_){
_start:
{
uint8_t v___x_2795_; 
v___x_2795_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___redArg(v_x_2792_, v_x_2793_, v_x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2796_, lean_object* v_x_2797_, lean_object* v_x_2798_, lean_object* v_x_2799_){
_start:
{
size_t v_x_18237__boxed_2800_; uint8_t v_res_2801_; lean_object* v_r_2802_; 
v_x_18237__boxed_2800_ = lean_unbox_usize(v_x_2798_);
lean_dec(v_x_2798_);
v_res_2801_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3(v_00_u03b2_2796_, v_x_2797_, v_x_18237__boxed_2800_, v_x_2799_);
lean_dec(v_x_2799_);
lean_dec_ref(v_x_2797_);
v_r_2802_ = lean_box(v_res_2801_);
return v_r_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2803_, lean_object* v_x_2804_, size_t v_x_2805_, size_t v_x_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___redArg(v_x_2804_, v_x_2805_, v_x_2806_, v_x_2807_, v_x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_){
_start:
{
size_t v_x_18248__boxed_2816_; size_t v_x_18249__boxed_2817_; lean_object* v_res_2818_; 
v_x_18248__boxed_2816_ = lean_unbox_usize(v_x_2812_);
lean_dec(v_x_2812_);
v_x_18249__boxed_2817_ = lean_unbox_usize(v_x_2813_);
lean_dec(v_x_2813_);
v_res_2818_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6(v_00_u03b2_2810_, v_x_2811_, v_x_18248__boxed_2816_, v_x_18249__boxed_2817_, v_x_2814_, v_x_2815_);
return v_res_2818_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_2819_, lean_object* v_keys_2820_, lean_object* v_vals_2821_, lean_object* v_heq_2822_, lean_object* v_i_2823_, lean_object* v_k_2824_){
_start:
{
uint8_t v___x_2825_; 
v___x_2825_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___redArg(v_keys_2820_, v_i_2823_, v_k_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_2826_, lean_object* v_keys_2827_, lean_object* v_vals_2828_, lean_object* v_heq_2829_, lean_object* v_i_2830_, lean_object* v_k_2831_){
_start:
{
uint8_t v_res_2832_; lean_object* v_r_2833_; 
v_res_2832_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_2826_, v_keys_2827_, v_vals_2828_, v_heq_2829_, v_i_2830_, v_k_2831_);
lean_dec(v_k_2831_);
lean_dec_ref(v_vals_2828_);
lean_dec_ref(v_keys_2827_);
v_r_2833_ = lean_box(v_res_2832_);
return v_r_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_2834_, lean_object* v_n_2835_, lean_object* v_k_2836_, lean_object* v_v_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13___redArg(v_n_2835_, v_k_2836_, v_v_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(lean_object* v_00_u03b2_2839_, size_t v_depth_2840_, lean_object* v_keys_2841_, lean_object* v_vals_2842_, lean_object* v_heq_2843_, lean_object* v_i_2844_, lean_object* v_entries_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___redArg(v_depth_2840_, v_keys_2841_, v_vals_2842_, v_i_2844_, v_entries_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14___boxed(lean_object* v_00_u03b2_2847_, lean_object* v_depth_2848_, lean_object* v_keys_2849_, lean_object* v_vals_2850_, lean_object* v_heq_2851_, lean_object* v_i_2852_, lean_object* v_entries_2853_){
_start:
{
size_t v_depth_boxed_2854_; lean_object* v_res_2855_; 
v_depth_boxed_2854_ = lean_unbox_usize(v_depth_2848_);
lean_dec(v_depth_2848_);
v_res_2855_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__14(v_00_u03b2_2847_, v_depth_boxed_2854_, v_keys_2849_, v_vals_2850_, v_heq_2851_, v_i_2852_, v_entries_2853_);
lean_dec_ref(v_vals_2850_);
lean_dec_ref(v_keys_2849_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_2856_, lean_object* v_x_2857_, lean_object* v_x_2858_, lean_object* v_x_2859_, lean_object* v_x_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__1_spec__2_spec__6_spec__13_spec__15___redArg(v_x_2857_, v_x_2858_, v_x_2859_, v_x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(lean_object* v_e_2862_, lean_object* v___y_2863_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = l_Lean_Expr_hasMVar(v_e_2862_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_e_2862_);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; lean_object* v_mctx_2868_; lean_object* v___x_2869_; lean_object* v_fst_2870_; lean_object* v_snd_2871_; lean_object* v___x_2872_; lean_object* v_cache_2873_; lean_object* v_zetaDeltaFVarIds_2874_; lean_object* v_postponed_2875_; lean_object* v_diag_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2885_; 
v___x_2867_ = lean_st_ref_get(v___y_2863_);
v_mctx_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc_ref(v_mctx_2868_);
lean_dec(v___x_2867_);
v___x_2869_ = l_Lean_instantiateMVarsCore(v_mctx_2868_, v_e_2862_);
v_fst_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_fst_2870_);
v_snd_2871_ = lean_ctor_get(v___x_2869_, 1);
lean_inc(v_snd_2871_);
lean_dec_ref(v___x_2869_);
v___x_2872_ = lean_st_ref_take(v___y_2863_);
v_cache_2873_ = lean_ctor_get(v___x_2872_, 1);
v_zetaDeltaFVarIds_2874_ = lean_ctor_get(v___x_2872_, 2);
v_postponed_2875_ = lean_ctor_get(v___x_2872_, 3);
v_diag_2876_ = lean_ctor_get(v___x_2872_, 4);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2885_ == 0)
{
lean_object* v_unused_2886_; 
v_unused_2886_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2886_);
v___x_2878_ = v___x_2872_;
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_diag_2876_);
lean_inc(v_postponed_2875_);
lean_inc(v_zetaDeltaFVarIds_2874_);
lean_inc(v_cache_2873_);
lean_dec(v___x_2872_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v_snd_2871_);
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_snd_2871_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_cache_2873_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_zetaDeltaFVarIds_2874_);
lean_ctor_set(v_reuseFailAlloc_2884_, 3, v_postponed_2875_);
lean_ctor_set(v_reuseFailAlloc_2884_, 4, v_diag_2876_);
v___x_2881_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_st_ref_put(v___y_2863_, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_fst_2870_);
return v___x_2883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg___boxed(lean_object* v_e_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2887_, v___y_2888_);
lean_dec(v___y_2888_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(lean_object* v_e_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_e_2891_, v___y_2895_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___boxed(lean_object* v_e_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1(v_e_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
return v_res_2908_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(lean_object* v_msg_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_21060__overap_2919_; lean_object* v___x_2920_; 
v___x_2918_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___closed__0);
v___x_21060__overap_2919_ = lean_panic_fn_borrowed(v___x_2918_, v_msg_2910_);
lean_inc(v___y_2916_);
lean_inc_ref(v___y_2915_);
lean_inc(v___y_2914_);
lean_inc_ref(v___y_2913_);
lean_inc(v___y_2912_);
lean_inc_ref(v___y_2911_);
v___x_2920_ = lean_apply_7(v___x_21060__overap_2919_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, lean_box(0));
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2___boxed(lean_object* v_msg_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v_msg_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(lean_object* v_a_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg___boxed(lean_object* v_a_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___redArg(v_a_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(lean_object* v_00_u03b1_2948_, lean_object* v_a_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6___boxed(lean_object* v_00_u03b1_2958_, lean_object* v_a_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__6(v_00_u03b1_2958_, v_a_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(lean_object* v_k_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v_b_2971_, lean_object* v_c_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; 
lean_inc(v___y_2976_);
lean_inc_ref(v___y_2975_);
lean_inc(v___y_2974_);
lean_inc_ref(v___y_2973_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
v___x_2978_ = lean_apply_9(v_k_2968_, v_b_2971_, v_c_2972_, v___y_2969_, v___y_2970_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, lean_box(0));
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed(lean_object* v_k_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v_b_2982_, lean_object* v_c_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0(v_k_2979_, v___y_2980_, v___y_2981_, v_b_2982_, v_c_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(lean_object* v_type_2990_, lean_object* v_k_2991_, uint8_t v_cleanupAnnotations_2992_, uint8_t v_whnfType_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___f_3001_; lean_object* v___x_3002_; 
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2994_);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3001_, 0, v_k_2991_);
lean_closure_set(v___f_3001_, 1, v___y_2994_);
lean_closure_set(v___f_3001_, 2, v___y_2995_);
v___x_3002_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2990_, v___f_3001_, v_cleanupAnnotations_2992_, v_whnfType_2993_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3002_) == 0)
{
return v___x_3002_;
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg___boxed(lean_object* v_type_3011_, lean_object* v_k_3012_, lean_object* v_cleanupAnnotations_3013_, lean_object* v_whnfType_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3022_; uint8_t v_whnfType_boxed_3023_; lean_object* v_res_3024_; 
v_cleanupAnnotations_boxed_3022_ = lean_unbox(v_cleanupAnnotations_3013_);
v_whnfType_boxed_3023_ = lean_unbox(v_whnfType_3014_);
v_res_3024_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3011_, v_k_3012_, v_cleanupAnnotations_boxed_3022_, v_whnfType_boxed_3023_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(lean_object* v_00_u03b1_3025_, lean_object* v_type_3026_, lean_object* v_k_3027_, uint8_t v_cleanupAnnotations_3028_, uint8_t v_whnfType_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_3026_, v_k_3027_, v_cleanupAnnotations_3028_, v_whnfType_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___boxed(lean_object* v_00_u03b1_3038_, lean_object* v_type_3039_, lean_object* v_k_3040_, lean_object* v_cleanupAnnotations_3041_, lean_object* v_whnfType_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3050_; uint8_t v_whnfType_boxed_3051_; lean_object* v_res_3052_; 
v_cleanupAnnotations_boxed_3050_ = lean_unbox(v_cleanupAnnotations_3041_);
v_whnfType_boxed_3051_ = lean_unbox(v_whnfType_3042_);
v_res_3052_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8(v_00_u03b1_3038_, v_type_3039_, v_k_3040_, v_cleanupAnnotations_boxed_3050_, v_whnfType_boxed_3051_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3052_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__0));
v___x_3055_ = l_Lean_stringToMessageData(v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___closed__1);
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0___boxed(lean_object* v_x_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__0(v_x_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v_x_3066_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(lean_object* v___x_3075_, lean_object* v_fst_3076_, lean_object* v_____r_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = l_Lean_mkAppN(v___x_3075_, v_fst_3076_);
v___x_3086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1___boxed(lean_object* v___x_3087_, lean_object* v_fst_3088_, lean_object* v_____r_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3087_, v_fst_3088_, v_____r_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v_fst_3088_);
return v_res_3097_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__0));
v___x_3100_ = l_Lean_stringToMessageData(v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(lean_object* v_ctorName_3101_, uint8_t v___x_3102_, lean_object* v_x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3111_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___closed__1);
v___x_3112_ = l_Lean_MessageData_ofConstName(v_ctorName_3101_, v___x_3102_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3113_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed(lean_object* v_ctorName_3117_, lean_object* v___x_3118_, lean_object* v_x_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
uint8_t v___x_25944__boxed_3127_; lean_object* v_res_3128_; 
v___x_25944__boxed_3127_ = lean_unbox(v___x_3118_);
v_res_3128_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2(v_ctorName_3117_, v___x_25944__boxed_3127_, v_x_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec_ref(v_x_3119_);
return v_res_3128_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(lean_object* v_e_3129_){
_start:
{
if (lean_obj_tag(v_e_3129_) == 0)
{
uint8_t v___x_3130_; 
v___x_3130_ = 2;
return v___x_3130_;
}
else
{
lean_object* v_a_3131_; uint8_t v___x_3132_; 
v_a_3131_ = lean_ctor_get(v_e_3129_, 0);
v___x_3132_ = l_Lean_Expr_hasSyntheticSorry(v_a_3131_);
if (v___x_3132_ == 0)
{
uint8_t v___x_3133_; 
v___x_3133_ = 0;
return v___x_3133_;
}
else
{
uint8_t v___x_3134_; 
v___x_3134_ = 1;
return v___x_3134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5___boxed(lean_object* v_e_3135_){
_start:
{
uint8_t v_res_3136_; lean_object* v_r_3137_; 
v_res_3136_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_e_3135_);
lean_dec_ref(v_e_3135_);
v_r_3137_ = lean_box(v_res_3136_);
return v_r_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(lean_object* v_cls_3138_, uint8_t v_collapsed_3139_, lean_object* v_tag_3140_, lean_object* v_opts_3141_, uint8_t v_clsEnabled_3142_, lean_object* v_oldTraces_3143_, lean_object* v_msg_3144_, lean_object* v_resStartStop_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_fst_3153_; lean_object* v_snd_3154_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v_data_3158_; lean_object* v_fst_3169_; lean_object* v_snd_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; lean_object* v___y_3174_; lean_object* v_a_3175_; uint8_t v___y_3190_; double v___y_3221_; 
v_fst_3153_ = lean_ctor_get(v_resStartStop_3145_, 0);
lean_inc(v_fst_3153_);
v_snd_3154_ = lean_ctor_get(v_resStartStop_3145_, 1);
lean_inc(v_snd_3154_);
lean_dec_ref(v_resStartStop_3145_);
v_fst_3169_ = lean_ctor_get(v_snd_3154_, 0);
lean_inc(v_fst_3169_);
v_snd_3170_ = lean_ctor_get(v_snd_3154_, 1);
lean_inc(v_snd_3170_);
lean_dec(v_snd_3154_);
v___x_3171_ = l_Lean_trace_profiler;
v___x_3172_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3141_, v___x_3171_);
if (v___x_3172_ == 0)
{
v___y_3190_ = v___x_3172_;
goto v___jp_3189_;
}
else
{
lean_object* v___x_3226_; uint8_t v___x_3227_; 
v___x_3226_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3227_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_3141_, v___x_3226_);
if (v___x_3227_ == 0)
{
lean_object* v___x_3228_; lean_object* v___x_3229_; double v___x_3230_; double v___x_3231_; double v___x_3232_; 
v___x_3228_ = l_Lean_trace_profiler_threshold;
v___x_3229_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3141_, v___x_3228_);
v___x_3230_ = lean_float_of_nat(v___x_3229_);
v___x_3231_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__2);
v___x_3232_ = lean_float_div(v___x_3230_, v___x_3231_);
v___y_3221_ = v___x_3232_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; double v___x_3235_; 
v___x_3233_ = l_Lean_trace_profiler_threshold;
v___x_3234_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__8(v_opts_3141_, v___x_3233_);
v___x_3235_ = lean_float_of_nat(v___x_3234_);
v___y_3221_ = v___x_3235_;
goto v___jp_3220_;
}
}
v___jp_3155_:
{
lean_object* v___x_3159_; 
lean_inc(v___y_3156_);
v___x_3159_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__5___redArg(v_oldTraces_3143_, v_data_3158_, v___y_3156_, v___y_3157_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v___x_3160_; 
lean_dec_ref_known(v___x_3159_, 1);
v___x_3160_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3153_);
return v___x_3160_;
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_fst_3153_);
v_a_3161_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3159_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3159_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
v___jp_3173_:
{
uint8_t v_result_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; double v___x_3179_; lean_object* v_data_3180_; 
v_result_3176_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5_spec__5(v_fst_3153_);
v___x_3177_ = lean_box(v_result_3176_);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
v___x_3179_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3140_);
lean_inc_ref(v___x_3178_);
lean_inc(v_cls_3138_);
v_data_3180_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3180_, 0, v_cls_3138_);
lean_ctor_set(v_data_3180_, 1, v___x_3178_);
lean_ctor_set(v_data_3180_, 2, v_tag_3140_);
lean_ctor_set_float(v_data_3180_, sizeof(void*)*3, v___x_3179_);
lean_ctor_set_float(v_data_3180_, sizeof(void*)*3 + 8, v___x_3179_);
lean_ctor_set_uint8(v_data_3180_, sizeof(void*)*3 + 16, v_collapsed_3139_);
if (v___x_3172_ == 0)
{
lean_dec_ref_known(v___x_3178_, 1);
lean_dec(v_snd_3170_);
lean_dec(v_fst_3169_);
lean_dec_ref(v_tag_3140_);
lean_dec(v_cls_3138_);
v___y_3156_ = v___y_3174_;
v___y_3157_ = v_a_3175_;
v_data_3158_ = v_data_3180_;
goto v___jp_3155_;
}
else
{
lean_object* v_data_3181_; double v___x_3182_; double v___x_3183_; 
lean_dec_ref_known(v_data_3180_, 3);
v_data_3181_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3181_, 0, v_cls_3138_);
lean_ctor_set(v_data_3181_, 1, v___x_3178_);
lean_ctor_set(v_data_3181_, 2, v_tag_3140_);
v___x_3182_ = lean_unbox_float(v_fst_3169_);
lean_dec(v_fst_3169_);
lean_ctor_set_float(v_data_3181_, sizeof(void*)*3, v___x_3182_);
v___x_3183_ = lean_unbox_float(v_snd_3170_);
lean_dec(v_snd_3170_);
lean_ctor_set_float(v_data_3181_, sizeof(void*)*3 + 8, v___x_3183_);
lean_ctor_set_uint8(v_data_3181_, sizeof(void*)*3 + 16, v_collapsed_3139_);
v___y_3156_ = v___y_3174_;
v___y_3157_ = v_a_3175_;
v_data_3158_ = v_data_3181_;
goto v___jp_3155_;
}
}
v___jp_3184_:
{
lean_object* v_ref_3185_; lean_object* v___x_3186_; 
v_ref_3185_ = lean_ctor_get(v___y_3150_, 5);
lean_inc(v___y_3151_);
lean_inc_ref(v___y_3150_);
lean_inc(v___y_3149_);
lean_inc_ref(v___y_3148_);
lean_inc(v___y_3147_);
lean_inc_ref(v___y_3146_);
lean_inc(v_fst_3153_);
v___x_3186_ = lean_apply_8(v_msg_3144_, v_fst_3153_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, lean_box(0));
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3186_, 1);
v___y_3174_ = v_ref_3185_;
v_a_3175_ = v_a_3187_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3188_; 
lean_dec_ref_known(v___x_3186_, 1);
v___x_3188_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3___closed__1);
v___y_3174_ = v_ref_3185_;
v_a_3175_ = v___x_3188_;
goto v___jp_3173_;
}
}
v___jp_3189_:
{
if (v_clsEnabled_3142_ == 0)
{
if (v___y_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v_traceState_3192_; lean_object* v_env_3193_; lean_object* v_nextMacroScope_3194_; lean_object* v_ngen_3195_; lean_object* v_auxDeclNGen_3196_; lean_object* v_cache_3197_; lean_object* v_messages_3198_; lean_object* v_infoState_3199_; lean_object* v_snapshotTasks_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v_snd_3170_);
lean_dec(v_fst_3169_);
lean_dec_ref(v_msg_3144_);
lean_dec_ref(v_tag_3140_);
lean_dec(v_cls_3138_);
v___x_3191_ = lean_st_ref_take(v___y_3151_);
v_traceState_3192_ = lean_ctor_get(v___x_3191_, 4);
v_env_3193_ = lean_ctor_get(v___x_3191_, 0);
v_nextMacroScope_3194_ = lean_ctor_get(v___x_3191_, 1);
v_ngen_3195_ = lean_ctor_get(v___x_3191_, 2);
v_auxDeclNGen_3196_ = lean_ctor_get(v___x_3191_, 3);
v_cache_3197_ = lean_ctor_get(v___x_3191_, 5);
v_messages_3198_ = lean_ctor_get(v___x_3191_, 6);
v_infoState_3199_ = lean_ctor_get(v___x_3191_, 7);
v_snapshotTasks_3200_ = lean_ctor_get(v___x_3191_, 8);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3202_ = v___x_3191_;
v_isShared_3203_ = v_isSharedCheck_3219_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snapshotTasks_3200_);
lean_inc(v_infoState_3199_);
lean_inc(v_messages_3198_);
lean_inc(v_cache_3197_);
lean_inc(v_traceState_3192_);
lean_inc(v_auxDeclNGen_3196_);
lean_inc(v_ngen_3195_);
lean_inc(v_nextMacroScope_3194_);
lean_inc(v_env_3193_);
lean_dec(v___x_3191_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3219_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
uint64_t v_tid_3204_; lean_object* v_traces_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3218_; 
v_tid_3204_ = lean_ctor_get_uint64(v_traceState_3192_, sizeof(void*)*1);
v_traces_3205_ = lean_ctor_get(v_traceState_3192_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_traceState_3192_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3207_ = v_traceState_3192_;
v_isShared_3208_ = v_isSharedCheck_3218_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_traces_3205_);
lean_dec(v_traceState_3192_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3218_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3209_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3143_, v_traces_3205_);
lean_dec_ref(v_traces_3205_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3209_);
v___x_3211_ = v___x_3207_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3209_);
lean_ctor_set_uint64(v_reuseFailAlloc_3217_, sizeof(void*)*1, v_tid_3204_);
v___x_3211_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3213_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 4, v___x_3211_);
v___x_3213_ = v___x_3202_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_env_3193_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_nextMacroScope_3194_);
lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_ngen_3195_);
lean_ctor_set(v_reuseFailAlloc_3216_, 3, v_auxDeclNGen_3196_);
lean_ctor_set(v_reuseFailAlloc_3216_, 4, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3216_, 5, v_cache_3197_);
lean_ctor_set(v_reuseFailAlloc_3216_, 6, v_messages_3198_);
lean_ctor_set(v_reuseFailAlloc_3216_, 7, v_infoState_3199_);
lean_ctor_set(v_reuseFailAlloc_3216_, 8, v_snapshotTasks_3200_);
v___x_3213_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = lean_st_ref_put(v___y_3151_, v___x_3213_);
v___x_3215_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__3_spec__6___redArg(v_fst_3153_);
return v___x_3215_;
}
}
}
}
}
else
{
goto v___jp_3184_;
}
}
else
{
goto v___jp_3184_;
}
}
v___jp_3220_:
{
double v___x_3222_; double v___x_3223_; double v___x_3224_; uint8_t v___x_3225_; 
v___x_3222_ = lean_unbox_float(v_snd_3170_);
v___x_3223_ = lean_unbox_float(v_fst_3169_);
v___x_3224_ = lean_float_sub(v___x_3222_, v___x_3223_);
v___x_3225_ = lean_float_decLt(v___y_3221_, v___x_3224_);
v___y_3190_ = v___x_3225_;
goto v___jp_3189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5___boxed(lean_object* v_cls_3236_, lean_object* v_collapsed_3237_, lean_object* v_tag_3238_, lean_object* v_opts_3239_, lean_object* v_clsEnabled_3240_, lean_object* v_oldTraces_3241_, lean_object* v_msg_3242_, lean_object* v_resStartStop_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_collapsed_boxed_3251_; uint8_t v_clsEnabled_boxed_3252_; lean_object* v_res_3253_; 
v_collapsed_boxed_3251_ = lean_unbox(v_collapsed_3237_);
v_clsEnabled_boxed_3252_ = lean_unbox(v_clsEnabled_3240_);
v_res_3253_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v_cls_3236_, v_collapsed_boxed_3251_, v_tag_3238_, v_opts_3239_, v_clsEnabled_boxed_3252_, v_oldTraces_3241_, v_msg_3242_, v_resStartStop_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v_opts_3239_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(lean_object* v___x_3254_, lean_object* v_as_3255_, size_t v_i_3256_, size_t v_stop_3257_, lean_object* v_b_3258_){
_start:
{
lean_object* v___y_3260_; uint8_t v___x_3264_; 
v___x_3264_ = lean_usize_dec_eq(v_i_3256_, v_stop_3257_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3265_ = lean_array_uget_borrowed(v_as_3255_, v_i_3256_);
v___x_3266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts_spec__3_spec__3_spec__5_spec__6___redArg(v___x_3254_, v___x_3265_);
if (v___x_3266_ == 0)
{
v___y_3260_ = v_b_3258_;
goto v___jp_3259_;
}
else
{
lean_object* v___x_3267_; 
lean_inc(v___x_3265_);
v___x_3267_ = lean_array_push(v_b_3258_, v___x_3265_);
v___y_3260_ = v___x_3267_;
goto v___jp_3259_;
}
}
else
{
return v_b_3258_;
}
v___jp_3259_:
{
size_t v___x_3261_; size_t v___x_3262_; 
v___x_3261_ = ((size_t)1ULL);
v___x_3262_ = lean_usize_add(v_i_3256_, v___x_3261_);
v_i_3256_ = v___x_3262_;
v_b_3258_ = v___y_3260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4___boxed(lean_object* v___x_3268_, lean_object* v_as_3269_, lean_object* v_i_3270_, lean_object* v_stop_3271_, lean_object* v_b_3272_){
_start:
{
size_t v_i_boxed_3273_; size_t v_stop_boxed_3274_; lean_object* v_res_3275_; 
v_i_boxed_3273_ = lean_unbox_usize(v_i_3270_);
lean_dec(v_i_3270_);
v_stop_boxed_3274_ = lean_unbox_usize(v_stop_3271_);
lean_dec(v_stop_3271_);
v_res_3275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v___x_3268_, v_as_3269_, v_i_boxed_3273_, v_stop_boxed_3274_, v_b_3272_);
lean_dec_ref(v_as_3269_);
lean_dec_ref(v___x_3268_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
if (lean_obj_tag(v_a_3276_) == 0)
{
lean_object* v___x_3278_; 
v___x_3278_ = l_List_reverse___redArg(v_a_3277_);
return v___x_3278_;
}
else
{
lean_object* v_head_3279_; lean_object* v_tail_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3289_; 
v_head_3279_ = lean_ctor_get(v_a_3276_, 0);
v_tail_3280_ = lean_ctor_get(v_a_3276_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_a_3276_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3282_ = v_a_3276_;
v_isShared_3283_ = v_isSharedCheck_3289_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_tail_3280_);
lean_inc(v_head_3279_);
lean_dec(v_a_3276_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3289_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3284_ = l_Lean_MessageData_ofExpr(v_head_3279_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 1, v_a_3277_);
lean_ctor_set(v___x_3282_, 0, v___x_3284_);
v___x_3286_ = v___x_3282_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_a_3277_);
v___x_3286_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
v_a_3276_ = v_tail_3280_;
v_a_3277_ = v___x_3286_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3293_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__2));
v___x_3294_ = lean_unsigned_to_nat(6u);
v___x_3295_ = lean_unsigned_to_nat(108u);
v___x_3296_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__1));
v___x_3297_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__0));
v___x_3298_ = l_mkPanicMessageWithDecl(v___x_3297_, v___x_3296_, v___x_3295_, v___x_3294_, v___x_3293_);
return v___x_3298_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__4));
v___x_3301_ = l_Lean_stringToMessageData(v___x_3300_);
return v___x_3301_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__6));
v___x_3304_ = l_Lean_stringToMessageData(v___x_3303_);
return v___x_3304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__8));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_unsigned_to_nat(16u);
v___x_3312_ = lean_mk_array(v___x_3311_, v___x_3310_);
return v___x_3312_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__12));
v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__14));
v___x_3318_ = l_Lean_stringToMessageData(v___x_3317_);
return v___x_3318_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__16));
v___x_3321_ = l_Lean_stringToMessageData(v___x_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(lean_object* v_inductiveTypeName_3329_, lean_object* v_us_3330_, lean_object* v_xs_3331_, lean_object* v___x_3332_, lean_object* v___x_3333_, lean_object* v_ctorName_3334_, lean_object* v___x_3335_, lean_object* v___f_3336_, lean_object* v_insts_3337_, lean_object* v_localInst2Index_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v___x_3346_; lean_object* v_env_3347_; lean_object* v___x_3348_; lean_object* v_type_3349_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint8_t v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v_val_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3518_; lean_object* v___y_3529_; uint8_t v___x_3539_; uint8_t v___x_3540_; 
v___x_3346_ = lean_st_ref_get(v___y_3344_);
v_env_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc_ref(v_env_3347_);
lean_dec(v___x_3346_);
lean_inc(v_us_3330_);
lean_inc(v_inductiveTypeName_3329_);
v___x_3348_ = l_Lean_Expr_const___override(v_inductiveTypeName_3329_, v_us_3330_);
v_type_3349_ = l_Lean_mkAppN(v___x_3348_, v_xs_3331_);
v___x_3539_ = l_Lean_isStructure(v_env_3347_, v_inductiveTypeName_3329_);
v___x_3540_ = 1;
if (v___x_3539_ == 0)
{
lean_object* v_options_3541_; lean_object* v_inheritedTraceOptions_3542_; uint8_t v_hasTrace_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec_ref(v___f_3336_);
v_options_3541_ = lean_ctor_get(v___y_3343_, 2);
v_inheritedTraceOptions_3542_ = lean_ctor_get(v___y_3343_, 13);
v_hasTrace_3543_ = lean_ctor_get_uint8(v_options_3541_, sizeof(void*)*1);
lean_inc(v_ctorName_3334_);
v___x_3544_ = l_Lean_Expr_const___override(v_ctorName_3334_, v_us_3330_);
v___x_3545_ = l_Lean_mkAppN(v___x_3544_, v___x_3335_);
if (v_hasTrace_3543_ == 0)
{
lean_object* v___x_3546_; 
lean_dec(v_ctorName_3334_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
lean_inc_ref(v___x_3545_);
v___x_3546_ = lean_infer_type(v___x_3545_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; lean_object* v___x_3550_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = lean_box(0);
v___x_3549_ = 0;
v___x_3550_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3547_, v___x_3548_, v___x_3549_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v_snd_3552_; lean_object* v_fst_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3596_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v_snd_3552_ = lean_ctor_get(v_a_3551_, 1);
v_fst_3553_ = lean_ctor_get(v_a_3551_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_a_3551_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3555_ = v_a_3551_;
v_isShared_3556_ = v_isSharedCheck_3596_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_snd_3552_);
lean_inc(v_fst_3553_);
lean_dec(v_a_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3596_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v_snd_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3594_; 
v_snd_3557_ = lean_ctor_get(v_snd_3552_, 1);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_snd_3552_);
if (v_isSharedCheck_3594_ == 0)
{
lean_object* v_unused_3595_; 
v_unused_3595_ = lean_ctor_get(v_snd_3552_, 0);
lean_dec(v_unused_3595_);
v___x_3559_ = v_snd_3552_;
v_isShared_3560_ = v_isSharedCheck_3594_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_snd_3557_);
lean_dec(v_snd_3552_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3594_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; 
lean_inc(v_snd_3557_);
lean_inc_ref(v_type_3349_);
v___x_3561_ = l_Lean_Meta_isExprDefEq(v_type_3349_, v_snd_3557_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; uint8_t v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
v___x_3563_ = lean_unbox(v_a_3562_);
lean_dec(v_a_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3567_; 
lean_dec(v_fst_3553_);
lean_dec_ref(v___x_3545_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
v___x_3564_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
v___x_3565_ = l_Lean_indentExpr(v_type_3349_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set_tag(v___x_3559_, 7);
lean_ctor_set(v___x_3559_, 1, v___x_3565_);
lean_ctor_set(v___x_3559_, 0, v___x_3564_);
v___x_3567_ = v___x_3559_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3556_ == 0)
{
lean_ctor_set_tag(v___x_3555_, 7);
lean_ctor_set(v___x_3555_, 1, v___x_3568_);
lean_ctor_set(v___x_3555_, 0, v___x_3567_);
v___x_3570_ = v___x_3555_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
v___x_3571_ = l_Lean_indentExpr(v_snd_3557_);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3572_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
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
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
lean_del_object(v___x_3559_);
lean_dec(v_snd_3557_);
lean_del_object(v___x_3555_);
v___x_3584_ = lean_box(0);
v___x_3585_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3545_, v_fst_3553_, v___x_3584_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v_fst_3553_);
v___y_3518_ = v___x_3585_;
goto v___jp_3517_;
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_del_object(v___x_3559_);
lean_dec(v_snd_3557_);
lean_del_object(v___x_3555_);
lean_dec(v_fst_3553_);
lean_dec_ref(v___x_3545_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
v_a_3586_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3561_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3561_);
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
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v___x_3545_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
v_a_3597_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3550_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3550_);
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
lean_dec_ref(v___x_3545_);
v___y_3518_ = v___x_3546_;
goto v___jp_3517_;
}
}
else
{
lean_object* v___x_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v_a_3614_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v_a_3629_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v_a_3647_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v_a_3659_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; 
v___x_3605_ = lean_box(v___x_3539_);
v___f_3606_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__2___boxed), 10, 2);
lean_closure_set(v___f_3606_, 0, v_ctorName_3334_);
lean_closure_set(v___f_3606_, 1, v___x_3605_);
v___x_3607_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3608_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3609_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3542_, v_options_3541_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3757_ = l_Lean_trace_profiler;
v___x_3758_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3541_, v___x_3757_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; 
lean_dec_ref(v___f_3606_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
lean_inc_ref(v___x_3545_);
v___x_3759_ = lean_infer_type(v___x_3545_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; lean_object* v___x_3763_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = lean_box(0);
v___x_3762_ = 0;
v___x_3763_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3760_, v___x_3761_, v___x_3762_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
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
v___x_3774_ = l_Lean_Meta_isExprDefEq(v_type_3349_, v_snd_3770_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
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
lean_dec_ref(v___x_3545_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
v___x_3777_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
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
v___x_3781_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
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
v___x_3786_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3785_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
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
v___x_3798_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3545_, v_fst_3766_, v___x_3797_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
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
lean_dec_ref(v___x_3545_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
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
lean_dec_ref(v___x_3545_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
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
lean_dec_ref(v___x_3545_);
v___y_3518_ = v___x_3759_;
goto v___jp_3517_;
}
}
else
{
goto v___jp_3674_;
}
}
else
{
goto v___jp_3674_;
}
v___jp_3611_:
{
lean_object* v___x_3615_; double v___x_3616_; double v___x_3617_; double v___x_3618_; double v___x_3619_; double v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3615_ = lean_io_mono_nanos_now();
v___x_3616_ = lean_float_of_nat(v___y_3612_);
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
v___x_3625_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3607_, v___x_3540_, v___x_3608_, v_options_3541_, v___x_3610_, v___y_3613_, v___f_3606_, v___x_3624_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
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
if (lean_obj_tag(v___y_3634_) == 0)
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
else
{
lean_object* v_a_3643_; 
v_a_3643_ = lean_ctor_get(v___y_3634_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___y_3634_, 1);
v___y_3627_ = v___y_3632_;
v___y_3628_ = v___y_3633_;
v_a_3629_ = v_a_3643_;
goto v___jp_3626_;
}
}
v___jp_3644_:
{
lean_object* v___x_3648_; double v___x_3649_; double v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3648_ = lean_io_get_num_heartbeats();
v___x_3649_ = lean_float_of_nat(v___y_3645_);
v___x_3650_ = lean_float_of_nat(v___x_3648_);
v___x_3651_ = lean_box_float(v___x_3649_);
v___x_3652_ = lean_box_float(v___x_3650_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v_a_3647_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3607_, v___x_3540_, v___x_3608_, v_options_3541_, v___x_3610_, v___y_3646_, v___f_3606_, v___x_3654_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v___y_3518_ = v___x_3655_;
goto v___jp_3517_;
}
v___jp_3656_:
{
lean_object* v___x_3660_; 
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v_a_3659_);
v___y_3645_ = v___y_3657_;
v___y_3646_ = v___y_3658_;
v_a_3647_ = v___x_3660_;
goto v___jp_3644_;
}
v___jp_3661_:
{
if (lean_obj_tag(v___y_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___y_3664_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___y_3664_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___y_3664_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___y_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 1);
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v___y_3645_ = v___y_3662_;
v___y_3646_ = v___y_3663_;
v_a_3647_ = v___x_3670_;
goto v___jp_3644_;
}
}
}
else
{
lean_object* v_a_3673_; 
v_a_3673_ = lean_ctor_get(v___y_3664_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___y_3664_, 1);
v___y_3657_ = v___y_3662_;
v___y_3658_ = v___y_3663_;
v_a_3659_ = v_a_3673_;
goto v___jp_3656_;
}
}
v___jp_3674_:
{
lean_object* v___x_3675_; lean_object* v_a_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
v___x_3675_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3344_);
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_a_3676_);
lean_dec_ref(v___x_3675_);
v___x_3677_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3678_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3541_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_io_mono_nanos_now();
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
lean_inc_ref(v___x_3545_);
v___x_3680_ = lean_infer_type(v___x_3545_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; lean_object* v___x_3684_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3680_, 1);
v___x_3682_ = lean_box(0);
v___x_3683_ = 0;
v___x_3684_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3681_, v___x_3682_, v___x_3683_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v_snd_3686_; lean_object* v_fst_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3716_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref_known(v___x_3684_, 1);
v_snd_3686_ = lean_ctor_get(v_a_3685_, 1);
v_fst_3687_ = lean_ctor_get(v_a_3685_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_a_3685_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3689_ = v_a_3685_;
v_isShared_3690_ = v_isSharedCheck_3716_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_snd_3686_);
lean_inc(v_fst_3687_);
lean_dec(v_a_3685_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3716_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v_snd_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3714_; 
v_snd_3691_ = lean_ctor_get(v_snd_3686_, 1);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_snd_3686_);
if (v_isSharedCheck_3714_ == 0)
{
lean_object* v_unused_3715_; 
v_unused_3715_ = lean_ctor_get(v_snd_3686_, 0);
lean_dec(v_unused_3715_);
v___x_3693_ = v_snd_3686_;
v_isShared_3694_ = v_isSharedCheck_3714_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_snd_3691_);
lean_dec(v_snd_3686_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3714_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3695_; 
lean_inc(v_snd_3691_);
lean_inc_ref(v_type_3349_);
v___x_3695_ = l_Lean_Meta_isExprDefEq(v_type_3349_, v_snd_3691_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; uint8_t v___x_3697_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3697_ = lean_unbox(v_a_3696_);
lean_dec(v_a_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
lean_dec(v_fst_3687_);
lean_dec_ref(v___x_3545_);
v___x_3698_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3349_);
v___x_3699_ = l_Lean_indentExpr(v_type_3349_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set_tag(v___x_3693_, 7);
lean_ctor_set(v___x_3693_, 1, v___x_3699_);
lean_ctor_set(v___x_3693_, 0, v___x_3698_);
v___x_3701_ = v___x_3693_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3702_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 7);
lean_ctor_set(v___x_3689_, 1, v___x_3702_);
lean_ctor_set(v___x_3689_, 0, v___x_3701_);
v___x_3704_ = v___x_3689_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3701_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v_a_3708_; 
v___x_3705_ = l_Lean_indentExpr(v_snd_3691_);
v___x_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3704_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3706_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v___x_3707_);
v___y_3627_ = v___x_3679_;
v___y_3628_ = v_a_3676_;
v_a_3629_ = v_a_3708_;
goto v___jp_3626_;
}
}
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_del_object(v___x_3693_);
lean_dec(v_snd_3691_);
lean_del_object(v___x_3689_);
v___x_3711_ = lean_box(0);
v___x_3712_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3545_, v_fst_3687_, v___x_3711_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v_fst_3687_);
v___y_3632_ = v___x_3679_;
v___y_3633_ = v_a_3676_;
v___y_3634_ = v___x_3712_;
goto v___jp_3631_;
}
}
else
{
lean_object* v_a_3713_; 
lean_del_object(v___x_3693_);
lean_dec(v_snd_3691_);
lean_del_object(v___x_3689_);
lean_dec(v_fst_3687_);
lean_dec_ref(v___x_3545_);
v_a_3713_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3695_, 1);
v___y_3627_ = v___x_3679_;
v___y_3628_ = v_a_3676_;
v_a_3629_ = v_a_3713_;
goto v___jp_3626_;
}
}
}
}
else
{
lean_object* v_a_3717_; 
lean_dec_ref(v___x_3545_);
v_a_3717_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3717_);
lean_dec_ref_known(v___x_3684_, 1);
v___y_3627_ = v___x_3679_;
v___y_3628_ = v_a_3676_;
v_a_3629_ = v_a_3717_;
goto v___jp_3626_;
}
}
else
{
lean_dec_ref(v___x_3545_);
v___y_3632_ = v___x_3679_;
v___y_3633_ = v_a_3676_;
v___y_3634_ = v___x_3680_;
goto v___jp_3631_;
}
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
lean_inc_ref(v___x_3545_);
v___x_3719_ = lean_infer_type(v___x_3545_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; lean_object* v___x_3723_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3719_, 1);
v___x_3721_ = lean_box(0);
v___x_3722_ = 0;
v___x_3723_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3720_, v___x_3721_, v___x_3722_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v_snd_3725_; lean_object* v_fst_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3755_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v___x_3723_, 1);
v_snd_3725_ = lean_ctor_get(v_a_3724_, 1);
v_fst_3726_ = lean_ctor_get(v_a_3724_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_a_3724_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3728_ = v_a_3724_;
v_isShared_3729_ = v_isSharedCheck_3755_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_snd_3725_);
lean_inc(v_fst_3726_);
lean_dec(v_a_3724_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3755_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v_snd_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3753_; 
v_snd_3730_ = lean_ctor_get(v_snd_3725_, 1);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_snd_3725_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; 
v_unused_3754_ = lean_ctor_get(v_snd_3725_, 0);
lean_dec(v_unused_3754_);
v___x_3732_ = v_snd_3725_;
v_isShared_3733_ = v_isSharedCheck_3753_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_snd_3730_);
lean_dec(v_snd_3725_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3753_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3734_; 
lean_inc(v_snd_3730_);
lean_inc_ref(v_type_3349_);
v___x_3734_ = l_Lean_Meta_isExprDefEq(v_type_3349_, v_snd_3730_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; uint8_t v___x_3736_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3734_, 1);
v___x_3736_ = lean_unbox(v_a_3735_);
lean_dec(v_a_3735_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
lean_dec(v_fst_3726_);
lean_dec_ref(v___x_3545_);
v___x_3737_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__15);
lean_inc_ref(v_type_3349_);
v___x_3738_ = l_Lean_indentExpr(v_type_3349_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set_tag(v___x_3732_, 7);
lean_ctor_set(v___x_3732_, 1, v___x_3738_);
lean_ctor_set(v___x_3732_, 0, v___x_3737_);
v___x_3740_ = v___x_3732_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; lean_object* v___x_3743_; 
v___x_3741_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__17);
if (v_isShared_3729_ == 0)
{
lean_ctor_set_tag(v___x_3728_, 7);
lean_ctor_set(v___x_3728_, 1, v___x_3741_);
lean_ctor_set(v___x_3728_, 0, v___x_3740_);
v___x_3743_ = v___x_3728_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v_a_3747_; 
v___x_3744_ = l_Lean_indentExpr(v_snd_3730_);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3743_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3745_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref(v___x_3746_);
v___y_3657_ = v___x_3718_;
v___y_3658_ = v_a_3676_;
v_a_3659_ = v_a_3747_;
goto v___jp_3656_;
}
}
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_del_object(v___x_3732_);
lean_dec(v_snd_3730_);
lean_del_object(v___x_3728_);
v___x_3750_ = lean_box(0);
v___x_3751_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__1(v___x_3545_, v_fst_3726_, v___x_3750_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v_fst_3726_);
v___y_3662_ = v___x_3718_;
v___y_3663_ = v_a_3676_;
v___y_3664_ = v___x_3751_;
goto v___jp_3661_;
}
}
else
{
lean_object* v_a_3752_; 
lean_del_object(v___x_3732_);
lean_dec(v_snd_3730_);
lean_del_object(v___x_3728_);
lean_dec(v_fst_3726_);
lean_dec_ref(v___x_3545_);
v_a_3752_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3734_, 1);
v___y_3657_ = v___x_3718_;
v___y_3658_ = v_a_3676_;
v_a_3659_ = v_a_3752_;
goto v___jp_3656_;
}
}
}
}
else
{
lean_object* v_a_3756_; 
lean_dec_ref(v___x_3545_);
v_a_3756_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3723_, 1);
v___y_3657_ = v___x_3718_;
v___y_3658_ = v_a_3676_;
v_a_3659_ = v_a_3756_;
goto v___jp_3656_;
}
}
else
{
lean_dec_ref(v___x_3545_);
v___y_3662_ = v___x_3718_;
v___y_3663_ = v_a_3676_;
v___y_3664_ = v___x_3719_;
goto v___jp_3661_;
}
}
}
}
}
else
{
lean_object* v_options_3818_; uint8_t v_hasTrace_3819_; 
lean_dec(v_ctorName_3334_);
lean_dec(v_us_3330_);
v_options_3818_ = lean_ctor_get(v___y_3343_, 2);
v_hasTrace_3819_ = lean_ctor_get_uint8(v_options_3818_, sizeof(void*)*1);
if (v_hasTrace_3819_ == 0)
{
lean_object* v_ref_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_dec_ref(v___f_3336_);
v_ref_3820_ = lean_ctor_get(v___y_3343_, 5);
v___x_3821_ = l_Lean_SourceInfo_fromRef(v_ref_3820_, v_hasTrace_3819_);
v___x_3822_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3823_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3821_);
v___x_3824_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3821_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = l_Lean_Syntax_node1(v___x_3821_, v___x_3822_, v___x_3824_);
lean_inc_ref(v_type_3349_);
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_type_3349_);
v___x_3827_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3827_, 0, v___x_3825_);
lean_closure_set(v___x_3827_, 1, v___x_3826_);
v___x_3828_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3827_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v___y_3529_ = v___x_3828_;
goto v___jp_3528_;
}
else
{
lean_object* v_ref_3829_; lean_object* v_inheritedTraceOptions_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v_a_3838_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v_a_3853_; 
v_ref_3829_ = lean_ctor_get(v___y_3343_, 5);
v_inheritedTraceOptions_3830_ = lean_ctor_get(v___y_3343_, 13);
v___x_3831_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3832_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg___closed__1));
v___x_3833_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3830_, v_options_3818_, v___x_3833_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3926_ = l_Lean_trace_profiler;
v___x_3927_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3818_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_dec_ref(v___f_3336_);
v___x_3928_ = l_Lean_SourceInfo_fromRef(v_ref_3829_, v___x_3927_);
v___x_3929_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3930_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3928_);
v___x_3931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3928_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = l_Lean_Syntax_node1(v___x_3928_, v___x_3929_, v___x_3931_);
lean_inc_ref(v_type_3349_);
v___x_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3933_, 0, v_type_3349_);
v___x_3934_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3934_, 0, v___x_3932_);
lean_closure_set(v___x_3934_, 1, v___x_3933_);
v___x_3935_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3934_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v___y_3529_ = v___x_3935_;
goto v___jp_3528_;
}
else
{
goto v___jp_3862_;
}
}
else
{
goto v___jp_3862_;
}
v___jp_3835_:
{
lean_object* v___x_3839_; double v___x_3840_; double v___x_3841_; double v___x_3842_; double v___x_3843_; double v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3839_ = lean_io_mono_nanos_now();
v___x_3840_ = lean_float_of_nat(v___y_3836_);
v___x_3841_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__5___lam__1___closed__0);
v___x_3842_ = lean_float_div(v___x_3840_, v___x_3841_);
v___x_3843_ = lean_float_of_nat(v___x_3839_);
v___x_3844_ = lean_float_div(v___x_3843_, v___x_3841_);
v___x_3845_ = lean_box_float(v___x_3842_);
v___x_3846_ = lean_box_float(v___x_3844_);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v_a_3838_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3831_, v___x_3540_, v___x_3832_, v_options_3818_, v___x_3834_, v___y_3837_, v___f_3336_, v___x_3848_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v___y_3529_ = v___x_3849_;
goto v___jp_3528_;
}
v___jp_3850_:
{
lean_object* v___x_3854_; double v___x_3855_; double v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3854_ = lean_io_get_num_heartbeats();
v___x_3855_ = lean_float_of_nat(v___y_3852_);
v___x_3856_ = lean_float_of_nat(v___x_3854_);
v___x_3857_ = lean_box_float(v___x_3855_);
v___x_3858_ = lean_box_float(v___x_3856_);
v___x_3859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3857_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3860_, 0, v_a_3853_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__5(v___x_3831_, v___x_3540_, v___x_3832_, v_options_3818_, v___x_3834_, v___y_3851_, v___f_3336_, v___x_3860_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
v___y_3529_ = v___x_3861_;
goto v___jp_3528_;
}
v___jp_3862_:
{
lean_object* v___x_3863_; lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3925_; 
v___x_3863_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault_spec__2___redArg(v___y_3344_);
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3925_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3925_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3868_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3869_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_options_3818_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
v___x_3870_ = lean_io_mono_nanos_now();
v___x_3871_ = l_Lean_SourceInfo_fromRef(v_ref_3829_, v___x_3869_);
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3873_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3871_);
v___x_3874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3871_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
v___x_3875_ = l_Lean_Syntax_node1(v___x_3871_, v___x_3872_, v___x_3874_);
lean_inc_ref(v_type_3349_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set_tag(v___x_3866_, 1);
lean_ctor_set(v___x_3866_, 0, v_type_3349_);
v___x_3877_ = v___x_3866_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_type_3349_);
v___x_3877_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3878_, 0, v___x_3875_);
lean_closure_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3878_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3879_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set_tag(v___x_3882_, 1);
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
v___y_3836_ = v___x_3870_;
v___y_3837_ = v_a_3864_;
v_a_3838_ = v___x_3885_;
goto v___jp_3835_;
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
v_a_3888_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3879_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3879_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set_tag(v___x_3890_, 0);
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
v___y_3836_ = v___x_3870_;
v___y_3837_ = v_a_3864_;
v_a_3838_ = v___x_3893_;
goto v___jp_3835_;
}
}
}
}
}
else
{
lean_object* v___x_3897_; uint8_t v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3897_ = lean_io_get_num_heartbeats();
v___x_3898_ = 0;
v___x_3899_ = l_Lean_SourceInfo_fromRef(v_ref_3829_, v___x_3898_);
v___x_3900_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__19));
v___x_3901_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__20));
lean_inc(v___x_3899_);
v___x_3902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3899_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = l_Lean_Syntax_node1(v___x_3899_, v___x_3900_, v___x_3902_);
lean_inc_ref(v_type_3349_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set_tag(v___x_3866_, 1);
lean_ctor_set(v___x_3866_, 0, v_type_3349_);
v___x_3905_ = v___x_3866_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_type_3349_);
v___x_3905_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize___boxed), 9, 2);
lean_closure_set(v___x_3906_, 0, v___x_3903_);
lean_closure_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_3906_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3907_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set_tag(v___x_3910_, 1);
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
v___y_3851_ = v_a_3864_;
v___y_3852_ = v___x_3897_;
v_a_3853_ = v___x_3913_;
goto v___jp_3850_;
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
v_a_3916_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3907_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3907_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set_tag(v___x_3918_, 0);
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
v___y_3851_ = v_a_3864_;
v___y_3852_ = v___x_3897_;
v_a_3853_ = v___x_3921_;
goto v___jp_3850_;
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
v___x_3359_ = l_Array_append___redArg(v_xs_3331_, v___y_3352_);
lean_dec_ref(v___y_3352_);
v___x_3360_ = 0;
v___x_3361_ = 1;
v___x_3362_ = l_Lean_Meta_mkForallFVars(v___x_3359_, v_type_3349_, v___x_3360_, v___y_3353_, v___y_3353_, v___x_3361_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = l_Lean_Meta_mkLambdaFVars(v___x_3359_, v___y_3351_, v___x_3360_, v___y_3353_, v___x_3360_, v___y_3353_, v___x_3361_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
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
v___x_3404_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_3401_, v___x_3403_, v___y_3394_, v___y_3397_, v___y_3399_, v___y_3393_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_dec_ref_known(v___x_3404_, 1);
v___y_3351_ = v___y_3392_;
v___y_3352_ = v___y_3396_;
v___y_3353_ = v___y_3398_;
v___y_3354_ = v___y_3400_;
v___y_3355_ = v___y_3394_;
v___y_3356_ = v___y_3397_;
v___y_3357_ = v___y_3399_;
v___y_3358_ = v___y_3393_;
goto v___jp_3350_;
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3396_);
lean_dec_ref(v___y_3392_);
lean_dec_ref(v_type_3349_);
lean_dec_ref(v_xs_3331_);
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
v___x_3425_ = lean_nat_dec_eq(v___y_3422_, v___y_3424_);
lean_dec(v___y_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_dec(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v_type_3349_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
v___x_3426_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__3);
v___x_3427_ = l_panic___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__2(v___x_3426_, v___y_3421_, v___y_3420_, v___y_3416_, v___y_3418_, v___y_3419_, v___y_3415_);
return v___x_3427_;
}
else
{
lean_object* v_options_3428_; uint8_t v_hasTrace_3429_; 
v_options_3428_ = lean_ctor_get(v___y_3419_, 2);
v_hasTrace_3429_ = lean_ctor_get_uint8(v_options_3428_, sizeof(void*)*1);
if (v_hasTrace_3429_ == 0)
{
lean_dec(v___y_3422_);
lean_dec(v___x_3332_);
v___y_3351_ = v___y_3414_;
v___y_3352_ = v___y_3417_;
v___y_3353_ = v___x_3425_;
v___y_3354_ = v___y_3423_;
v___y_3355_ = v___y_3416_;
v___y_3356_ = v___y_3418_;
v___y_3357_ = v___y_3419_;
v___y_3358_ = v___y_3415_;
goto v___jp_3350_;
}
else
{
lean_object* v_inheritedTraceOptions_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v_inheritedTraceOptions_3430_ = lean_ctor_get(v___y_3419_, 13);
v___x_3431_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_3432_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_3433_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3430_, v_options_3428_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_dec(v___y_3422_);
lean_dec(v___x_3332_);
v___y_3351_ = v___y_3414_;
v___y_3352_ = v___y_3417_;
v___y_3353_ = v___x_3425_;
v___y_3354_ = v___y_3423_;
v___y_3355_ = v___y_3416_;
v___y_3356_ = v___y_3418_;
v___y_3357_ = v___y_3419_;
v___y_3358_ = v___y_3415_;
goto v___jp_3350_;
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3434_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__5);
v___x_3435_ = lean_unsigned_to_nat(30u);
lean_inc_ref(v___y_3414_);
v___x_3436_ = l_Lean_inlineExpr(v___y_3414_, v___x_3435_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3434_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = lean_nat_dec_eq(v___y_3422_, v___x_3332_);
lean_dec(v___x_3332_);
lean_dec(v___y_3422_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3439_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__7);
lean_inc_ref(v___y_3417_);
v___x_3440_ = lean_array_to_list(v___y_3417_);
v___x_3441_ = lean_box(0);
v___x_3442_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__3(v___x_3440_, v___x_3441_);
v___x_3443_ = l_Lean_MessageData_ofList(v___x_3442_);
v___x_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3439_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__9);
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3444_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___y_3392_ = v___y_3414_;
v___y_3393_ = v___y_3415_;
v___y_3394_ = v___y_3416_;
v___y_3395_ = v___x_3437_;
v___y_3396_ = v___y_3417_;
v___y_3397_ = v___y_3418_;
v___y_3398_ = v___x_3425_;
v___y_3399_ = v___y_3419_;
v___y_3400_ = v___y_3423_;
v___y_3401_ = v___x_3431_;
v___y_3402_ = v___x_3446_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__10);
v___y_3392_ = v___y_3414_;
v___y_3393_ = v___y_3415_;
v___y_3394_ = v___y_3416_;
v___y_3395_ = v___x_3437_;
v___y_3396_ = v___y_3417_;
v___y_3397_ = v___y_3418_;
v___y_3398_ = v___x_3425_;
v___y_3399_ = v___y_3419_;
v___y_3400_ = v___y_3423_;
v___y_3401_ = v___x_3431_;
v___y_3402_ = v___x_3447_;
goto v___jp_3391_;
}
}
}
}
}
v___jp_3448_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3457_ = lean_box(1);
lean_inc_ref(v___y_3450_);
v___x_3458_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_collectUsedLocalsInsts(v___x_3457_, v_localInst2Index_3338_, v___y_3450_);
v___x_3459_ = lean_array_get_size(v___y_3456_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_size_3460_; 
v_size_3460_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_size_3460_);
v___y_3414_ = v___y_3450_;
v___y_3415_ = v___y_3449_;
v___y_3416_ = v___y_3451_;
v___y_3417_ = v___y_3456_;
v___y_3418_ = v___y_3452_;
v___y_3419_ = v___y_3454_;
v___y_3420_ = v___y_3453_;
v___y_3421_ = v___y_3455_;
v___y_3422_ = v___x_3459_;
v___y_3423_ = v___x_3458_;
v___y_3424_ = v_size_3460_;
goto v___jp_3413_;
}
else
{
lean_inc(v___x_3332_);
v___y_3414_ = v___y_3450_;
v___y_3415_ = v___y_3449_;
v___y_3416_ = v___y_3451_;
v___y_3417_ = v___y_3456_;
v___y_3418_ = v___y_3452_;
v___y_3419_ = v___y_3454_;
v___y_3420_ = v___y_3453_;
v___y_3421_ = v___y_3455_;
v___y_3422_ = v___x_3459_;
v___y_3423_ = v___x_3458_;
v___y_3424_ = v___x_3332_;
goto v___jp_3413_;
}
}
v___jp_3461_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3469_ = lean_array_get_size(v_insts_3337_);
v___x_3470_ = lean_mk_empty_array_with_capacity(v___x_3332_);
v___x_3471_ = lean_nat_dec_lt(v___x_3332_, v___x_3469_);
if (v___x_3471_ == 0)
{
lean_dec(v___x_3333_);
v___y_3449_ = v___y_3468_;
v___y_3450_ = v___y_3462_;
v___y_3451_ = v___y_3465_;
v___y_3452_ = v___y_3466_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3467_;
v___y_3455_ = v___y_3463_;
v___y_3456_ = v___x_3470_;
goto v___jp_3448_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v_visitedExpr_3476_; uint8_t v___x_3477_; 
v___x_3472_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__11);
lean_inc(v___x_3332_);
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3332_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
lean_inc_ref(v___x_3470_);
v___x_3474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3333_);
lean_ctor_set(v___x_3474_, 2, v___x_3470_);
lean_inc_ref(v___y_3462_);
v___x_3475_ = l_Lean_collectFVars(v___x_3474_, v___y_3462_);
v_visitedExpr_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc_ref(v_visitedExpr_3476_);
lean_dec_ref(v___x_3475_);
v___x_3477_ = lean_nat_dec_le(v___x_3469_, v___x_3469_);
if (v___x_3477_ == 0)
{
if (v___x_3471_ == 0)
{
lean_dec_ref(v_visitedExpr_3476_);
v___y_3449_ = v___y_3468_;
v___y_3450_ = v___y_3462_;
v___y_3451_ = v___y_3465_;
v___y_3452_ = v___y_3466_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3467_;
v___y_3455_ = v___y_3463_;
v___y_3456_ = v___x_3470_;
goto v___jp_3448_;
}
else
{
size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = ((size_t)0ULL);
v___x_3479_ = lean_usize_of_nat(v___x_3469_);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3476_, v_insts_3337_, v___x_3478_, v___x_3479_, v___x_3470_);
lean_dec_ref(v_visitedExpr_3476_);
v___y_3449_ = v___y_3468_;
v___y_3450_ = v___y_3462_;
v___y_3451_ = v___y_3465_;
v___y_3452_ = v___y_3466_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3467_;
v___y_3455_ = v___y_3463_;
v___y_3456_ = v___x_3480_;
goto v___jp_3448_;
}
}
else
{
size_t v___x_3481_; size_t v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = ((size_t)0ULL);
v___x_3482_ = lean_usize_of_nat(v___x_3469_);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__4(v_visitedExpr_3476_, v_insts_3337_, v___x_3481_, v___x_3482_, v___x_3470_);
lean_dec_ref(v_visitedExpr_3476_);
v___y_3449_ = v___y_3468_;
v___y_3450_ = v___y_3462_;
v___y_3451_ = v___y_3465_;
v___y_3452_ = v___y_3466_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3467_;
v___y_3455_ = v___y_3463_;
v___y_3456_ = v___x_3483_;
goto v___jp_3448_;
}
}
}
v___jp_3484_:
{
lean_object* v___x_3492_; 
lean_inc_ref(v_val_3485_);
v___x_3492_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_solveMVarsWithDefault(v_val_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v___x_3493_; lean_object* v_a_3494_; uint8_t v___x_3495_; 
lean_dec_ref_known(v___x_3492_, 1);
v___x_3493_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__1___redArg(v_val_3485_, v___y_3489_);
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref(v___x_3493_);
v___x_3495_ = l_Lean_Expr_hasMVar(v_a_3494_);
if (v___x_3495_ == 0)
{
v___y_3462_ = v_a_3494_;
v___y_3463_ = v___y_3486_;
v___y_3464_ = v___y_3487_;
v___y_3465_ = v___y_3488_;
v___y_3466_ = v___y_3489_;
v___y_3467_ = v___y_3490_;
v___y_3468_ = v___y_3491_;
goto v___jp_3461_;
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
v___x_3496_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___closed__13);
v___x_3497_ = lean_unsigned_to_nat(30u);
v___x_3498_ = l_Lean_inlineExprTrailing(v_a_3494_, v___x_3497_);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3496_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1___redArg(v___x_3499_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec_ref(v_val_3485_);
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
v_a_3509_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3492_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3492_);
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
v_val_3485_ = v_a_3519_;
v___y_3486_ = v___y_3339_;
v___y_3487_ = v___y_3340_;
v___y_3488_ = v___y_3341_;
v___y_3489_ = v___y_3342_;
v___y_3490_ = v___y_3343_;
v___y_3491_ = v___y_3344_;
goto v___jp_3484_;
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
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
v___jp_3528_:
{
if (lean_obj_tag(v___y_3529_) == 0)
{
lean_object* v_a_3530_; 
v_a_3530_ = lean_ctor_get(v___y_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___y_3529_, 1);
v_val_3485_ = v_a_3530_;
v___y_3486_ = v___y_3339_;
v___y_3487_ = v___y_3340_;
v___y_3488_ = v___y_3341_;
v___y_3489_ = v___y_3342_;
v___y_3490_ = v___y_3343_;
v___y_3491_ = v___y_3344_;
goto v___jp_3484_;
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v_type_3349_);
lean_dec(v_localInst2Index_3338_);
lean_dec(v___x_3333_);
lean_dec(v___x_3332_);
lean_dec_ref(v_xs_3331_);
v_a_3531_ = lean_ctor_get(v___y_3529_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___y_3529_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___y_3529_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___y_3529_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed(lean_object** _args){
lean_object* v_inductiveTypeName_3936_ = _args[0];
lean_object* v_us_3937_ = _args[1];
lean_object* v_xs_3938_ = _args[2];
lean_object* v___x_3939_ = _args[3];
lean_object* v___x_3940_ = _args[4];
lean_object* v_ctorName_3941_ = _args[5];
lean_object* v___x_3942_ = _args[6];
lean_object* v___f_3943_ = _args[7];
lean_object* v_insts_3944_ = _args[8];
lean_object* v_localInst2Index_3945_ = _args[9];
lean_object* v___y_3946_ = _args[10];
lean_object* v___y_3947_ = _args[11];
lean_object* v___y_3948_ = _args[12];
lean_object* v___y_3949_ = _args[13];
lean_object* v___y_3950_ = _args[14];
lean_object* v___y_3951_ = _args[15];
lean_object* v___y_3952_ = _args[16];
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6(v_inductiveTypeName_3936_, v_us_3937_, v_xs_3938_, v___x_3939_, v___x_3940_, v_ctorName_3941_, v___x_3942_, v___f_3943_, v_insts_3944_, v_localInst2Index_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec_ref(v_insts_3944_);
lean_dec_ref(v___x_3942_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(size_t v_sz_3954_, size_t v_i_3955_, lean_object* v_bs_3956_){
_start:
{
uint8_t v___x_3957_; 
v___x_3957_ = lean_usize_dec_lt(v_i_3955_, v_sz_3954_);
if (v___x_3957_ == 0)
{
return v_bs_3956_;
}
else
{
lean_object* v_v_3958_; lean_object* v___x_3959_; lean_object* v_bs_x27_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; size_t v___x_3965_; size_t v___x_3966_; lean_object* v___x_3967_; 
v_v_3958_ = lean_array_uget(v_bs_3956_, v_i_3955_);
v___x_3959_ = lean_unsigned_to_nat(0u);
v_bs_x27_3960_ = lean_array_uset(v_bs_3956_, v_i_3955_, v___x_3959_);
v___x_3961_ = l_Lean_Expr_fvarId_x21(v_v_3958_);
lean_dec(v_v_3958_);
v___x_3962_ = 1;
v___x_3963_ = lean_box(v___x_3962_);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3961_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = ((size_t)1ULL);
v___x_3966_ = lean_usize_add(v_i_3955_, v___x_3965_);
v___x_3967_ = lean_array_uset(v_bs_x27_3960_, v_i_3955_, v___x_3964_);
v_i_3955_ = v___x_3966_;
v_bs_3956_ = v___x_3967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8___boxed(lean_object* v_sz_3969_, lean_object* v_i_3970_, lean_object* v_bs_3971_){
_start:
{
size_t v_sz_boxed_3972_; size_t v_i_boxed_3973_; lean_object* v_res_3974_; 
v_sz_boxed_3972_ = lean_unbox_usize(v_sz_3969_);
lean_dec(v_sz_3969_);
v_i_boxed_3973_ = lean_unbox_usize(v_i_3970_);
lean_dec(v_i_3970_);
v_res_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_boxed_3972_, v_i_boxed_3973_, v_bs_3971_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(lean_object* v_k_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; 
lean_inc(v___y_3977_);
lean_inc_ref(v___y_3976_);
v___x_3983_ = lean_apply_7(v_k_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, lean_box(0));
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0(v_k_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(lean_object* v_bs_3993_, lean_object* v_k_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v___f_4002_; lean_object* v___x_4003_; 
lean_inc(v___y_3996_);
lean_inc_ref(v___y_3995_);
v___f_4002_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4002_, 0, v_k_3994_);
lean_closure_set(v___f_4002_, 1, v___y_3995_);
lean_closure_set(v___f_4002_, 2, v___y_3996_);
v___x_4003_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_3993_, v___f_4002_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
if (lean_obj_tag(v___x_4003_) == 0)
{
return v___x_4003_;
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_4003_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_4003_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg___boxed(lean_object* v_bs_4012_, lean_object* v_k_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4012_, v_k_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec_ref(v_bs_4012_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(lean_object* v_bs_4022_, lean_object* v_k_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
size_t v_sz_4031_; size_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_sz_4031_ = lean_array_size(v_bs_4022_);
v___x_4032_ = ((size_t)0ULL);
v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__8(v_sz_4031_, v___x_4032_, v_bs_4022_);
v___x_4034_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v___x_4033_, v_k_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec_ref(v___x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg___boxed(lean_object* v_bs_4035_, lean_object* v_k_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4035_, v_k_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(lean_object* v_numParams_4045_, lean_object* v_inductiveTypeName_4046_, lean_object* v_us_4047_, lean_object* v___x_4048_, lean_object* v_ctorName_4049_, lean_object* v___f_4050_, uint8_t v_addHypotheses_4051_, lean_object* v_xs_4052_, lean_object* v_x_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___f_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4061_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_xs_4052_, 2);
v___x_4062_ = l_Array_toSubarray___redArg(v_xs_4052_, v___x_4061_, v_numParams_4045_);
v___x_4063_ = l_Subarray_copy___redArg(v___x_4062_);
lean_inc_ref(v___x_4063_);
v___f_4064_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__6___boxed), 17, 8);
lean_closure_set(v___f_4064_, 0, v_inductiveTypeName_4046_);
lean_closure_set(v___f_4064_, 1, v_us_4047_);
lean_closure_set(v___f_4064_, 2, v_xs_4052_);
lean_closure_set(v___f_4064_, 3, v___x_4061_);
lean_closure_set(v___f_4064_, 4, v___x_4048_);
lean_closure_set(v___f_4064_, 5, v_ctorName_4049_);
lean_closure_set(v___f_4064_, 6, v___x_4063_);
lean_closure_set(v___f_4064_, 7, v___f_4050_);
v___x_4065_ = lean_box(v_addHypotheses_4051_);
v___x_4066_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParams___boxed), 11, 4);
lean_closure_set(v___x_4066_, 0, v___x_4065_);
lean_closure_set(v___x_4066_, 1, lean_box(0));
lean_closure_set(v___x_4066_, 2, v___x_4063_);
lean_closure_set(v___x_4066_, 3, v___f_4064_);
v___x_4067_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_xs_4052_, v___x_4066_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed(lean_object* v_numParams_4068_, lean_object* v_inductiveTypeName_4069_, lean_object* v_us_4070_, lean_object* v___x_4071_, lean_object* v_ctorName_4072_, lean_object* v___f_4073_, lean_object* v_addHypotheses_4074_, lean_object* v_xs_4075_, lean_object* v_x_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
uint8_t v_addHypotheses_boxed_4084_; lean_object* v_res_4085_; 
v_addHypotheses_boxed_4084_ = lean_unbox(v_addHypotheses_4074_);
v_res_4085_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3(v_numParams_4068_, v_inductiveTypeName_4069_, v_us_4070_, v___x_4071_, v_ctorName_4072_, v___f_4073_, v_addHypotheses_boxed_4084_, v_xs_4075_, v_x_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec_ref(v_x_4076_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(lean_object* v_a_4086_, lean_object* v_a_4087_){
_start:
{
if (lean_obj_tag(v_a_4086_) == 0)
{
lean_object* v___x_4088_; 
v___x_4088_ = l_List_reverse___redArg(v_a_4087_);
return v___x_4088_;
}
else
{
lean_object* v_head_4089_; lean_object* v_tail_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4099_; 
v_head_4089_ = lean_ctor_get(v_a_4086_, 0);
v_tail_4090_ = lean_ctor_get(v_a_4086_, 1);
v_isSharedCheck_4099_ = !lean_is_exclusive(v_a_4086_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4092_ = v_a_4086_;
v_isShared_4093_ = v_isSharedCheck_4099_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_tail_4090_);
lean_inc(v_head_4089_);
lean_dec(v_a_4086_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4099_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4094_; lean_object* v___x_4096_; 
v___x_4094_ = l_Lean_Level_param___override(v_head_4089_);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 1, v_a_4087_);
lean_ctor_set(v___x_4092_, 0, v___x_4094_);
v___x_4096_ = v___x_4092_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4094_);
lean_ctor_set(v_reuseFailAlloc_4098_, 1, v_a_4087_);
v___x_4096_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
v_a_4086_ = v_tail_4090_;
v_a_4087_ = v___x_4096_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(lean_object* v_inductiveTypeName_4101_, lean_object* v_ctorName_4102_, uint8_t v_addHypotheses_4103_, lean_object* v_indVal_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_){
_start:
{
lean_object* v_toConstantVal_4112_; lean_object* v_numParams_4113_; lean_object* v_levelParams_4114_; lean_object* v_type_4115_; lean_object* v___f_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v_us_4119_; lean_object* v___x_4120_; lean_object* v___f_4121_; uint8_t v___x_4122_; lean_object* v___x_4123_; 
v_toConstantVal_4112_ = lean_ctor_get(v_indVal_4104_, 0);
lean_inc_ref(v_toConstantVal_4112_);
v_numParams_4113_ = lean_ctor_get(v_indVal_4104_, 1);
lean_inc(v_numParams_4113_);
lean_dec_ref(v_indVal_4104_);
v_levelParams_4114_ = lean_ctor_get(v_toConstantVal_4112_, 1);
lean_inc(v_levelParams_4114_);
v_type_4115_ = lean_ctor_get(v_toConstantVal_4112_, 2);
lean_inc_ref(v_type_4115_);
lean_dec_ref(v_toConstantVal_4112_);
v___f_4116_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___closed__0));
v___x_4117_ = lean_box(1);
v___x_4118_ = lean_box(0);
v_us_4119_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__0(v_levelParams_4114_, v___x_4118_);
v___x_4120_ = lean_box(v_addHypotheses_4103_);
v___f_4121_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___lam__3___boxed), 16, 7);
lean_closure_set(v___f_4121_, 0, v_numParams_4113_);
lean_closure_set(v___f_4121_, 1, v_inductiveTypeName_4101_);
lean_closure_set(v___f_4121_, 2, v_us_4119_);
lean_closure_set(v___f_4121_, 3, v___x_4117_);
lean_closure_set(v___f_4121_, 4, v_ctorName_4102_);
lean_closure_set(v___f_4121_, 5, v___f_4116_);
lean_closure_set(v___f_4121_, 6, v___x_4120_);
v___x_4122_ = 0;
v___x_4123_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__8___redArg(v_type_4115_, v___f_4121_, v___x_4122_, v___x_4122_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed(lean_object* v_inductiveTypeName_4124_, lean_object* v_ctorName_4125_, lean_object* v_addHypotheses_4126_, lean_object* v_indVal_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
uint8_t v_addHypotheses_boxed_4135_; lean_object* v_res_4136_; 
v_addHypotheses_boxed_4135_ = lean_unbox(v_addHypotheses_4126_);
v_res_4136_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue(v_inductiveTypeName_4124_, v_ctorName_4125_, v_addHypotheses_boxed_4135_, v_indVal_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_);
lean_dec(v_a_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
lean_dec(v_a_4129_);
lean_dec_ref(v_a_4128_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(lean_object* v_00_u03b1_4137_, lean_object* v_bs_4138_, lean_object* v_k_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___redArg(v_bs_4138_, v_k_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4148_, lean_object* v_bs_4149_, lean_object* v_k_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7_spec__9(v_00_u03b1_4148_, v_bs_4149_, v_k_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec_ref(v_bs_4149_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(lean_object* v_00_u03b1_4159_, lean_object* v_bs_4160_, lean_object* v_k_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___redArg(v_bs_4160_, v_k_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7___boxed(lean_object* v_00_u03b1_4170_, lean_object* v_bs_4171_, lean_object* v_k_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue_spec__7(v_00_u03b1_4170_, v_bs_4171_, v_k_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(lean_object* v_name_4181_, lean_object* v_levelParams_4182_, lean_object* v_type_4183_, lean_object* v_value_4184_, lean_object* v_hints_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; uint8_t v___y_4190_; uint8_t v___y_4197_; lean_object* v_env_4200_; uint8_t v___x_4201_; 
v___x_4188_ = lean_st_ref_get(v___y_4186_);
v_env_4200_ = lean_ctor_get(v___x_4188_, 0);
lean_inc_ref_n(v_env_4200_, 2);
lean_dec(v___x_4188_);
v___x_4201_ = l_Lean_Environment_hasUnsafe(v_env_4200_, v_type_4183_);
if (v___x_4201_ == 0)
{
uint8_t v___x_4202_; 
v___x_4202_ = l_Lean_Environment_hasUnsafe(v_env_4200_, v_value_4184_);
v___y_4197_ = v___x_4202_;
goto v___jp_4196_;
}
else
{
lean_dec_ref(v_env_4200_);
v___y_4197_ = v___x_4201_;
goto v___jp_4196_;
}
v___jp_4189_:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_inc(v_name_4181_);
v___x_4191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4191_, 0, v_name_4181_);
lean_ctor_set(v___x_4191_, 1, v_levelParams_4182_);
lean_ctor_set(v___x_4191_, 2, v_type_4183_);
v___x_4192_ = lean_box(0);
v___x_4193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4193_, 0, v_name_4181_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4194_, 0, v___x_4191_);
lean_ctor_set(v___x_4194_, 1, v_value_4184_);
lean_ctor_set(v___x_4194_, 2, v_hints_4185_);
lean_ctor_set(v___x_4194_, 3, v___x_4193_);
lean_ctor_set_uint8(v___x_4194_, sizeof(void*)*4, v___y_4190_);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
v___jp_4196_:
{
if (v___y_4197_ == 0)
{
uint8_t v___x_4198_; 
v___x_4198_ = 1;
v___y_4190_ = v___x_4198_;
goto v___jp_4189_;
}
else
{
uint8_t v___x_4199_; 
v___x_4199_ = 0;
v___y_4190_ = v___x_4199_;
goto v___jp_4189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg___boxed(lean_object* v_name_4203_, lean_object* v_levelParams_4204_, lean_object* v_type_4205_, lean_object* v_value_4206_, lean_object* v_hints_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4203_, v_levelParams_4204_, v_type_4205_, v_value_4206_, v_hints_4207_, v___y_4208_);
lean_dec(v___y_4208_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(lean_object* v_name_4211_, lean_object* v_levelParams_4212_, lean_object* v_type_4213_, lean_object* v_value_4214_, lean_object* v_hints_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v_name_4211_, v_levelParams_4212_, v_type_4213_, v_value_4214_, v_hints_4215_, v___y_4221_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___boxed(lean_object* v_name_4224_, lean_object* v_levelParams_4225_, lean_object* v_type_4226_, lean_object* v_value_4227_, lean_object* v_hints_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
lean_object* v_res_4236_; 
v_res_4236_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0(v_name_4224_, v_levelParams_4225_, v_type_4226_, v_value_4227_, v_hints_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(lean_object* v___y_4237_, uint8_t v_isExporting_4238_, lean_object* v___x_4239_, lean_object* v___y_4240_, lean_object* v___x_4241_, lean_object* v_a_x3f_4242_){
_start:
{
lean_object* v___x_4244_; lean_object* v_env_4245_; lean_object* v_nextMacroScope_4246_; lean_object* v_ngen_4247_; lean_object* v_auxDeclNGen_4248_; lean_object* v_traceState_4249_; lean_object* v_messages_4250_; lean_object* v_infoState_4251_; lean_object* v_snapshotTasks_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4277_; 
v___x_4244_ = lean_st_ref_take(v___y_4237_);
v_env_4245_ = lean_ctor_get(v___x_4244_, 0);
v_nextMacroScope_4246_ = lean_ctor_get(v___x_4244_, 1);
v_ngen_4247_ = lean_ctor_get(v___x_4244_, 2);
v_auxDeclNGen_4248_ = lean_ctor_get(v___x_4244_, 3);
v_traceState_4249_ = lean_ctor_get(v___x_4244_, 4);
v_messages_4250_ = lean_ctor_get(v___x_4244_, 6);
v_infoState_4251_ = lean_ctor_get(v___x_4244_, 7);
v_snapshotTasks_4252_ = lean_ctor_get(v___x_4244_, 8);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4277_ == 0)
{
lean_object* v_unused_4278_; 
v_unused_4278_ = lean_ctor_get(v___x_4244_, 5);
lean_dec(v_unused_4278_);
v___x_4254_ = v___x_4244_;
v_isShared_4255_ = v_isSharedCheck_4277_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_snapshotTasks_4252_);
lean_inc(v_infoState_4251_);
lean_inc(v_messages_4250_);
lean_inc(v_traceState_4249_);
lean_inc(v_auxDeclNGen_4248_);
lean_inc(v_ngen_4247_);
lean_inc(v_nextMacroScope_4246_);
lean_inc(v_env_4245_);
lean_dec(v___x_4244_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4277_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4256_; lean_object* v___x_4258_; 
v___x_4256_ = l_Lean_Environment_setExporting(v_env_4245_, v_isExporting_4238_);
if (v_isShared_4255_ == 0)
{
lean_ctor_set(v___x_4254_, 5, v___x_4239_);
lean_ctor_set(v___x_4254_, 0, v___x_4256_);
v___x_4258_ = v___x_4254_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4256_);
lean_ctor_set(v_reuseFailAlloc_4276_, 1, v_nextMacroScope_4246_);
lean_ctor_set(v_reuseFailAlloc_4276_, 2, v_ngen_4247_);
lean_ctor_set(v_reuseFailAlloc_4276_, 3, v_auxDeclNGen_4248_);
lean_ctor_set(v_reuseFailAlloc_4276_, 4, v_traceState_4249_);
lean_ctor_set(v_reuseFailAlloc_4276_, 5, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4276_, 6, v_messages_4250_);
lean_ctor_set(v_reuseFailAlloc_4276_, 7, v_infoState_4251_);
lean_ctor_set(v_reuseFailAlloc_4276_, 8, v_snapshotTasks_4252_);
v___x_4258_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v_mctx_4261_; lean_object* v_zetaDeltaFVarIds_4262_; lean_object* v_postponed_4263_; lean_object* v_diag_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4274_; 
v___x_4259_ = lean_st_ref_put(v___y_4237_, v___x_4258_);
v___x_4260_ = lean_st_ref_take(v___y_4240_);
v_mctx_4261_ = lean_ctor_get(v___x_4260_, 0);
v_zetaDeltaFVarIds_4262_ = lean_ctor_get(v___x_4260_, 2);
v_postponed_4263_ = lean_ctor_get(v___x_4260_, 3);
v_diag_4264_ = lean_ctor_get(v___x_4260_, 4);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4274_ == 0)
{
lean_object* v_unused_4275_; 
v_unused_4275_ = lean_ctor_get(v___x_4260_, 1);
lean_dec(v_unused_4275_);
v___x_4266_ = v___x_4260_;
v_isShared_4267_ = v_isSharedCheck_4274_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_diag_4264_);
lean_inc(v_postponed_4263_);
lean_inc(v_zetaDeltaFVarIds_4262_);
lean_inc(v_mctx_4261_);
lean_dec(v___x_4260_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4274_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 1, v___x_4241_);
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_mctx_4261_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v___x_4241_);
lean_ctor_set(v_reuseFailAlloc_4273_, 2, v_zetaDeltaFVarIds_4262_);
lean_ctor_set(v_reuseFailAlloc_4273_, 3, v_postponed_4263_);
lean_ctor_set(v_reuseFailAlloc_4273_, 4, v_diag_4264_);
v___x_4269_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4270_ = lean_st_ref_put(v___y_4240_, v___x_4269_);
v___x_4271_ = lean_box(0);
v___x_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4271_);
return v___x_4272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0___boxed(lean_object* v___y_4279_, lean_object* v_isExporting_4280_, lean_object* v___x_4281_, lean_object* v___y_4282_, lean_object* v___x_4283_, lean_object* v_a_x3f_4284_, lean_object* v___y_4285_){
_start:
{
uint8_t v_isExporting_boxed_4286_; lean_object* v_res_4287_; 
v_isExporting_boxed_4286_ = lean_unbox(v_isExporting_4280_);
v_res_4287_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4279_, v_isExporting_boxed_4286_, v___x_4281_, v___y_4282_, v___x_4283_, v_a_x3f_4284_);
lean_dec(v_a_x3f_4284_);
lean_dec(v___y_4282_);
lean_dec(v___y_4279_);
return v_res_4287_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4288_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__0);
v___x_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4289_);
return v___x_4290_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4291_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
return v___x_4292_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__1);
v___x_4294_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
lean_ctor_set(v___x_4294_, 2, v___x_4293_);
lean_ctor_set(v___x_4294_, 3, v___x_4293_);
lean_ctor_set(v___x_4294_, 4, v___x_4293_);
lean_ctor_set(v___x_4294_, 5, v___x_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(lean_object* v_x_4295_, uint8_t v_isExporting_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v___x_4304_; lean_object* v_env_4305_; lean_object* v___x_4306_; uint8_t v_isModule_4307_; 
v___x_4304_ = lean_st_ref_get(v___y_4302_);
v_env_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc_ref(v_env_4305_);
lean_dec(v___x_4304_);
v___x_4306_ = l_Lean_Environment_header(v_env_4305_);
v_isModule_4307_ = lean_ctor_get_uint8(v___x_4306_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4306_);
if (v_isModule_4307_ == 0)
{
lean_object* v___x_4308_; 
lean_dec_ref(v_env_4305_);
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc_ref(v___y_4299_);
lean_inc(v___y_4298_);
lean_inc_ref(v___y_4297_);
v___x_4308_ = lean_apply_7(v_x_4295_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, lean_box(0));
return v___x_4308_;
}
else
{
uint8_t v_isExporting_4309_; 
v_isExporting_4309_ = lean_ctor_get_uint8(v_env_4305_, sizeof(void*)*8);
lean_dec_ref(v_env_4305_);
if (v_isExporting_4296_ == 0)
{
if (v_isExporting_4309_ == 0)
{
lean_object* v___x_4375_; 
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc_ref(v___y_4299_);
lean_inc(v___y_4298_);
lean_inc_ref(v___y_4297_);
v___x_4375_ = lean_apply_7(v_x_4295_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, lean_box(0));
return v___x_4375_;
}
else
{
goto v___jp_4310_;
}
}
else
{
if (v_isExporting_4309_ == 0)
{
goto v___jp_4310_;
}
else
{
lean_object* v___x_4376_; 
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc_ref(v___y_4299_);
lean_inc(v___y_4298_);
lean_inc_ref(v___y_4297_);
v___x_4376_ = lean_apply_7(v_x_4295_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, lean_box(0));
return v___x_4376_;
}
}
v___jp_4310_:
{
lean_object* v___x_4311_; lean_object* v_env_4312_; lean_object* v_nextMacroScope_4313_; lean_object* v_ngen_4314_; lean_object* v_auxDeclNGen_4315_; lean_object* v_traceState_4316_; lean_object* v_messages_4317_; lean_object* v_infoState_4318_; lean_object* v_snapshotTasks_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4373_; 
v___x_4311_ = lean_st_ref_take(v___y_4302_);
v_env_4312_ = lean_ctor_get(v___x_4311_, 0);
v_nextMacroScope_4313_ = lean_ctor_get(v___x_4311_, 1);
v_ngen_4314_ = lean_ctor_get(v___x_4311_, 2);
v_auxDeclNGen_4315_ = lean_ctor_get(v___x_4311_, 3);
v_traceState_4316_ = lean_ctor_get(v___x_4311_, 4);
v_messages_4317_ = lean_ctor_get(v___x_4311_, 6);
v_infoState_4318_ = lean_ctor_get(v___x_4311_, 7);
v_snapshotTasks_4319_ = lean_ctor_get(v___x_4311_, 8);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4373_ == 0)
{
lean_object* v_unused_4374_; 
v_unused_4374_ = lean_ctor_get(v___x_4311_, 5);
lean_dec(v_unused_4374_);
v___x_4321_ = v___x_4311_;
v_isShared_4322_ = v_isSharedCheck_4373_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_snapshotTasks_4319_);
lean_inc(v_infoState_4318_);
lean_inc(v_messages_4317_);
lean_inc(v_traceState_4316_);
lean_inc(v_auxDeclNGen_4315_);
lean_inc(v_ngen_4314_);
lean_inc(v_nextMacroScope_4313_);
lean_inc(v_env_4312_);
lean_dec(v___x_4311_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4373_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4326_; 
v___x_4323_ = l_Lean_Environment_setExporting(v_env_4312_, v_isExporting_4296_);
v___x_4324_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 5, v___x_4324_);
lean_ctor_set(v___x_4321_, 0, v___x_4323_);
v___x_4326_ = v___x_4321_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4323_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v_nextMacroScope_4313_);
lean_ctor_set(v_reuseFailAlloc_4372_, 2, v_ngen_4314_);
lean_ctor_set(v_reuseFailAlloc_4372_, 3, v_auxDeclNGen_4315_);
lean_ctor_set(v_reuseFailAlloc_4372_, 4, v_traceState_4316_);
lean_ctor_set(v_reuseFailAlloc_4372_, 5, v___x_4324_);
lean_ctor_set(v_reuseFailAlloc_4372_, 6, v_messages_4317_);
lean_ctor_set(v_reuseFailAlloc_4372_, 7, v_infoState_4318_);
lean_ctor_set(v_reuseFailAlloc_4372_, 8, v_snapshotTasks_4319_);
v___x_4326_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v_mctx_4329_; lean_object* v_zetaDeltaFVarIds_4330_; lean_object* v_postponed_4331_; lean_object* v_diag_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4370_; 
v___x_4327_ = lean_st_ref_put(v___y_4302_, v___x_4326_);
v___x_4328_ = lean_st_ref_take(v___y_4300_);
v_mctx_4329_ = lean_ctor_get(v___x_4328_, 0);
v_zetaDeltaFVarIds_4330_ = lean_ctor_get(v___x_4328_, 2);
v_postponed_4331_ = lean_ctor_get(v___x_4328_, 3);
v_diag_4332_ = lean_ctor_get(v___x_4328_, 4);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4370_ == 0)
{
lean_object* v_unused_4371_; 
v_unused_4371_ = lean_ctor_get(v___x_4328_, 1);
lean_dec(v_unused_4371_);
v___x_4334_ = v___x_4328_;
v_isShared_4335_ = v_isSharedCheck_4370_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_diag_4332_);
lean_inc(v_postponed_4331_);
lean_inc(v_zetaDeltaFVarIds_4330_);
lean_inc(v_mctx_4329_);
lean_dec(v___x_4328_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4370_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4336_; lean_object* v___x_4338_; 
v___x_4336_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 1, v___x_4336_);
v___x_4338_ = v___x_4334_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_mctx_4329_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4369_, 2, v_zetaDeltaFVarIds_4330_);
lean_ctor_set(v_reuseFailAlloc_4369_, 3, v_postponed_4331_);
lean_ctor_set(v_reuseFailAlloc_4369_, 4, v_diag_4332_);
v___x_4338_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4339_; lean_object* v_r_4340_; 
v___x_4339_ = lean_st_ref_put(v___y_4300_, v___x_4338_);
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc_ref(v___y_4299_);
lean_inc(v___y_4298_);
lean_inc_ref(v___y_4297_);
v_r_4340_ = lean_apply_7(v_x_4295_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, lean_box(0));
if (lean_obj_tag(v_r_4340_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4357_; 
v_a_4341_ = lean_ctor_get(v_r_4340_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v_r_4340_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4343_ = v_r_4340_;
v_isShared_4344_ = v_isSharedCheck_4357_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v_r_4340_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4357_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
lean_inc(v_a_4341_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set_tag(v___x_4343_, 1);
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
v___x_4347_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4302_, v_isExporting_4309_, v___x_4324_, v___y_4300_, v___x_4336_, v___x_4346_);
lean_dec_ref(v___x_4346_);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4354_ == 0)
{
lean_object* v_unused_4355_; 
v_unused_4355_ = lean_ctor_get(v___x_4347_, 0);
lean_dec(v_unused_4355_);
v___x_4349_ = v___x_4347_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_dec(v___x_4347_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v_a_4341_);
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4341_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_a_4358_ = lean_ctor_get(v_r_4340_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v_r_4340_, 1);
v___x_4359_ = lean_box(0);
v___x_4360_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___lam__0(v___y_4302_, v_isExporting_4309_, v___x_4324_, v___y_4300_, v___x_4336_, v___x_4359_);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4367_ == 0)
{
lean_object* v_unused_4368_; 
v_unused_4368_ = lean_ctor_get(v___x_4360_, 0);
lean_dec(v_unused_4368_);
v___x_4362_ = v___x_4360_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_dec(v___x_4360_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
lean_ctor_set_tag(v___x_4362_, 1);
lean_ctor_set(v___x_4362_, 0, v_a_4358_);
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4358_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___boxed(lean_object* v_x_4377_, lean_object* v_isExporting_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
uint8_t v_isExporting_boxed_4386_; lean_object* v_res_4387_; 
v_isExporting_boxed_4386_ = lean_unbox(v_isExporting_4378_);
v_res_4387_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4377_, v_isExporting_boxed_4386_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(lean_object* v_00_u03b1_4388_, lean_object* v_x_4389_, uint8_t v_isExporting_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v_x_4389_, v_isExporting_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___boxed(lean_object* v_00_u03b1_4399_, lean_object* v_x_4400_, lean_object* v_isExporting_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
uint8_t v_isExporting_boxed_4409_; lean_object* v_res_4410_; 
v_isExporting_boxed_4409_ = lean_unbox(v_isExporting_4401_);
v_res_4410_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1(v_00_u03b1_4399_, v_x_4400_, v_isExporting_boxed_4409_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(lean_object* v_____r_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___closed__0));
v___x_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0___boxed(lean_object* v_____r_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__0(v_____r_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
return v_res_4431_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__0));
v___x_4434_ = l_Lean_stringToMessageData(v___x_4433_);
return v___x_4434_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4436_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__2));
v___x_4437_ = l_Lean_stringToMessageData(v___x_4436_);
return v___x_4437_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__4));
v___x_4440_ = l_Lean_stringToMessageData(v___x_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(lean_object* v___x_4441_, lean_object* v___x_4442_, lean_object* v_inductiveTypeName_4443_, uint8_t v___x_4444_, lean_object* v___x_4445_, lean_object* v_ctorName_4446_, uint8_t v_addHypotheses_4447_, lean_object* v___f_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v___y_4457_; lean_object* v___x_4460_; 
lean_inc(v_inductiveTypeName_4443_);
v___x_4460_ = l_Lean_Elab_Deriving_mkContext(v___x_4441_, v___x_4442_, v_inductiveTypeName_4443_, v___x_4444_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v_options_4462_; lean_object* v_currNamespace_4463_; lean_object* v_inheritedTraceOptions_4464_; lean_object* v___x_4465_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref_known(v___x_4460_, 1);
v_options_4462_ = lean_ctor_get(v___y_4453_, 2);
v_currNamespace_4463_ = lean_ctor_get(v___y_4453_, 6);
v_inheritedTraceOptions_4464_ = lean_ctor_get(v___y_4453_, 13);
lean_inc(v_inductiveTypeName_4443_);
v___x_4465_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1(v_inductiveTypeName_4443_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v_instName_4467_; lean_object* v_auxFunNames_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4513_; uint8_t v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; uint8_t v___y_4522_; uint8_t v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v_a_4576_; lean_object* v___y_4647_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc_n(v_a_4466_, 2);
lean_dec_ref_known(v___x_4465_, 1);
v_instName_4467_ = lean_ctor_get(v_a_4461_, 0);
lean_inc(v_instName_4467_);
v_auxFunNames_4468_ = lean_ctor_get(v_a_4461_, 2);
lean_inc_ref(v_auxFunNames_4468_);
lean_dec(v_a_4461_);
v___x_4469_ = lean_unsigned_to_nat(0u);
v___x_4470_ = lean_array_get(v___x_4445_, v_auxFunNames_4468_, v___x_4469_);
lean_dec_ref(v_auxFunNames_4468_);
lean_inc(v_currNamespace_4463_);
v___x_4471_ = l_Lean_Name_append(v_currNamespace_4463_, v___x_4470_);
v___x_4666_ = lean_box(v_addHypotheses_4447_);
lean_inc(v_inductiveTypeName_4443_);
v___x_4667_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkDefaultValue___boxed), 11, 4);
lean_closure_set(v___x_4667_, 0, v_inductiveTypeName_4443_);
lean_closure_set(v___x_4667_, 1, v_ctorName_4446_);
lean_closure_set(v___x_4667_, 2, v___x_4666_);
lean_closure_set(v___x_4667_, 3, v_a_4466_);
lean_inc(v___x_4471_);
v___x_4668_ = l_Lean_Elab_Term_withDeclName___redArg(v___x_4471_, v___x_4667_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; 
lean_dec_ref(v___f_4448_);
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref_known(v___x_4668_, 1);
v_a_4576_ = v_a_4669_;
goto v___jp_4575_;
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4702_; 
v_a_4670_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4672_ = v___x_4668_;
v_isShared_4673_ = v_isSharedCheck_4702_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4668_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4702_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
uint8_t v___y_4678_; uint8_t v___x_4700_; 
v___x_4700_ = l_Lean_Exception_isInterrupt(v_a_4670_);
if (v___x_4700_ == 0)
{
uint8_t v___x_4701_; 
lean_inc(v_a_4670_);
v___x_4701_ = l_Lean_Exception_isRuntime(v_a_4670_);
v___y_4678_ = v___x_4701_;
goto v___jp_4677_;
}
else
{
v___y_4678_ = v___x_4700_;
goto v___jp_4677_;
}
v___jp_4674_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = lean_box(0);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
lean_inc(v___y_4450_);
lean_inc_ref(v___y_4449_);
v___x_4676_ = lean_apply_8(v___f_4448_, v___x_4675_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, lean_box(0));
v___y_4647_ = v___x_4676_;
goto v___jp_4646_;
}
v___jp_4677_:
{
if (v___y_4678_ == 0)
{
uint8_t v_hasTrace_4679_; 
lean_del_object(v___x_4672_);
v_hasTrace_4679_ = lean_ctor_get_uint8(v_options_4462_, sizeof(void*)*1);
if (v_hasTrace_4679_ == 0)
{
lean_dec(v_a_4670_);
goto v___jp_4674_;
}
else
{
lean_object* v___x_4680_; lean_object* v___x_4681_; uint8_t v___x_4682_; 
v___x_4680_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_4681_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4464_, v_options_4462_, v___x_4681_);
if (v___x_4682_ == 0)
{
lean_dec(v_a_4670_);
goto v___jp_4674_;
}
else
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4683_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__5);
v___x_4684_ = l_Lean_Exception_toMessageData(v_a_4670_);
v___x_4685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4683_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
v___x_4686_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4680_, v___x_4685_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4688_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v___x_4686_, 1);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
lean_inc(v___y_4450_);
lean_inc_ref(v___y_4449_);
v___x_4688_ = lean_apply_8(v___f_4448_, v_a_4687_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, lean_box(0));
v___y_4647_ = v___x_4688_;
goto v___jp_4646_;
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_dec(v___x_4471_);
lean_dec(v_instName_4467_);
lean_dec(v_a_4466_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec_ref(v___f_4448_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4689_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4686_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4686_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
}
}
else
{
lean_object* v___x_4698_; 
lean_dec(v___x_4471_);
lean_dec(v_instName_4467_);
lean_dec(v_a_4466_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec_ref(v___f_4448_);
lean_dec(v_inductiveTypeName_4443_);
if (v_isShared_4673_ == 0)
{
v___x_4698_ = v___x_4672_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4670_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
}
v___jp_4472_:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4481_ = l_Lean_mkIdent(v_instName_4467_);
v___x_4482_ = l_Lean_mkCIdent(v___x_4471_);
v___x_4483_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith(v_inductiveTypeName_4443_, v___x_4481_, v___y_4474_, v___x_4482_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_options_4484_; uint8_t v_hasTrace_4485_; 
v_options_4484_ = lean_ctor_get(v___y_4479_, 2);
v_hasTrace_4485_ = lean_ctor_get_uint8(v_options_4484_, sizeof(void*)*1);
if (v_hasTrace_4485_ == 0)
{
lean_object* v_a_4486_; 
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4473_);
v_a_4486_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4483_, 1);
v___y_4457_ = v_a_4486_;
goto v___jp_4456_;
}
else
{
lean_object* v_a_4487_; lean_object* v_inheritedTraceOptions_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; uint8_t v___x_4491_; 
v_a_4487_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4483_, 1);
v_inheritedTraceOptions_4488_ = lean_ctor_get(v___y_4479_, 13);
v___x_4489_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__5));
lean_inc(v___y_4473_);
v___x_4490_ = l_Lean_Name_append(v___x_4489_, v___y_4473_);
v___x_4491_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4488_, v_options_4484_, v___x_4490_);
lean_dec(v___x_4490_);
if (v___x_4491_ == 0)
{
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4473_);
v___y_4457_ = v_a_4487_;
goto v___jp_4456_;
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4492_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__1);
lean_inc(v_a_4487_);
v___x_4493_ = l_Lean_MessageData_ofSyntax(v_a_4487_);
v___x_4494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4492_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___x_4495_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___y_4473_, v___x_4494_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_dec_ref_known(v___x_4495_, 1);
v___y_4457_ = v_a_4487_;
goto v___jp_4456_;
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
lean_dec(v_a_4487_);
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___x_4495_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4495_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4473_);
v_a_4504_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4483_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4483_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
v___jp_4512_:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_compileDecls(v___y_4519_, v___y_4522_, v___y_4521_, v___y_4516_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v___x_4524_; 
lean_dec_ref_known(v___x_4523_, 1);
lean_inc(v___x_4471_);
v___x_4524_ = l_Lean_enableRealizationsForConst(v___x_4471_, v___y_4521_, v___y_4516_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_options_4525_; lean_object* v_inheritedTraceOptions_4526_; uint8_t v_hasTrace_4527_; lean_object* v___x_4528_; 
lean_dec_ref_known(v___x_4524_, 1);
v_options_4525_ = lean_ctor_get(v___y_4521_, 2);
v_inheritedTraceOptions_4526_ = lean_ctor_get(v___y_4521_, 13);
v_hasTrace_4527_ = lean_ctor_get_uint8(v_options_4525_, sizeof(void*)*1);
v___x_4528_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
if (v_hasTrace_4527_ == 0)
{
v___y_4473_ = v___x_4528_;
v___y_4474_ = v___y_4517_;
v___y_4475_ = v___y_4515_;
v___y_4476_ = v___y_4513_;
v___y_4477_ = v___y_4518_;
v___y_4478_ = v___y_4520_;
v___y_4479_ = v___y_4521_;
v___y_4480_ = v___y_4516_;
goto v___jp_4472_;
}
else
{
lean_object* v___x_4529_; uint8_t v___x_4530_; 
v___x_4529_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__6);
v___x_4530_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4526_, v_options_4525_, v___x_4529_);
if (v___x_4530_ == 0)
{
v___y_4473_ = v___x_4528_;
v___y_4474_ = v___y_4517_;
v___y_4475_ = v___y_4515_;
v___y_4476_ = v___y_4513_;
v___y_4477_ = v___y_4518_;
v___y_4478_ = v___y_4520_;
v___y_4479_ = v___y_4521_;
v___y_4480_ = v___y_4516_;
goto v___jp_4472_;
}
else
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4531_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___closed__3);
lean_inc(v___x_4471_);
v___x_4532_ = l_Lean_MessageData_ofConstName(v___x_4471_, v___y_4514_);
v___x_4533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4531_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___x_4534_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux_spec__0___redArg(v___x_4528_, v___x_4533_, v___y_4518_, v___y_4520_, v___y_4521_, v___y_4516_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_dec_ref_known(v___x_4534_, 1);
v___y_4473_ = v___x_4528_;
v___y_4474_ = v___y_4517_;
v___y_4475_ = v___y_4515_;
v___y_4476_ = v___y_4513_;
v___y_4477_ = v___y_4518_;
v___y_4478_ = v___y_4520_;
v___y_4479_ = v___y_4521_;
v___y_4480_ = v___y_4516_;
goto v___jp_4472_;
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4513_);
lean_dec(v___x_4471_);
lean_dec(v_instName_4467_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4534_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4534_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4513_);
lean_dec(v___x_4471_);
lean_dec(v_instName_4467_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4543_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4524_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4524_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4513_);
lean_dec(v___x_4471_);
lean_dec(v_instName_4467_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4551_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4523_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4523_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
v___jp_4559_:
{
lean_object* v___x_4568_; lean_object* v_env_4569_; uint8_t v_isNoncomputableSection_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4568_ = lean_st_ref_get(v___y_4567_);
v_env_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc_ref(v_env_4569_);
lean_dec(v___x_4568_);
v_isNoncomputableSection_4570_ = lean_ctor_get_uint8(v___y_4562_, sizeof(void*)*8 + 4);
v___x_4571_ = lean_unsigned_to_nat(1u);
v___x_4572_ = lean_mk_empty_array_with_capacity(v___x_4571_);
lean_inc(v___x_4471_);
v___x_4573_ = lean_array_push(v___x_4572_, v___x_4471_);
if (v_isNoncomputableSection_4570_ == 0)
{
lean_dec_ref(v_env_4569_);
v___y_4513_ = v___y_4563_;
v___y_4514_ = v___y_4560_;
v___y_4515_ = v___y_4562_;
v___y_4516_ = v___y_4567_;
v___y_4517_ = v___y_4561_;
v___y_4518_ = v___y_4564_;
v___y_4519_ = v___x_4573_;
v___y_4520_ = v___y_4565_;
v___y_4521_ = v___y_4566_;
v___y_4522_ = v___x_4444_;
goto v___jp_4512_;
}
else
{
uint8_t v___x_4574_; 
lean_inc(v___x_4471_);
v___x_4574_ = l_Lean_isMarkedMeta(v_env_4569_, v___x_4471_);
v___y_4513_ = v___y_4563_;
v___y_4514_ = v___y_4560_;
v___y_4515_ = v___y_4562_;
v___y_4516_ = v___y_4567_;
v___y_4517_ = v___y_4561_;
v___y_4518_ = v___y_4564_;
v___y_4519_ = v___x_4573_;
v___y_4520_ = v___y_4565_;
v___y_4521_ = v___y_4566_;
v___y_4522_ = v___x_4574_;
goto v___jp_4512_;
}
}
v___jp_4575_:
{
lean_object* v_snd_4577_; lean_object* v_fst_4578_; lean_object* v_fst_4579_; lean_object* v_snd_4580_; lean_object* v___x_4581_; lean_object* v_toConstantVal_4582_; lean_object* v_env_4583_; lean_object* v_levelParams_4584_; uint32_t v___x_4585_; uint32_t v___x_4586_; uint32_t v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4645_; 
v_snd_4577_ = lean_ctor_get(v_a_4576_, 1);
lean_inc(v_snd_4577_);
v_fst_4578_ = lean_ctor_get(v_a_4576_, 0);
lean_inc(v_fst_4578_);
lean_dec_ref(v_a_4576_);
v_fst_4579_ = lean_ctor_get(v_snd_4577_, 0);
lean_inc_n(v_fst_4579_, 2);
v_snd_4580_ = lean_ctor_get(v_snd_4577_, 1);
lean_inc(v_snd_4580_);
lean_dec(v_snd_4577_);
v___x_4581_ = lean_st_ref_get(v___y_4454_);
v_toConstantVal_4582_ = lean_ctor_get(v_a_4466_, 0);
lean_inc_ref(v_toConstantVal_4582_);
lean_dec(v_a_4466_);
v_env_4583_ = lean_ctor_get(v___x_4581_, 0);
lean_inc_ref(v_env_4583_);
lean_dec(v___x_4581_);
v_levelParams_4584_ = lean_ctor_get(v_toConstantVal_4582_, 1);
lean_inc(v_levelParams_4584_);
lean_dec_ref(v_toConstantVal_4582_);
v___x_4585_ = l_Lean_getMaxHeight(v_env_4583_, v_fst_4579_);
v___x_4586_ = 1;
v___x_4587_ = lean_uint32_add(v___x_4585_, v___x_4586_);
v___x_4588_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_4588_, 0, v___x_4587_);
lean_inc(v___x_4471_);
v___x_4589_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__0___redArg(v___x_4471_, v_levelParams_4584_, v_fst_4578_, v_fst_4579_, v___x_4588_, v___y_4454_);
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4592_ = v___x_4589_;
v_isShared_4593_ = v_isSharedCheck_4645_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4589_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4645_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set_tag(v___x_4592_, 1);
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
uint8_t v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = 0;
v___x_4597_ = l_Lean_addDecl(v___x_4595_, v___x_4596_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v___x_4598_; lean_object* v_env_4599_; uint8_t v___x_4600_; 
lean_dec_ref_known(v___x_4597_, 1);
v___x_4598_ = lean_st_ref_get(v___y_4454_);
v_env_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc_ref(v_env_4599_);
lean_dec(v___x_4598_);
lean_inc(v_inductiveTypeName_4443_);
v___x_4600_ = l_Lean_isMarkedMeta(v_env_4599_, v_inductiveTypeName_4443_);
if (v___x_4600_ == 0)
{
v___y_4560_ = v___x_4596_;
v___y_4561_ = v_snd_4580_;
v___y_4562_ = v___y_4449_;
v___y_4563_ = v___y_4450_;
v___y_4564_ = v___y_4451_;
v___y_4565_ = v___y_4452_;
v___y_4566_ = v___y_4453_;
v___y_4567_ = v___y_4454_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4601_; lean_object* v_env_4602_; lean_object* v_nextMacroScope_4603_; lean_object* v_ngen_4604_; lean_object* v_auxDeclNGen_4605_; lean_object* v_traceState_4606_; lean_object* v_messages_4607_; lean_object* v_infoState_4608_; lean_object* v_snapshotTasks_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4634_; 
v___x_4601_ = lean_st_ref_take(v___y_4454_);
v_env_4602_ = lean_ctor_get(v___x_4601_, 0);
v_nextMacroScope_4603_ = lean_ctor_get(v___x_4601_, 1);
v_ngen_4604_ = lean_ctor_get(v___x_4601_, 2);
v_auxDeclNGen_4605_ = lean_ctor_get(v___x_4601_, 3);
v_traceState_4606_ = lean_ctor_get(v___x_4601_, 4);
v_messages_4607_ = lean_ctor_get(v___x_4601_, 6);
v_infoState_4608_ = lean_ctor_get(v___x_4601_, 7);
v_snapshotTasks_4609_ = lean_ctor_get(v___x_4601_, 8);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4634_ == 0)
{
lean_object* v_unused_4635_; 
v_unused_4635_ = lean_ctor_get(v___x_4601_, 5);
lean_dec(v_unused_4635_);
v___x_4611_ = v___x_4601_;
v_isShared_4612_ = v_isSharedCheck_4634_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_snapshotTasks_4609_);
lean_inc(v_infoState_4608_);
lean_inc(v_messages_4607_);
lean_inc(v_traceState_4606_);
lean_inc(v_auxDeclNGen_4605_);
lean_inc(v_ngen_4604_);
lean_inc(v_nextMacroScope_4603_);
lean_inc(v_env_4602_);
lean_dec(v___x_4601_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4634_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4616_; 
lean_inc(v___x_4471_);
v___x_4613_ = l_Lean_markMeta(v_env_4602_, v___x_4471_);
v___x_4614_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__2);
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 5, v___x_4614_);
lean_ctor_set(v___x_4611_, 0, v___x_4613_);
v___x_4616_ = v___x_4611_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4613_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v_nextMacroScope_4603_);
lean_ctor_set(v_reuseFailAlloc_4633_, 2, v_ngen_4604_);
lean_ctor_set(v_reuseFailAlloc_4633_, 3, v_auxDeclNGen_4605_);
lean_ctor_set(v_reuseFailAlloc_4633_, 4, v_traceState_4606_);
lean_ctor_set(v_reuseFailAlloc_4633_, 5, v___x_4614_);
lean_ctor_set(v_reuseFailAlloc_4633_, 6, v_messages_4607_);
lean_ctor_set(v_reuseFailAlloc_4633_, 7, v_infoState_4608_);
lean_ctor_set(v_reuseFailAlloc_4633_, 8, v_snapshotTasks_4609_);
v___x_4616_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v_mctx_4619_; lean_object* v_zetaDeltaFVarIds_4620_; lean_object* v_postponed_4621_; lean_object* v_diag_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4631_; 
v___x_4617_ = lean_st_ref_put(v___y_4454_, v___x_4616_);
v___x_4618_ = lean_st_ref_take(v___y_4452_);
v_mctx_4619_ = lean_ctor_get(v___x_4618_, 0);
v_zetaDeltaFVarIds_4620_ = lean_ctor_get(v___x_4618_, 2);
v_postponed_4621_ = lean_ctor_get(v___x_4618_, 3);
v_diag_4622_ = lean_ctor_get(v___x_4618_, 4);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4631_ == 0)
{
lean_object* v_unused_4632_; 
v_unused_4632_ = lean_ctor_get(v___x_4618_, 1);
lean_dec(v_unused_4632_);
v___x_4624_ = v___x_4618_;
v_isShared_4625_ = v_isSharedCheck_4631_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_diag_4622_);
lean_inc(v_postponed_4621_);
lean_inc(v_zetaDeltaFVarIds_4620_);
lean_inc(v_mctx_4619_);
lean_dec(v___x_4618_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4631_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; lean_object* v___x_4628_; 
v___x_4626_ = lean_obj_once(&l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg___closed__3);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 1, v___x_4626_);
v___x_4628_ = v___x_4624_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_mctx_4619_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4630_, 2, v_zetaDeltaFVarIds_4620_);
lean_ctor_set(v_reuseFailAlloc_4630_, 3, v_postponed_4621_);
lean_ctor_set(v_reuseFailAlloc_4630_, 4, v_diag_4622_);
v___x_4628_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
lean_object* v___x_4629_; 
v___x_4629_ = lean_st_ref_put(v___y_4452_, v___x_4628_);
v___y_4560_ = v___x_4596_;
v___y_4561_ = v_snd_4580_;
v___y_4562_ = v___y_4449_;
v___y_4563_ = v___y_4450_;
v___y_4564_ = v___y_4451_;
v___y_4565_ = v___y_4452_;
v___y_4566_ = v___y_4453_;
v___y_4567_ = v___y_4454_;
goto v___jp_4559_;
}
}
}
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_snd_4580_);
lean_dec(v___x_4471_);
lean_dec(v_instName_4467_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4636_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4597_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4597_);
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
v___jp_4646_:
{
if (lean_obj_tag(v___y_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4657_; 
v_a_4648_ = lean_ctor_get(v___y_4647_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___y_4647_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4650_ = v___y_4647_;
v_isShared_4651_ = v_isSharedCheck_4657_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___y_4647_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4657_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
if (lean_obj_tag(v_a_4648_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4654_; 
lean_dec(v___x_4471_);
lean_dec(v_instName_4467_);
lean_dec(v_a_4466_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4652_ = lean_ctor_get(v_a_4648_, 0);
lean_inc(v_a_4652_);
lean_dec_ref_known(v_a_4648_, 1);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 0, v_a_4652_);
v___x_4654_ = v___x_4650_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4652_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
else
{
lean_object* v_a_4656_; 
lean_del_object(v___x_4650_);
v_a_4656_ = lean_ctor_get(v_a_4648_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v_a_4648_, 1);
v_a_4576_ = v_a_4656_;
goto v___jp_4575_;
}
}
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
lean_dec(v___x_4471_);
lean_dec(v_instName_4467_);
lean_dec(v_a_4466_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4658_ = lean_ctor_get(v___y_4647_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___y_4647_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___y_4647_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___y_4647_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_dec(v_a_4461_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec_ref(v___f_4448_);
lean_dec(v_ctorName_4446_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4703_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4465_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4465_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec_ref(v___f_4448_);
lean_dec(v_ctorName_4446_);
lean_dec(v_inductiveTypeName_4443_);
v_a_4711_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4460_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4460_);
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
v___jp_4456_:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4458_, 0, v___y_4457_);
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
return v___x_4459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed(lean_object* v___x_4719_, lean_object* v___x_4720_, lean_object* v_inductiveTypeName_4721_, lean_object* v___x_4722_, lean_object* v___x_4723_, lean_object* v_ctorName_4724_, lean_object* v_addHypotheses_4725_, lean_object* v___f_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
uint8_t v___x_16435__boxed_4734_; uint8_t v_addHypotheses_boxed_4735_; lean_object* v_res_4736_; 
v___x_16435__boxed_4734_ = lean_unbox(v___x_4722_);
v_addHypotheses_boxed_4735_ = lean_unbox(v_addHypotheses_4725_);
v_res_4736_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1(v___x_4719_, v___x_4720_, v_inductiveTypeName_4721_, v___x_16435__boxed_4734_, v___x_4723_, v_ctorName_4724_, v_addHypotheses_boxed_4735_, v___f_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_);
lean_dec(v___x_4723_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(lean_object* v_inductiveTypeName_4739_, lean_object* v_ctorName_4740_, uint8_t v_addHypotheses_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_){
_start:
{
lean_object* v___f_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; uint8_t v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___f_4756_; uint8_t v___x_4757_; 
v___f_4749_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__0));
v___x_4750_ = lean_box(0);
v___x_4751_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_4752_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___closed__1));
v___x_4753_ = 1;
v___x_4754_ = lean_box(v___x_4753_);
v___x_4755_ = lean_box(v_addHypotheses_4741_);
lean_inc(v_ctorName_4740_);
v___f_4756_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___lam__1___boxed), 15, 8);
lean_closure_set(v___f_4756_, 0, v___x_4751_);
lean_closure_set(v___f_4756_, 1, v___x_4752_);
lean_closure_set(v___f_4756_, 2, v_inductiveTypeName_4739_);
lean_closure_set(v___f_4756_, 3, v___x_4754_);
lean_closure_set(v___f_4756_, 4, v___x_4750_);
lean_closure_set(v___f_4756_, 5, v_ctorName_4740_);
lean_closure_set(v___f_4756_, 6, v___x_4755_);
lean_closure_set(v___f_4756_, 7, v___f_4749_);
v___x_4757_ = l_Lean_isPrivateName(v_ctorName_4740_);
lean_dec(v_ctorName_4740_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; 
v___x_4758_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4756_, v___x_4753_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
return v___x_4758_;
}
else
{
uint8_t v___x_4759_; lean_object* v___x_4760_; 
v___x_4759_ = 0;
v___x_4760_ = l_Lean_withExporting___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f_spec__1___redArg(v___f_4756_, v___x_4759_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
return v___x_4760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed(lean_object* v_inductiveTypeName_4761_, lean_object* v_ctorName_4762_, lean_object* v_addHypotheses_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
uint8_t v_addHypotheses_boxed_4771_; lean_object* v_res_4772_; 
v_addHypotheses_boxed_4771_ = lean_unbox(v_addHypotheses_4763_);
v_res_4772_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f(v_inductiveTypeName_4761_, v_ctorName_4762_, v_addHypotheses_boxed_4771_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(lean_object* v_inductiveTypeName_4773_, lean_object* v_ctorName_4774_, uint8_t v_addHypotheses_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4779_ = lean_box(v_addHypotheses_4775_);
v___x_4780_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmd_x3f___boxed), 10, 3);
lean_closure_set(v___x_4780_, 0, v_inductiveTypeName_4773_);
lean_closure_set(v___x_4780_, 1, v_ctorName_4774_);
lean_closure_set(v___x_4780_, 2, v___x_4779_);
v___x_4781_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_4780_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4811_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4784_ = v___x_4781_;
v_isShared_4785_ = v_isSharedCheck_4811_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4781_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4811_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
if (lean_obj_tag(v_a_4782_) == 0)
{
uint8_t v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4789_; 
v___x_4786_ = 0;
v___x_4787_ = lean_box(v___x_4786_);
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 0, v___x_4787_);
v___x_4789_ = v___x_4784_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v___x_4787_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
else
{
lean_object* v_val_4791_; lean_object* v___x_4792_; 
lean_del_object(v___x_4784_);
v_val_4791_ = lean_ctor_get(v_a_4782_, 0);
lean_inc(v_val_4791_);
lean_dec_ref_known(v_a_4782_, 1);
v___x_4792_ = l_Lean_Elab_Command_elabCommand(v_val_4791_, v_a_4776_, v_a_4777_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4801_; 
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4801_ == 0)
{
lean_object* v_unused_4802_; 
v_unused_4802_ = lean_ctor_get(v___x_4792_, 0);
lean_dec(v_unused_4802_);
v___x_4794_ = v___x_4792_;
v_isShared_4795_ = v_isSharedCheck_4801_;
goto v_resetjp_4793_;
}
else
{
lean_dec(v___x_4792_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4801_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
uint8_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4799_; 
v___x_4796_ = 1;
v___x_4797_ = lean_box(v___x_4796_);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 0, v___x_4797_);
v___x_4799_ = v___x_4794_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4797_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
v_a_4803_ = lean_ctor_get(v___x_4792_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4792_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4792_);
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
}
}
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
v_a_4812_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v___x_4781_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4781_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing___boxed(lean_object* v_inductiveTypeName_4820_, lean_object* v_ctorName_4821_, lean_object* v_addHypotheses_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
uint8_t v_addHypotheses_boxed_4826_; lean_object* v_res_4827_; 
v_addHypotheses_boxed_4826_ = lean_unbox(v_addHypotheses_4822_);
v_res_4827_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_inductiveTypeName_4820_, v_ctorName_4821_, v_addHypotheses_boxed_4826_, v_a_4823_, v_a_4824_);
lean_dec(v_a_4824_);
lean_dec_ref(v_a_4823_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(lean_object* v_declName_4831_, uint8_t v_addHypotheses_4832_, lean_object* v_as_x27_4833_, lean_object* v_b_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
if (lean_obj_tag(v_as_x27_4833_) == 0)
{
lean_object* v___x_4838_; 
lean_dec(v_declName_4831_);
v___x_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4838_, 0, v_b_4834_);
return v___x_4838_;
}
else
{
lean_object* v_head_4839_; lean_object* v_tail_4840_; lean_object* v___x_4841_; 
lean_dec_ref(v_b_4834_);
v_head_4839_ = lean_ctor_get(v_as_x27_4833_, 0);
v_tail_4840_ = lean_ctor_get(v_as_x27_4833_, 1);
lean_inc(v_head_4839_);
lean_inc(v_declName_4831_);
v___x_4841_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing(v_declName_4831_, v_head_4839_, v_addHypotheses_4832_, v___y_4835_, v___y_4836_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4855_; 
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4844_ = v___x_4841_;
v_isShared_4845_ = v_isSharedCheck_4855_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4841_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4855_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4846_; uint8_t v___x_4847_; 
v___x_4846_ = lean_box(0);
v___x_4847_ = lean_unbox(v_a_4842_);
if (v___x_4847_ == 0)
{
lean_object* v___x_4848_; 
lean_del_object(v___x_4844_);
lean_dec(v_a_4842_);
v___x_4848_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v_as_x27_4833_ = v_tail_4840_;
v_b_4834_ = v___x_4848_;
goto _start;
}
else
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4853_; 
lean_dec(v_declName_4831_);
v___x_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4850_, 0, v_a_4842_);
v___x_4851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4850_);
lean_ctor_set(v___x_4851_, 1, v___x_4846_);
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 0, v___x_4851_);
v___x_4853_ = v___x_4844_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4851_);
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
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_dec(v_declName_4831_);
v_a_4856_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4841_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4841_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___boxed(lean_object* v_declName_4864_, lean_object* v_addHypotheses_4865_, lean_object* v_as_x27_4866_, lean_object* v_b_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
uint8_t v_addHypotheses_boxed_4871_; lean_object* v_res_4872_; 
v_addHypotheses_boxed_4871_ = lean_unbox(v_addHypotheses_4865_);
v_res_4872_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4864_, v_addHypotheses_boxed_4871_, v_as_x27_4866_, v_b_4867_, v___y_4868_, v___y_4869_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v_as_x27_4866_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(lean_object* v_a_4873_, lean_object* v_declName_4874_, uint8_t v_addHypotheses_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v_ctors_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v_ctors_4879_ = lean_ctor_get(v_a_4873_, 4);
v___x_4880_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg___closed__0));
v___x_4881_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_4874_, v_addHypotheses_4875_, v_ctors_4879_, v___x_4880_, v___y_4876_, v___y_4877_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4896_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4884_ = v___x_4881_;
v_isShared_4885_ = v_isSharedCheck_4896_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4881_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4896_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v_fst_4886_; 
v_fst_4886_ = lean_ctor_get(v_a_4882_, 0);
lean_inc(v_fst_4886_);
lean_dec(v_a_4882_);
if (lean_obj_tag(v_fst_4886_) == 0)
{
uint8_t v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4890_; 
v___x_4887_ = 0;
v___x_4888_ = lean_box(v___x_4887_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v___x_4888_);
v___x_4890_ = v___x_4884_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4888_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
else
{
lean_object* v_val_4892_; lean_object* v___x_4894_; 
v_val_4892_ = lean_ctor_get(v_fst_4886_, 0);
lean_inc(v_val_4892_);
lean_dec_ref_known(v_fst_4886_, 1);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v_val_4892_);
v___x_4894_ = v___x_4884_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_val_4892_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
v_a_4897_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4881_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4881_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0___boxed(lean_object* v_a_4905_, lean_object* v_declName_4906_, lean_object* v_addHypotheses_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
uint8_t v_addHypotheses_boxed_4911_; lean_object* v_res_4912_; 
v_addHypotheses_boxed_4911_ = lean_unbox(v_addHypotheses_4907_);
v_res_4912_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_4905_, v_declName_4906_, v_addHypotheses_boxed_4911_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec_ref(v_a_4905_);
return v_res_4912_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4913_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4914_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__0);
v___x_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
return v___x_4915_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4916_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4917_ = lean_unsigned_to_nat(0u);
v___x_4918_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
lean_ctor_set(v___x_4918_, 1, v___x_4917_);
lean_ctor_set(v___x_4918_, 2, v___x_4917_);
lean_ctor_set(v___x_4918_, 3, v___x_4917_);
lean_ctor_set(v___x_4918_, 4, v___x_4916_);
lean_ctor_set(v___x_4918_, 5, v___x_4916_);
lean_ctor_set(v___x_4918_, 6, v___x_4916_);
lean_ctor_set(v___x_4918_, 7, v___x_4916_);
lean_ctor_set(v___x_4918_, 8, v___x_4916_);
lean_ctor_set(v___x_4918_, 9, v___x_4916_);
lean_ctor_set(v___x_4918_, 10, v___x_4916_);
return v___x_4918_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4919_ = lean_unsigned_to_nat(32u);
v___x_4920_ = lean_mk_empty_array_with_capacity(v___x_4919_);
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
return v___x_4921_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4922_ = ((size_t)5ULL);
v___x_4923_ = lean_unsigned_to_nat(0u);
v___x_4924_ = lean_unsigned_to_nat(32u);
v___x_4925_ = lean_mk_empty_array_with_capacity(v___x_4924_);
v___x_4926_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__3);
v___x_4927_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
lean_ctor_set(v___x_4927_, 1, v___x_4925_);
lean_ctor_set(v___x_4927_, 2, v___x_4923_);
lean_ctor_set(v___x_4927_, 3, v___x_4923_);
lean_ctor_set_usize(v___x_4927_, 4, v___x_4922_);
return v___x_4927_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4928_ = lean_box(1);
v___x_4929_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__4);
v___x_4930_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__1);
v___x_4931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
lean_ctor_set(v___x_4931_, 1, v___x_4929_);
lean_ctor_set(v___x_4931_, 2, v___x_4928_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(lean_object* v_msgData_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v___x_4935_; lean_object* v_env_4936_; lean_object* v___x_4937_; lean_object* v_scopes_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v_opts_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4935_ = lean_st_ref_get(v___y_4933_);
v_env_4936_ = lean_ctor_get(v___x_4935_, 0);
lean_inc_ref(v_env_4936_);
lean_dec(v___x_4935_);
v___x_4937_ = lean_st_ref_get(v___y_4933_);
v_scopes_4938_ = lean_ctor_get(v___x_4937_, 2);
lean_inc(v_scopes_4938_);
lean_dec(v___x_4937_);
v___x_4939_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4940_ = l_List_head_x21___redArg(v___x_4939_, v_scopes_4938_);
lean_dec(v_scopes_4938_);
v_opts_4941_ = lean_ctor_get(v___x_4940_, 1);
lean_inc_ref(v_opts_4941_);
lean_dec(v___x_4940_);
v___x_4942_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__2);
v___x_4943_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___closed__5);
v___x_4944_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4944_, 0, v_env_4936_);
lean_ctor_set(v___x_4944_, 1, v___x_4942_);
lean_ctor_set(v___x_4944_, 2, v___x_4943_);
lean_ctor_set(v___x_4944_, 3, v_opts_4941_);
v___x_4945_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
lean_ctor_set(v___x_4945_, 1, v_msgData_4932_);
v___x_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4945_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_4947_, v___y_4948_);
lean_dec(v___y_4948_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(lean_object* v_msgData_4951_, lean_object* v_macroStack_4952_, lean_object* v___y_4953_){
_start:
{
lean_object* v___x_4955_; lean_object* v_scopes_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v_opts_4959_; lean_object* v___x_4960_; uint8_t v___x_4961_; 
v___x_4955_ = lean_st_ref_get(v___y_4953_);
v_scopes_4956_ = lean_ctor_get(v___x_4955_, 2);
lean_inc(v_scopes_4956_);
lean_dec(v___x_4955_);
v___x_4957_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4958_ = l_List_head_x21___redArg(v___x_4957_, v_scopes_4956_);
lean_dec(v_scopes_4956_);
v_opts_4959_ = lean_ctor_get(v___x_4958_, 1);
lean_inc_ref(v_opts_4959_);
lean_dec(v___x_4958_);
v___x_4960_ = l_Lean_Elab_pp_macroStack;
v___x_4961_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__4(v_opts_4959_, v___x_4960_);
lean_dec_ref(v_opts_4959_);
if (v___x_4961_ == 0)
{
lean_object* v___x_4962_; 
lean_dec(v_macroStack_4952_);
v___x_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4962_, 0, v_msgData_4951_);
return v___x_4962_;
}
else
{
if (lean_obj_tag(v_macroStack_4952_) == 0)
{
lean_object* v___x_4963_; 
v___x_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4963_, 0, v_msgData_4951_);
return v___x_4963_;
}
else
{
lean_object* v_head_4964_; lean_object* v_after_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4980_; 
v_head_4964_ = lean_ctor_get(v_macroStack_4952_, 0);
lean_inc(v_head_4964_);
v_after_4965_ = lean_ctor_get(v_head_4964_, 1);
v_isSharedCheck_4980_ = !lean_is_exclusive(v_head_4964_);
if (v_isSharedCheck_4980_ == 0)
{
lean_object* v_unused_4981_; 
v_unused_4981_ = lean_ctor_get(v_head_4964_, 0);
lean_dec(v_unused_4981_);
v___x_4967_ = v_head_4964_;
v_isShared_4968_ = v_isSharedCheck_4980_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_after_4965_);
lean_dec(v_head_4964_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4980_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4969_; lean_object* v___x_4971_; 
v___x_4969_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5___closed__0);
if (v_isShared_4968_ == 0)
{
lean_ctor_set_tag(v___x_4967_, 7);
lean_ctor_set(v___x_4967_, 1, v___x_4969_);
lean_ctor_set(v___x_4967_, 0, v_msgData_4951_);
v___x_4971_ = v___x_4967_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_msgData_4951_);
lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___x_4969_);
v___x_4971_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v_msgData_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4972_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_4973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4971_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
v___x_4974_ = l_Lean_MessageData_ofSyntax(v_after_4965_);
v___x_4975_ = l_Lean_indentD(v___x_4974_);
v_msgData_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4976_, 0, v___x_4973_);
lean_ctor_set(v_msgData_4976_, 1, v___x_4975_);
v___x_4977_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1_spec__1_spec__2_spec__5(v_msgData_4976_, v_macroStack_4952_);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
return v___x_4978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_4982_, lean_object* v_macroStack_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_4982_, v_macroStack_4983_, v___y_4984_);
lean_dec(v___y_4984_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(lean_object* v_msg_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = l_Lean_Elab_Command_getRef___redArg(v___y_4988_);
if (lean_obj_tag(v___x_4991_) == 0)
{
lean_object* v_a_4992_; lean_object* v_macroStack_4993_; lean_object* v___x_4994_; lean_object* v_a_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5006_; 
v_a_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_a_4992_);
lean_dec_ref_known(v___x_4991_, 1);
v_macroStack_4993_ = lean_ctor_get(v___y_4988_, 4);
v___x_4994_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msg_4987_, v___y_4989_);
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_a_4995_);
lean_dec_ref(v___x_4994_);
v___x_4996_ = l_Lean_Elab_getBetterRef(v_a_4992_, v_macroStack_4993_);
lean_dec(v_a_4992_);
lean_inc(v_macroStack_4993_);
v___x_4997_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_a_4995_, v_macroStack_4993_, v___y_4989_);
v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5000_ = v___x_4997_;
v_isShared_5001_ = v_isSharedCheck_5006_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4997_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5006_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5002_; lean_object* v___x_5004_; 
v___x_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_4996_);
lean_ctor_set(v___x_5002_, 1, v_a_4998_);
if (v_isShared_5001_ == 0)
{
lean_ctor_set_tag(v___x_5000_, 1);
lean_ctor_set(v___x_5000_, 0, v___x_5002_);
v___x_5004_ = v___x_5000_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_5002_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5014_; 
lean_dec_ref(v_msg_4987_);
v_a_5007_ = lean_ctor_get(v___x_4991_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4991_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5009_ = v___x_4991_;
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_4991_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_a_5007_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg___boxed(lean_object* v_msg_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5015_, v___y_5016_, v___y_5017_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(lean_object* v_constName_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
lean_object* v___x_5024_; lean_object* v_env_5025_; lean_object* v___x_5026_; 
v___x_5024_ = lean_st_ref_get(v___y_5022_);
v_env_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc_ref(v_env_5025_);
lean_dec(v___x_5024_);
lean_inc(v_constName_5020_);
v___x_5026_ = l_Lean_isInductiveCore_x3f(v_env_5025_, v_constName_5020_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_object* v___x_5027_; uint8_t v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5027_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5028_ = 0;
v___x_5029_ = l_Lean_MessageData_ofConstName(v_constName_5020_, v___x_5028_);
v___x_5030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5027_);
lean_ctor_set(v___x_5030_, 1, v___x_5029_);
v___x_5031_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__3);
v___x_5032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5030_);
lean_ctor_set(v___x_5032_, 1, v___x_5031_);
v___x_5033_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5032_, v___y_5021_, v___y_5022_);
return v___x_5033_;
}
else
{
lean_object* v_val_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_dec(v_constName_5020_);
v_val_5034_ = lean_ctor_get(v___x_5026_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5026_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_5026_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_val_5034_);
lean_dec(v___x_5026_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
lean_ctor_set_tag(v___x_5036_, 0);
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_val_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0___boxed(lean_object* v_constName_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_constName_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
return v_res_5046_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5048_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__0));
v___x_5049_ = l_Lean_stringToMessageData(v___x_5048_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(lean_object* v_declName_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
lean_object* v___x_5057_; 
lean_inc(v_declName_5050_);
v___x_5057_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__0(v_declName_5050_, v___y_5051_, v___y_5052_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; uint8_t v___x_5059_; lean_object* v___x_5060_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v___x_5059_ = 0;
lean_inc(v_declName_5050_);
v___x_5060_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5058_, v_declName_5050_, v___x_5059_, v___y_5051_, v___y_5052_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; uint8_t v___x_5062_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v___x_5062_ = lean_unbox(v_a_5061_);
lean_dec(v_a_5061_);
if (v___x_5062_ == 0)
{
uint8_t v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = 1;
lean_inc(v_declName_5050_);
v___x_5064_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__0(v_a_5058_, v_declName_5050_, v___x_5063_, v___y_5051_, v___y_5052_);
lean_dec(v_a_5058_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_a_5065_; uint8_t v___x_5066_; 
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref_known(v___x_5064_, 1);
v___x_5066_ = lean_unbox(v_a_5065_);
lean_dec(v_a_5065_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5067_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1, &l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1_once, _init_l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___closed__1);
v___x_5068_ = l_Lean_MessageData_ofConstName(v_declName_5050_, v___x_5059_);
v___x_5069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5067_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
v___x_5070_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_mkInstanceCmdWith_spec__1___closed__1);
v___x_5071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5069_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v___x_5071_, v___y_5051_, v___y_5052_);
return v___x_5072_;
}
else
{
lean_dec(v_declName_5050_);
goto v___jp_5054_;
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
lean_dec(v_declName_5050_);
v_a_5073_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5064_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5064_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
else
{
lean_dec(v_a_5058_);
lean_dec(v_declName_5050_);
goto v___jp_5054_;
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
lean_dec(v_a_5058_);
lean_dec(v_declName_5050_);
v_a_5081_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5060_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5060_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
lean_dec(v_declName_5050_);
v_a_5089_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___x_5057_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5057_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
v___jp_5054_:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5055_ = lean_box(0);
v___x_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5055_);
return v___x_5056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed(lean_object* v_declName_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1(v_declName_5097_, v___y_5098_, v___y_5099_);
lean_dec(v___y_5099_);
lean_dec_ref(v___y_5098_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(lean_object* v_declName_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v___f_5106_; lean_object* v___x_5107_; 
lean_inc(v_declName_5102_);
v___f_5106_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5106_, 0, v_declName_5102_);
v___x_5107_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_5102_, v___f_5106_, v_a_5103_, v_a_5104_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance___boxed(lean_object* v_declName_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v_declName_5108_, v_a_5109_, v_a_5110_);
lean_dec(v_a_5110_);
lean_dec_ref(v_a_5109_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(lean_object* v_declName_5113_, uint8_t v_addHypotheses_5114_, lean_object* v_as_5115_, lean_object* v_as_x27_5116_, lean_object* v_b_5117_, lean_object* v_a_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v___x_5122_; 
v___x_5122_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___redArg(v_declName_5113_, v_addHypotheses_5114_, v_as_x27_5116_, v_b_5117_, v___y_5119_, v___y_5120_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1___boxed(lean_object* v_declName_5123_, lean_object* v_addHypotheses_5124_, lean_object* v_as_5125_, lean_object* v_as_x27_5126_, lean_object* v_b_5127_, lean_object* v_a_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
uint8_t v_addHypotheses_boxed_5132_; lean_object* v_res_5133_; 
v_addHypotheses_boxed_5132_ = lean_unbox(v_addHypotheses_5124_);
v_res_5133_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__1(v_declName_5123_, v_addHypotheses_boxed_5132_, v_as_5125_, v_as_x27_5126_, v_b_5127_, v_a_5128_, v___y_5129_, v___y_5130_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec(v_as_x27_5126_);
lean_dec(v_as_5125_);
return v_res_5133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(lean_object* v_msgData_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v___x_5138_; 
v___x_5138_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___redArg(v_msgData_5134_, v___y_5136_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2___boxed(lean_object* v_msgData_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__2(v_msgData_5139_, v___y_5140_, v___y_5141_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(lean_object* v_00_u03b1_5144_, lean_object* v_msg_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___redArg(v_msg_5145_, v___y_5146_, v___y_5147_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2___boxed(lean_object* v_00_u03b1_5150_, lean_object* v_msg_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2(v_00_u03b1_5150_, v_msg_5151_, v___y_5152_, v___y_5153_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(lean_object* v_msgData_5156_, lean_object* v_macroStack_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
lean_object* v___x_5161_; 
v___x_5161_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___redArg(v_msgData_5156_, v_macroStack_5157_, v___y_5159_);
return v___x_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3___boxed(lean_object* v_msgData_5162_, lean_object* v_macroStack_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance_spec__2_spec__3(v_msgData_5162_, v_macroStack_5163_, v___y_5164_, v___y_5165_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(lean_object* v_declName_5168_, lean_object* v___y_5169_){
_start:
{
lean_object* v___x_5171_; lean_object* v_env_5172_; uint8_t v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; 
v___x_5171_ = lean_st_ref_get(v___y_5169_);
v_env_5172_ = lean_ctor_get(v___x_5171_, 0);
lean_inc_ref(v_env_5172_);
lean_dec(v___x_5171_);
v___x_5173_ = l_Lean_isInductiveCore(v_env_5172_, v_declName_5168_);
v___x_5174_ = lean_box(v___x_5173_);
v___x_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5175_, 0, v___x_5174_);
return v___x_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5176_, v___y_5177_);
lean_dec(v___y_5177_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(lean_object* v_declName_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_){
_start:
{
lean_object* v___x_5184_; 
v___x_5184_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v_declName_5180_, v___y_5182_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___boxed(lean_object* v_declName_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0(v_declName_5185_, v___y_5186_, v___y_5187_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(uint8_t v_____do__lift_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
if (v_____do__lift_5190_ == 0)
{
uint8_t v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5194_ = 1;
v___x_5195_ = lean_box(v___x_5194_);
v___x_5196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5195_);
return v___x_5196_;
}
else
{
uint8_t v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5197_ = 0;
v___x_5198_ = lean_box(v___x_5197_);
v___x_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5198_);
return v___x_5199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
uint8_t v_____do__lift_1590__boxed_5204_; lean_object* v_res_5205_; 
v_____do__lift_1590__boxed_5204_ = lean_unbox(v_____do__lift_5200_);
v_res_5205_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v_____do__lift_1590__boxed_5204_, v___y_5201_, v___y_5202_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(lean_object* v_as_5206_, size_t v_i_5207_, size_t v_stop_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
uint8_t v___x_5216_; 
v___x_5216_ = lean_usize_dec_eq(v_i_5207_, v_stop_5208_);
if (v___x_5216_ == 0)
{
uint8_t v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v___x_5217_ = 1;
v___x_5218_ = lean_array_uget_borrowed(v_as_5206_, v_i_5207_);
lean_inc(v___x_5218_);
v___x_5219_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__0___redArg(v___x_5218_, v___y_5210_);
if (lean_obj_tag(v___x_5219_) == 0)
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5229_; 
v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5222_ = v___x_5219_;
v_isShared_5223_ = v_isSharedCheck_5229_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5219_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5229_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
uint8_t v___x_5224_; 
v___x_5224_ = lean_unbox(v_a_5220_);
lean_dec(v_a_5220_);
if (v___x_5224_ == 0)
{
lean_object* v___x_5225_; lean_object* v___x_5227_; 
v___x_5225_ = lean_box(v___x_5217_);
if (v_isShared_5223_ == 0)
{
lean_ctor_set(v___x_5222_, 0, v___x_5225_);
v___x_5227_ = v___x_5222_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v___x_5225_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
else
{
lean_del_object(v___x_5222_);
goto v___jp_5212_;
}
}
}
else
{
if (lean_obj_tag(v___x_5219_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5239_; 
v_a_5230_ = lean_ctor_get(v___x_5219_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5232_ = v___x_5219_;
v_isShared_5233_ = v_isSharedCheck_5239_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5219_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5239_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
uint8_t v___x_5234_; 
v___x_5234_ = lean_unbox(v_a_5230_);
lean_dec(v_a_5230_);
if (v___x_5234_ == 0)
{
lean_del_object(v___x_5232_);
goto v___jp_5212_;
}
else
{
lean_object* v___x_5235_; lean_object* v___x_5237_; 
v___x_5235_ = lean_box(v___x_5217_);
if (v_isShared_5233_ == 0)
{
lean_ctor_set_tag(v___x_5232_, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5235_);
v___x_5237_ = v___x_5232_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5235_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
return v___x_5237_;
}
}
}
}
else
{
return v___x_5219_;
}
}
}
else
{
uint8_t v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
v___x_5240_ = 0;
v___x_5241_ = lean_box(v___x_5240_);
v___x_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5241_);
return v___x_5242_;
}
v___jp_5212_:
{
size_t v___x_5213_; size_t v___x_5214_; 
v___x_5213_ = ((size_t)1ULL);
v___x_5214_ = lean_usize_add(v_i_5207_, v___x_5213_);
v_i_5207_ = v___x_5214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2___boxed(lean_object* v_as_5243_, lean_object* v_i_5244_, lean_object* v_stop_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
size_t v_i_boxed_5249_; size_t v_stop_boxed_5250_; lean_object* v_res_5251_; 
v_i_boxed_5249_ = lean_unbox_usize(v_i_5244_);
lean_dec(v_i_5244_);
v_stop_boxed_5250_ = lean_unbox_usize(v_stop_5245_);
lean_dec(v_stop_5245_);
v_res_5251_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_as_5243_, v_i_boxed_5249_, v_stop_boxed_5250_, v___y_5246_, v___y_5247_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec_ref(v_as_5243_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(lean_object* v_as_5252_, size_t v_i_5253_, size_t v_stop_5254_, lean_object* v_b_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
uint8_t v___x_5259_; 
v___x_5259_ = lean_usize_dec_eq(v_i_5253_, v_stop_5254_);
if (v___x_5259_ == 0)
{
lean_object* v___x_5260_; lean_object* v___x_5261_; 
v___x_5260_ = lean_array_uget_borrowed(v_as_5252_, v_i_5253_);
lean_inc(v___x_5260_);
v___x_5261_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstance(v___x_5260_, v___y_5256_, v___y_5257_);
if (lean_obj_tag(v___x_5261_) == 0)
{
lean_object* v_a_5262_; size_t v___x_5263_; size_t v___x_5264_; 
v_a_5262_ = lean_ctor_get(v___x_5261_, 0);
lean_inc(v_a_5262_);
lean_dec_ref_known(v___x_5261_, 1);
v___x_5263_ = ((size_t)1ULL);
v___x_5264_ = lean_usize_add(v_i_5253_, v___x_5263_);
v_i_5253_ = v___x_5264_;
v_b_5255_ = v_a_5262_;
goto _start;
}
else
{
return v___x_5261_;
}
}
else
{
lean_object* v___x_5266_; 
v___x_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5266_, 0, v_b_5255_);
return v___x_5266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1___boxed(lean_object* v_as_5267_, lean_object* v_i_5268_, lean_object* v_stop_5269_, lean_object* v_b_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
size_t v_i_boxed_5274_; size_t v_stop_boxed_5275_; lean_object* v_res_5276_; 
v_i_boxed_5274_ = lean_unbox_usize(v_i_5268_);
lean_dec(v_i_5268_);
v_stop_boxed_5275_ = lean_unbox_usize(v_stop_5269_);
lean_dec(v_stop_5269_);
v_res_5276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_as_5267_, v_i_boxed_5274_, v_stop_boxed_5275_, v_b_5270_, v___y_5271_, v___y_5272_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec_ref(v_as_5267_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(lean_object* v_declNames_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_){
_start:
{
uint8_t v___y_5282_; lean_object* v___y_5283_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___y_5319_; uint8_t v___x_5322_; 
v___x_5301_ = lean_unsigned_to_nat(0u);
v___x_5302_ = lean_array_get_size(v_declNames_5277_);
v___x_5322_ = lean_nat_dec_lt(v___x_5301_, v___x_5302_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; 
v___x_5323_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5322_, v_a_5278_, v_a_5279_);
v___y_5319_ = v___x_5323_;
goto v___jp_5318_;
}
else
{
if (v___x_5322_ == 0)
{
goto v___jp_5303_;
}
else
{
size_t v___x_5324_; size_t v___x_5325_; lean_object* v___x_5326_; 
v___x_5324_ = ((size_t)0ULL);
v___x_5325_ = lean_usize_of_nat(v___x_5302_);
v___x_5326_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__2(v_declNames_5277_, v___x_5324_, v___x_5325_, v_a_5278_, v_a_5279_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; uint8_t v___x_5328_; lean_object* v___x_5329_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
lean_inc(v_a_5327_);
lean_dec_ref_known(v___x_5326_, 1);
v___x_5328_ = lean_unbox(v_a_5327_);
lean_dec(v_a_5327_);
v___x_5329_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___lam__0(v___x_5328_, v_a_5278_, v_a_5279_);
v___y_5319_ = v___x_5329_;
goto v___jp_5318_;
}
else
{
v___y_5319_ = v___x_5326_;
goto v___jp_5318_;
}
}
}
v___jp_5281_:
{
if (lean_obj_tag(v___y_5283_) == 0)
{
lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5291_; 
v_isSharedCheck_5291_ = !lean_is_exclusive(v___y_5283_);
if (v_isSharedCheck_5291_ == 0)
{
lean_object* v_unused_5292_; 
v_unused_5292_ = lean_ctor_get(v___y_5283_, 0);
lean_dec(v_unused_5292_);
v___x_5285_ = v___y_5283_;
v_isShared_5286_ = v_isSharedCheck_5291_;
goto v_resetjp_5284_;
}
else
{
lean_dec(v___y_5283_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5291_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v___x_5287_; lean_object* v___x_5289_; 
v___x_5287_ = lean_box(v___y_5282_);
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 0, v___x_5287_);
v___x_5289_ = v___x_5285_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v___x_5287_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
else
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5300_; 
v_a_5293_ = lean_ctor_get(v___y_5283_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___y_5283_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5295_ = v___y_5283_;
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___y_5283_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5298_; 
if (v_isShared_5296_ == 0)
{
v___x_5298_ = v___x_5295_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5293_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
}
}
v___jp_5303_:
{
uint8_t v___x_5304_; uint8_t v___x_5305_; 
v___x_5304_ = 1;
v___x_5305_ = lean_nat_dec_lt(v___x_5301_, v___x_5302_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5306_ = lean_box(v___x_5304_);
v___x_5307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5307_, 0, v___x_5306_);
return v___x_5307_;
}
else
{
lean_object* v___x_5308_; uint8_t v___x_5309_; 
v___x_5308_ = lean_box(0);
v___x_5309_ = lean_nat_dec_le(v___x_5302_, v___x_5302_);
if (v___x_5309_ == 0)
{
if (v___x_5305_ == 0)
{
lean_object* v___x_5310_; lean_object* v___x_5311_; 
v___x_5310_ = lean_box(v___x_5304_);
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5310_);
return v___x_5311_;
}
else
{
size_t v___x_5312_; size_t v___x_5313_; lean_object* v___x_5314_; 
v___x_5312_ = ((size_t)0ULL);
v___x_5313_ = lean_usize_of_nat(v___x_5302_);
v___x_5314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5277_, v___x_5312_, v___x_5313_, v___x_5308_, v_a_5278_, v_a_5279_);
v___y_5282_ = v___x_5304_;
v___y_5283_ = v___x_5314_;
goto v___jp_5281_;
}
}
else
{
size_t v___x_5315_; size_t v___x_5316_; lean_object* v___x_5317_; 
v___x_5315_ = ((size_t)0ULL);
v___x_5316_ = lean_usize_of_nat(v___x_5302_);
v___x_5317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_mkInhabitedInstanceHandler_spec__1(v_declNames_5277_, v___x_5315_, v___x_5316_, v___x_5308_, v_a_5278_, v_a_5279_);
v___y_5282_ = v___x_5304_;
v___y_5283_ = v___x_5317_;
goto v___jp_5281_;
}
}
}
v___jp_5318_:
{
if (lean_obj_tag(v___y_5319_) == 0)
{
lean_object* v_a_5320_; uint8_t v___x_5321_; 
v_a_5320_ = lean_ctor_get(v___y_5319_, 0);
v___x_5321_ = lean_unbox(v_a_5320_);
if (v___x_5321_ == 0)
{
return v___y_5319_;
}
else
{
lean_dec_ref_known(v___y_5319_, 1);
goto v___jp_5303_;
}
}
else
{
return v___y_5319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_mkInhabitedInstanceHandler___boxed(lean_object* v_declNames_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_){
_start:
{
lean_object* v_res_5334_; 
v_res_5334_ = l_Lean_Elab_Deriving_mkInhabitedInstanceHandler(v_declNames_5330_, v_a_5331_, v_a_5332_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec_ref(v_declNames_5330_);
return v_res_5334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5399_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___closed__1));
v___x_5400_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__0_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5401_ = l_Lean_Elab_registerDerivingHandler(v___x_5399_, v___x_5400_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_object* v___x_5402_; uint8_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
lean_dec_ref_known(v___x_5401_, 1);
v___x_5402_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_mkInhabitedInstanceUsing_addLocalInstancesForParamsAux___redArg___lam__0___closed__3));
v___x_5403_ = 0;
v___x_5404_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn___closed__24_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_));
v___x_5405_ = l_Lean_registerTraceClass(v___x_5402_, v___x_5403_, v___x_5404_);
return v___x_5405_;
}
else
{
return v___x_5401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2____boxed(lean_object* v_a_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l___private_Lean_Elab_Deriving_Inhabited_0__Lean_Elab_Deriving_initFn_00___x40_Lean_Elab_Deriving_Inhabited_1810264634____hygCtx___hyg_2_();
return v_res_5407_;
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
