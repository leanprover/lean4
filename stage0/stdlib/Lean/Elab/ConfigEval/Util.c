// Lean compiler output
// Module: Lean.Elab.ConfigEval.Util
// Imports: public import Lean.Elab.Command
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SynthInstance_getInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_==_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 251, 60, 160, 118, 54, 158, 27)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__1_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__2_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__3 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__3_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__4 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_makeStringMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_makeStringMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cyclic dependency on "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1;
static const lean_array_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "dependency has metavariables: "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigEval"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 88, 216, 244, 195, 195, 232, 169)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inst for `"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "` deps: "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inst: "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tryInst "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "extra deps for `"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "num insts for `"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", type: "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "plan: "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", processing: "};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "derivation plan `"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "` for `"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1;
static lean_once_cell_t l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "failure deriving instance for `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "added instance of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " for  `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_withClassInstDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_withClassInstDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__3_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__3_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__3_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__4_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__3_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__4_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__4_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__5_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__4_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(49, 58, 181, 5, 236, 53, 126, 112)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__5_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__5_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__7_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__5_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 244, 102, 227, 17, 49, 93, 235)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__7_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__7_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__8_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__7_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(46, 86, 175, 20, 156, 39, 237, 63)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__8_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__8_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__9_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__8_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 99, 187, 26, 97, 148, 46, 129)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__9_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__9_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__10_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__9_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 196, 28, 65, 54, 184, 83, 124)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__10_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__10_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__11_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__10_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 149, 234, 220, 176, 158, 110, 35)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__11_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__11_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__12_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__12_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__12_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__13_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__11_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__12_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 146, 233, 85, 230, 183, 29, 31)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__13_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__13_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__14_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__14_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__14_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__15_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__13_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__14_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 25, 214, 139, 169, 123, 212, 253)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__15_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__15_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__16_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__15_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 143, 223, 156, 141, 74, 141, 210)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__16_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__16_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__17_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__16_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 9, 137, 19, 191, 230, 38, 77)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__17_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__17_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__18_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__17_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 189, 234, 214, 39, 149, 2, 26)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__18_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__18_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__19_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__18_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__6_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 163, 164, 122, 24, 133, 22, 124)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__19_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__19_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__20_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__19_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1975219684) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(164, 217, 39, 207, 160, 189, 162, 71)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__20_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__20_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__21_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__21_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__21_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__22_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__20_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__21_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 204, 139, 154, 41, 189, 163, 36)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__22_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__22_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__23_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__23_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__23_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__24_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__22_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__23_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 127, 153, 141, 44, 255, 172, 234)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__24_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__24_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__24_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(94, 92, 131, 114, 55, 232, 140, 2)}};
static const lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(lean_object* v_discr_11_, lean_object* v_as_12_, size_t v_i_13_, size_t v_stop_14_, lean_object* v_b_15_, lean_object* v___y_16_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_usize_dec_eq(v_i_13_, v_stop_14_);
if (v___x_18_ == 0)
{
size_t v___x_19_; size_t v___x_20_; lean_object* v___x_21_; lean_object* v_fst_22_; lean_object* v_snd_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_46_; 
v___x_19_ = ((size_t)1ULL);
v___x_20_ = lean_usize_sub(v_i_13_, v___x_19_);
v___x_21_ = lean_array_uget(v_as_12_, v___x_20_);
v_fst_22_ = lean_ctor_get(v___x_21_, 0);
v_snd_23_ = lean_ctor_get(v___x_21_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_46_ == 0)
{
v___x_25_ = v___x_21_;
v_isShared_26_ = v_isSharedCheck_46_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_snd_23_);
lean_inc(v_fst_22_);
lean_dec(v___x_21_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_46_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v_ref_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v_ref_27_ = lean_ctor_get(v___y_16_, 2);
v___x_28_ = l_Lean_SourceInfo_fromRef(v_ref_27_, v___x_18_);
v___x_29_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1));
v___x_30_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2));
lean_inc(v___x_28_);
if (v_isShared_26_ == 0)
{
lean_ctor_set_tag(v___x_25_, 2);
lean_ctor_set(v___x_25_, 1, v___x_30_);
lean_ctor_set(v___x_25_, 0, v___x_28_);
v___x_32_ = v___x_25_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___x_30_);
v___x_32_ = v_reuseFailAlloc_45_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_33_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__4));
v___x_34_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__5));
lean_inc_n(v___x_28_, 4);
v___x_35_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_28_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v___x_36_ = lean_box(2);
v___x_37_ = l_Lean_Syntax_mkStrLit(v_fst_22_, v___x_36_);
lean_inc(v_discr_11_);
v___x_38_ = l_Lean_Syntax_node3(v___x_28_, v___x_33_, v_discr_11_, v___x_35_, v___x_37_);
v___x_39_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6));
v___x_40_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_28_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7));
v___x_42_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_28_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = l_Lean_Syntax_node6(v___x_28_, v___x_29_, v___x_32_, v___x_38_, v___x_40_, v_snd_23_, v___x_42_, v_b_15_);
v_i_13_ = v___x_20_;
v_b_15_ = v___x_43_;
goto _start;
}
}
}
else
{
lean_object* v___x_47_; 
lean_dec(v_discr_11_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v_b_15_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___boxed(lean_object* v_discr_48_, lean_object* v_as_49_, lean_object* v_i_50_, lean_object* v_stop_51_, lean_object* v_b_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
size_t v_i_boxed_55_; size_t v_stop_boxed_56_; lean_object* v_res_57_; 
v_i_boxed_55_ = lean_unbox_usize(v_i_50_);
lean_dec(v_i_50_);
v_stop_boxed_56_ = lean_unbox_usize(v_stop_51_);
lean_dec(v_stop_51_);
v_res_57_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(v_discr_48_, v_as_49_, v_i_boxed_55_, v_stop_boxed_56_, v_b_52_, v___y_53_);
lean_dec_ref(v___y_53_);
lean_dec_ref(v_as_49_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(lean_object* v_discr_66_, lean_object* v_onFail_67_, lean_object* v_start_68_, lean_object* v_stop_69_, lean_object* v_cases_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = lean_nat_sub(v_stop_69_, v_start_68_);
v___x_79_ = lean_unsigned_to_nat(5u);
v___x_80_ = lean_nat_dec_le(v___x_78_, v___x_79_);
lean_dec(v___x_78_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v_mid_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_fst_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_119_; 
v___x_81_ = lean_nat_add(v_start_68_, v_stop_69_);
v___x_82_ = lean_unsigned_to_nat(1u);
v_mid_83_ = lean_nat_shiftr(v___x_81_, v___x_82_);
lean_dec(v___x_81_);
v___x_84_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__1));
v___x_85_ = lean_array_get(v___x_84_, v_cases_70_, v_mid_83_);
v_fst_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v___x_85_, 1);
lean_dec(v_unused_120_);
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_119_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_fst_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_119_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; 
lean_inc_ref(v_cases_70_);
lean_inc(v_mid_83_);
lean_inc(v_onFail_67_);
lean_inc(v_discr_66_);
v___x_90_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(v_discr_66_, v_onFail_67_, v_start_68_, v_mid_83_, v_cases_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
lean_inc(v_discr_66_);
v___x_92_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(v_discr_66_, v_onFail_67_, v_mid_83_, v_stop_69_, v_cases_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_118_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_118_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_118_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_118_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v_ref_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v_ref_97_ = lean_ctor_get(v_a_75_, 2);
v___x_98_ = l_Lean_SourceInfo_fromRef(v_ref_97_, v___x_80_);
v___x_99_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__1));
v___x_100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__2));
lean_inc(v___x_98_);
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 2);
lean_ctor_set(v___x_88_, 1, v___x_100_);
lean_ctor_set(v___x_88_, 0, v___x_98_);
v___x_102_ = v___x_88_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_100_);
v___x_102_ = v_reuseFailAlloc_117_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_103_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__3));
v___x_104_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__4));
lean_inc_n(v___x_98_, 4);
v___x_105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_98_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_box(2);
v___x_107_ = l_Lean_Syntax_mkStrLit(v_fst_86_, v___x_106_);
v___x_108_ = l_Lean_Syntax_node3(v___x_98_, v___x_103_, v_discr_66_, v___x_105_, v___x_107_);
v___x_109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__6));
v___x_110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_98_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg___closed__7));
v___x_112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_98_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = l_Lean_Syntax_node6(v___x_98_, v___x_99_, v___x_102_, v___x_108_, v___x_110_, v_a_91_, v___x_112_, v_a_93_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_113_);
v___x_115_ = v___x_95_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_dec(v_a_91_);
lean_del_object(v___x_88_);
lean_dec(v_fst_86_);
lean_dec(v_discr_66_);
return v___x_92_;
}
}
else
{
lean_del_object(v___x_88_);
lean_dec(v_fst_86_);
lean_dec(v_mid_83_);
lean_dec_ref(v_cases_70_);
lean_dec(v_stop_69_);
lean_dec(v_onFail_67_);
lean_dec(v_discr_66_);
return v___x_90_;
}
}
}
else
{
lean_object* v___x_121_; lean_object* v_array_122_; lean_object* v_start_123_; lean_object* v_stop_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_121_ = l_Array_toSubarray___redArg(v_cases_70_, v_start_68_, v_stop_69_);
v_array_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc_ref(v_array_122_);
v_start_123_ = lean_ctor_get(v___x_121_, 1);
lean_inc(v_start_123_);
v_stop_124_ = lean_ctor_get(v___x_121_, 2);
lean_inc(v_stop_124_);
lean_dec_ref(v___x_121_);
v___x_125_ = lean_array_get_size(v_array_122_);
v___x_126_ = lean_nat_dec_le(v_stop_124_, v___x_125_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
lean_dec(v_stop_124_);
v___x_127_ = lean_nat_dec_lt(v_start_123_, v___x_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
lean_dec(v_start_123_);
lean_dec_ref(v_array_122_);
lean_dec(v_discr_66_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v_onFail_67_);
return v___x_128_;
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_usize_of_nat(v___x_125_);
v___x_130_ = lean_usize_of_nat(v_start_123_);
lean_dec(v_start_123_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(v_discr_66_, v_array_122_, v___x_129_, v___x_130_, v_onFail_67_, v_a_75_);
lean_dec_ref(v_array_122_);
return v___x_131_;
}
}
else
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_lt(v_start_123_, v_stop_124_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_dec(v_stop_124_);
lean_dec(v_start_123_);
lean_dec_ref(v_array_122_);
lean_dec(v_discr_66_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_onFail_67_);
return v___x_133_;
}
else
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_usize_of_nat(v_stop_124_);
lean_dec(v_stop_124_);
v___x_135_ = lean_usize_of_nat(v_start_123_);
lean_dec(v_start_123_);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(v_discr_66_, v_array_122_, v___x_134_, v___x_135_, v_onFail_67_, v_a_75_);
lean_dec_ref(v_array_122_);
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___boxed(lean_object* v_discr_137_, lean_object* v_onFail_138_, lean_object* v_start_139_, lean_object* v_stop_140_, lean_object* v_cases_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(v_discr_137_, v_onFail_138_, v_start_139_, v_stop_140_, v_cases_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0(lean_object* v_discr_150_, lean_object* v_as_151_, size_t v_i_152_, size_t v_stop_153_, lean_object* v_b_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___redArg(v_discr_150_, v_as_151_, v_i_152_, v_stop_153_, v_b_154_, v___y_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0___boxed(lean_object* v_discr_163_, lean_object* v_as_164_, lean_object* v_i_165_, lean_object* v_stop_166_, lean_object* v_b_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
size_t v_i_boxed_175_; size_t v_stop_boxed_176_; lean_object* v_res_177_; 
v_i_boxed_175_ = lean_unbox_usize(v_i_165_);
lean_dec(v_i_165_);
v_stop_boxed_176_ = lean_unbox_usize(v_stop_166_);
lean_dec(v_stop_166_);
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build_spec__0(v_discr_163_, v_as_164_, v_i_boxed_175_, v_stop_boxed_176_, v_b_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec_ref(v_as_164_);
return v_res_177_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(lean_object* v_c_178_, lean_object* v_c_x27_179_){
_start:
{
lean_object* v_fst_180_; lean_object* v_fst_181_; uint8_t v___x_182_; 
v_fst_180_ = lean_ctor_get(v_c_178_, 0);
v_fst_181_ = lean_ctor_get(v_c_x27_179_, 0);
v___x_182_ = lean_string_dec_lt(v_fst_180_, v_fst_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0___boxed(lean_object* v_c_183_, lean_object* v_c_x27_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(v_c_183_, v_c_x27_184_);
lean_dec_ref(v_c_x27_184_);
lean_dec_ref(v_c_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(lean_object* v_hi_187_, lean_object* v_pivot_188_, lean_object* v_as_189_, lean_object* v_i_190_, lean_object* v_k_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_lt(v_k_191_, v_hi_187_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_k_191_);
v___x_193_ = lean_array_fswap(v_as_189_, v_i_190_, v_hi_187_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v_i_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v_fst_196_; lean_object* v_fst_197_; uint8_t v___x_198_; 
v___x_195_ = lean_array_fget_borrowed(v_as_189_, v_k_191_);
v_fst_196_ = lean_ctor_get(v___x_195_, 0);
v_fst_197_ = lean_ctor_get(v_pivot_188_, 0);
v___x_198_ = lean_string_dec_lt(v_fst_196_, v_fst_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_nat_add(v_k_191_, v___x_199_);
lean_dec(v_k_191_);
v_k_191_ = v___x_200_;
goto _start;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = lean_array_fswap(v_as_189_, v_i_190_, v_k_191_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_add(v_i_190_, v___x_203_);
lean_dec(v_i_190_);
v___x_205_ = lean_nat_add(v_k_191_, v___x_203_);
lean_dec(v_k_191_);
v_as_189_ = v___x_202_;
v_i_190_ = v___x_204_;
v_k_191_ = v___x_205_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_hi_207_, lean_object* v_pivot_208_, lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_k_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(v_hi_207_, v_pivot_208_, v_as_209_, v_i_210_, v_k_211_);
lean_dec_ref(v_pivot_208_);
lean_dec(v_hi_207_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(lean_object* v_n_213_, lean_object* v_as_214_, lean_object* v_lo_215_, lean_object* v_hi_216_){
_start:
{
lean_object* v___y_218_; uint8_t v___x_228_; 
v___x_228_ = lean_nat_dec_lt(v_lo_215_, v_hi_216_);
if (v___x_228_ == 0)
{
lean_dec(v_lo_215_);
return v_as_214_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_mid_231_; lean_object* v___y_233_; lean_object* v___y_239_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_229_ = lean_nat_add(v_lo_215_, v_hi_216_);
v___x_230_ = lean_unsigned_to_nat(1u);
v_mid_231_ = lean_nat_shiftr(v___x_229_, v___x_230_);
lean_dec(v___x_229_);
v___x_244_ = lean_array_fget_borrowed(v_as_214_, v_mid_231_);
v___x_245_ = lean_array_fget_borrowed(v_as_214_, v_lo_215_);
v___x_246_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
v___y_239_ = v_as_214_;
goto v___jp_238_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_array_fswap(v_as_214_, v_lo_215_, v_mid_231_);
v___y_239_ = v___x_247_;
goto v___jp_238_;
}
v___jp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_234_ = lean_array_fget_borrowed(v___y_233_, v_mid_231_);
v___x_235_ = lean_array_fget_borrowed(v___y_233_, v_hi_216_);
v___x_236_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v_mid_231_);
v___y_218_ = v___y_233_;
goto v___jp_217_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_array_fswap(v___y_233_, v_mid_231_, v_hi_216_);
lean_dec(v_mid_231_);
v___y_218_ = v___x_237_;
goto v___jp_217_;
}
}
v___jp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = lean_array_fget_borrowed(v___y_239_, v_hi_216_);
v___x_241_ = lean_array_fget_borrowed(v___y_239_, v_lo_215_);
v___x_242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___lam__0(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
v___y_233_ = v___y_239_;
goto v___jp_232_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = lean_array_fswap(v___y_239_, v_lo_215_, v_hi_216_);
v___y_233_ = v___x_243_;
goto v___jp_232_;
}
}
}
v___jp_217_:
{
lean_object* v_pivot_219_; lean_object* v___x_220_; lean_object* v_fst_221_; lean_object* v_snd_222_; uint8_t v___x_223_; 
v_pivot_219_ = lean_array_fget(v___y_218_, v_hi_216_);
lean_inc_n(v_lo_215_, 2);
v___x_220_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(v_hi_216_, v_pivot_219_, v___y_218_, v_lo_215_, v_lo_215_);
lean_dec(v_pivot_219_);
v_fst_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_fst_221_);
v_snd_222_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_snd_222_);
lean_dec_ref(v___x_220_);
v___x_223_ = lean_nat_dec_le(v_hi_216_, v_fst_221_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(v_n_213_, v_snd_222_, v_lo_215_, v_fst_221_);
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_fst_221_, v___x_225_);
lean_dec(v_fst_221_);
v_as_214_ = v___x_224_;
v_lo_215_ = v___x_226_;
goto _start;
}
else
{
lean_dec(v_fst_221_);
lean_dec(v_lo_215_);
return v_snd_222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg___boxed(lean_object* v_n_248_, lean_object* v_as_249_, lean_object* v_lo_250_, lean_object* v_hi_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(v_n_248_, v_as_249_, v_lo_250_, v_hi_251_);
lean_dec(v_hi_251_);
lean_dec(v_n_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_makeStringMatcher(lean_object* v_discr_253_, lean_object* v_cases_254_, lean_object* v_onFail_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___y_265_; lean_object* v___x_268_; lean_object* v___y_270_; lean_object* v___y_271_; uint8_t v___x_273_; 
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_array_get_size(v_cases_254_);
v___x_273_ = lean_nat_dec_eq(v___x_268_, v___x_263_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___y_277_; uint8_t v___x_279_; 
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_sub(v___x_268_, v___x_274_);
v___x_279_ = lean_nat_dec_le(v___x_263_, v___x_275_);
if (v___x_279_ == 0)
{
lean_inc(v___x_275_);
v___y_277_ = v___x_275_;
goto v___jp_276_;
}
else
{
v___y_277_ = v___x_263_;
goto v___jp_276_;
}
v___jp_276_:
{
uint8_t v___x_278_; 
v___x_278_ = lean_nat_dec_le(v___y_277_, v___x_275_);
if (v___x_278_ == 0)
{
lean_dec(v___x_275_);
lean_inc(v___y_277_);
v___y_270_ = v___y_277_;
v___y_271_ = v___y_277_;
goto v___jp_269_;
}
else
{
v___y_270_ = v___y_277_;
v___y_271_ = v___x_275_;
goto v___jp_269_;
}
}
}
else
{
v___y_265_ = v_cases_254_;
goto v___jp_264_;
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_array_get_size(v___y_265_);
v___x_267_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build(v_discr_253_, v_onFail_255_, v___x_263_, v___x_266_, v___y_265_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
return v___x_267_;
}
v___jp_269_:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(v___x_268_, v_cases_254_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
v___y_265_ = v___x_272_;
goto v___jp_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_makeStringMatcher___boxed(lean_object* v_discr_280_, lean_object* v_cases_281_, lean_object* v_onFail_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Elab_ConfigEval_makeStringMatcher(v_discr_280_, v_cases_281_, v_onFail_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0(lean_object* v_n_291_, lean_object* v_as_292_, lean_object* v_lo_293_, lean_object* v_hi_294_, lean_object* v_w_295_, lean_object* v_hlo_296_, lean_object* v_hhi_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___redArg(v_n_291_, v_as_292_, v_lo_293_, v_hi_294_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0___boxed(lean_object* v_n_299_, lean_object* v_as_300_, lean_object* v_lo_301_, lean_object* v_hi_302_, lean_object* v_w_303_, lean_object* v_hlo_304_, lean_object* v_hhi_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0(v_n_299_, v_as_300_, v_lo_301_, v_hi_302_, v_w_303_, v_hlo_304_, v_hhi_305_);
lean_dec(v_hi_302_);
lean_dec(v_n_299_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0(lean_object* v_n_307_, lean_object* v_lo_308_, lean_object* v_hi_309_, lean_object* v_hhi_310_, lean_object* v_pivot_311_, lean_object* v_as_312_, lean_object* v_i_313_, lean_object* v_k_314_, lean_object* v_ilo_315_, lean_object* v_ik_316_, lean_object* v_w_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___redArg(v_hi_309_, v_pivot_311_, v_as_312_, v_i_313_, v_k_314_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0___boxed(lean_object* v_n_319_, lean_object* v_lo_320_, lean_object* v_hi_321_, lean_object* v_hhi_322_, lean_object* v_pivot_323_, lean_object* v_as_324_, lean_object* v_i_325_, lean_object* v_k_326_, lean_object* v_ilo_327_, lean_object* v_ik_328_, lean_object* v_w_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_ConfigEval_makeStringMatcher_spec__0_spec__0(v_n_319_, v_lo_320_, v_hi_321_, v_hhi_322_, v_pivot_323_, v_as_324_, v_i_325_, v_k_326_, v_ilo_327_, v_ik_328_, v_w_329_);
lean_dec_ref(v_pivot_323_);
lean_dec(v_hi_321_);
lean_dec(v_lo_320_);
lean_dec(v_n_319_);
return v_res_330_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = l_Lean_maxRecDepthErrorMessage;
v___x_337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__3);
v___x_339_ = l_Lean_MessageData_ofFormat(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__4);
v___x_341_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__2));
v___x_342_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(lean_object* v_ref_343_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___closed__5);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v_ref_343_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg___boxed(lean_object* v_ref_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6(lean_object* v_00_u03b1_351_, lean_object* v_ref_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_352_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___boxed(lean_object* v_00_u03b1_361_, lean_object* v_ref_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6(v_00_u03b1_361_, v_ref_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(lean_object* v_cls_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_toCold_382_; lean_object* v_options_383_; uint8_t v_hasTrace_384_; 
v_toCold_382_ = lean_ctor_get(v___y_379_, 0);
v_options_383_ = lean_ctor_get(v_toCold_382_, 2);
v_hasTrace_384_ = lean_ctor_get_uint8(v_options_383_, sizeof(void*)*1);
if (v_hasTrace_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_cls_374_);
v___x_385_ = lean_box(v_hasTrace_384_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v_inheritedTraceOptions_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_inheritedTraceOptions_387_ = lean_ctor_get(v_toCold_382_, 11);
v___x_388_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1));
v___x_389_ = l_Lean_Name_append(v___x_388_, v_cls_374_);
v___x_390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_387_, v_options_383_, v___x_389_);
lean_dec(v___x_389_);
v___x_391_ = lean_box(v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___boxed(lean_object* v_cls_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(lean_object* v_as_405_, size_t v_sz_406_, size_t v_i_407_, lean_object* v_b_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = lean_usize_dec_lt(v_i_407_, v_sz_406_);
if (v___x_409_ == 0)
{
lean_inc_ref(v_b_408_);
return v_b_408_;
}
else
{
lean_object* v___x_410_; lean_object* v_a_411_; uint8_t v___x_412_; 
v___x_410_ = lean_box(0);
v_a_411_ = lean_array_uget_borrowed(v_as_405_, v_i_407_);
v___x_412_ = l_Lean_Expr_hasMVar(v_a_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; size_t v___x_414_; size_t v___x_415_; 
v___x_413_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_407_, v___x_414_);
v_i_407_ = v___x_415_;
v_b_408_ = v___x_413_;
goto _start;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_inc(v_a_411_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_a_411_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_410_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___boxed(lean_object* v_as_420_, lean_object* v_sz_421_, lean_object* v_i_422_, lean_object* v_b_423_){
_start:
{
size_t v_sz_boxed_424_; size_t v_i_boxed_425_; lean_object* v_res_426_; 
v_sz_boxed_424_ = lean_unbox_usize(v_sz_421_);
lean_dec(v_sz_421_);
v_i_boxed_425_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(v_as_420_, v_sz_boxed_424_, v_i_boxed_425_, v_b_423_);
lean_dec_ref(v_b_423_);
lean_dec_ref(v_as_420_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(lean_object* v_a_427_, lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
v___x_433_ = lean_expr_eqv(v_a_427_, v___x_432_);
if (v___x_433_ == 0)
{
size_t v___x_434_; size_t v___x_435_; 
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_429_, v___x_434_);
v_i_429_ = v___x_435_;
goto _start;
}
else
{
return v___x_433_;
}
}
else
{
uint8_t v___x_437_; 
v___x_437_ = 0;
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0___boxed(lean_object* v_a_438_, lean_object* v_as_439_, lean_object* v_i_440_, lean_object* v_stop_441_){
_start:
{
size_t v_i_boxed_442_; size_t v_stop_boxed_443_; uint8_t v_res_444_; lean_object* v_r_445_; 
v_i_boxed_442_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_stop_boxed_443_ = lean_unbox_usize(v_stop_441_);
lean_dec(v_stop_441_);
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(v_a_438_, v_as_439_, v_i_boxed_442_, v_stop_boxed_443_);
lean_dec_ref(v_as_439_);
lean_dec_ref(v_a_438_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(lean_object* v_as_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v_as_446_);
v___x_450_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
return v___x_450_;
}
else
{
if (v___x_450_ == 0)
{
return v___x_450_;
}
else
{
size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v___x_451_ = ((size_t)0ULL);
v___x_452_ = lean_usize_of_nat(v___x_449_);
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(v_a_447_, v_as_446_, v___x_451_, v___x_452_);
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0___boxed(lean_object* v_as_454_, lean_object* v_a_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_as_454_, v_a_455_);
lean_dec_ref(v_a_455_);
lean_dec_ref(v_as_454_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(lean_object* v_plan_458_, lean_object* v_as_459_, size_t v_i_460_, size_t v_stop_461_, lean_object* v_b_462_){
_start:
{
lean_object* v___y_464_; uint8_t v___x_468_; 
v___x_468_ = lean_usize_dec_eq(v_i_460_, v_stop_461_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_array_uget_borrowed(v_as_459_, v_i_460_);
v___x_470_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_plan_458_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_inc(v___x_469_);
v___x_471_ = lean_array_push(v_b_462_, v___x_469_);
v___y_464_ = v___x_471_;
goto v___jp_463_;
}
else
{
v___y_464_ = v_b_462_;
goto v___jp_463_;
}
}
else
{
return v_b_462_;
}
v___jp_463_:
{
size_t v___x_465_; size_t v___x_466_; 
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_add(v_i_460_, v___x_465_);
v_i_460_ = v___x_466_;
v_b_462_ = v___y_464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15___boxed(lean_object* v_plan_472_, lean_object* v_as_473_, lean_object* v_i_474_, lean_object* v_stop_475_, lean_object* v_b_476_){
_start:
{
size_t v_i_boxed_477_; size_t v_stop_boxed_478_; lean_object* v_res_479_; 
v_i_boxed_477_ = lean_unbox_usize(v_i_474_);
lean_dec(v_i_474_);
v_stop_boxed_478_ = lean_unbox_usize(v_stop_475_);
lean_dec(v_stop_475_);
v_res_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_472_, v_as_473_, v_i_boxed_477_, v_stop_boxed_478_, v_b_476_);
lean_dec_ref(v_as_473_);
lean_dec_ref(v_plan_472_);
return v_res_479_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(lean_object* v_a_480_, lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
else
{
lean_object* v_key_483_; lean_object* v_tail_484_; uint8_t v___x_485_; 
v_key_483_ = lean_ctor_get(v_x_481_, 0);
v_tail_484_ = lean_ctor_get(v_x_481_, 2);
v___x_485_ = lean_expr_eqv(v_key_483_, v_a_480_);
if (v___x_485_ == 0)
{
v_x_481_ = v_tail_484_;
goto _start;
}
else
{
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg___boxed(lean_object* v_a_487_, lean_object* v_x_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_487_, v_x_488_);
lean_dec(v_x_488_);
lean_dec_ref(v_a_487_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(lean_object* v_m_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_buckets_493_; lean_object* v___x_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v_fold_498_; uint64_t v___x_499_; uint64_t v___x_500_; uint64_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_buckets_493_ = lean_ctor_get(v_m_491_, 1);
v___x_494_ = lean_array_get_size(v_buckets_493_);
v___x_495_ = l_Lean_Expr_hash(v_a_492_);
v___x_496_ = 32ULL;
v___x_497_ = lean_uint64_shift_right(v___x_495_, v___x_496_);
v_fold_498_ = lean_uint64_xor(v___x_495_, v___x_497_);
v___x_499_ = 16ULL;
v___x_500_ = lean_uint64_shift_right(v_fold_498_, v___x_499_);
v___x_501_ = lean_uint64_xor(v_fold_498_, v___x_500_);
v___x_502_ = lean_uint64_to_usize(v___x_501_);
v___x_503_ = lean_usize_of_nat(v___x_494_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_sub(v___x_503_, v___x_504_);
v___x_506_ = lean_usize_land(v___x_502_, v___x_505_);
v___x_507_ = lean_array_uget_borrowed(v_buckets_493_, v___x_506_);
v___x_508_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_492_, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg___boxed(lean_object* v_m_509_, lean_object* v_a_510_){
_start:
{
uint8_t v_res_511_; lean_object* v_r_512_; 
v_res_511_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(v_m_509_, v_a_510_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_m_509_);
v_r_512_ = lean_box(v_res_511_);
return v_r_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(lean_object* v_processing_513_, lean_object* v_as_514_, size_t v_sz_515_, size_t v_i_516_, lean_object* v_b_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = lean_usize_dec_lt(v_i_516_, v_sz_515_);
if (v___x_518_ == 0)
{
lean_inc_ref(v_b_517_);
return v_b_517_;
}
else
{
lean_object* v___x_519_; lean_object* v_a_520_; uint8_t v___x_521_; 
v___x_519_ = lean_box(0);
v_a_520_ = lean_array_uget_borrowed(v_as_514_, v_i_516_);
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(v_processing_513_, v_a_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; size_t v___x_523_; size_t v___x_524_; 
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v___x_523_ = ((size_t)1ULL);
v___x_524_ = lean_usize_add(v_i_516_, v___x_523_);
v_i_516_ = v___x_524_;
v_b_517_ = v___x_522_;
goto _start;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_inc(v_a_520_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_a_520_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_519_);
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13___boxed(lean_object* v_processing_529_, lean_object* v_as_530_, lean_object* v_sz_531_, lean_object* v_i_532_, lean_object* v_b_533_){
_start:
{
size_t v_sz_boxed_534_; size_t v_i_boxed_535_; lean_object* v_res_536_; 
v_sz_boxed_534_ = lean_unbox_usize(v_sz_531_);
lean_dec(v_sz_531_);
v_i_boxed_535_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(v_processing_529_, v_as_530_, v_sz_boxed_534_, v_i_boxed_535_, v_b_533_);
lean_dec_ref(v_b_533_);
lean_dec_ref(v_as_530_);
lean_dec_ref(v_processing_529_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
return v_x_537_;
}
else
{
lean_object* v_key_539_; lean_object* v_value_540_; lean_object* v_tail_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_564_; 
v_key_539_ = lean_ctor_get(v_x_538_, 0);
v_value_540_ = lean_ctor_get(v_x_538_, 1);
v_tail_541_ = lean_ctor_get(v_x_538_, 2);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_564_ == 0)
{
v___x_543_ = v_x_538_;
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_tail_541_);
lean_inc(v_value_540_);
lean_inc(v_key_539_);
lean_dec(v_x_538_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; uint64_t v_fold_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_545_ = lean_array_get_size(v_x_537_);
v___x_546_ = l_Lean_Expr_hash(v_key_539_);
v___x_547_ = 32ULL;
v___x_548_ = lean_uint64_shift_right(v___x_546_, v___x_547_);
v_fold_549_ = lean_uint64_xor(v___x_546_, v___x_548_);
v___x_550_ = 16ULL;
v___x_551_ = lean_uint64_shift_right(v_fold_549_, v___x_550_);
v___x_552_ = lean_uint64_xor(v_fold_549_, v___x_551_);
v___x_553_ = lean_uint64_to_usize(v___x_552_);
v___x_554_ = lean_usize_of_nat(v___x_545_);
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_sub(v___x_554_, v___x_555_);
v___x_557_ = lean_usize_land(v___x_553_, v___x_556_);
v___x_558_ = lean_array_uget_borrowed(v_x_537_, v___x_557_);
lean_inc(v___x_558_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 2, v___x_558_);
v___x_560_ = v___x_543_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_key_539_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_value_540_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v___x_558_);
v___x_560_ = v_reuseFailAlloc_563_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_array_uset(v_x_537_, v___x_557_, v___x_560_);
v_x_537_ = v___x_561_;
v_x_538_ = v_tail_541_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(lean_object* v_i_565_, lean_object* v_source_566_, lean_object* v_target_567_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v_source_566_);
v___x_569_ = lean_nat_dec_lt(v_i_565_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec_ref(v_source_566_);
lean_dec(v_i_565_);
return v_target_567_;
}
else
{
lean_object* v_es_570_; lean_object* v___x_571_; lean_object* v_source_572_; lean_object* v_target_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_es_570_ = lean_array_fget(v_source_566_, v_i_565_);
v___x_571_ = lean_box(0);
v_source_572_ = lean_array_fset(v_source_566_, v_i_565_, v___x_571_);
v_target_573_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(v_target_567_, v_es_570_);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_i_565_, v___x_574_);
lean_dec(v_i_565_);
v_i_565_ = v___x_575_;
v_source_566_ = v_source_572_;
v_target_567_ = v_target_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(lean_object* v_data_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_nbuckets_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_578_ = lean_array_get_size(v_data_577_);
v___x_579_ = lean_unsigned_to_nat(2u);
v_nbuckets_580_ = lean_nat_mul(v___x_578_, v___x_579_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_box(0);
v___x_583_ = lean_mk_array(v_nbuckets_580_, v___x_582_);
v___x_584_ = lean_array_propagate_mark(v_data_577_, v___x_583_);
v___x_585_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(v___x_581_, v_data_577_, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(lean_object* v_m_586_, lean_object* v_a_587_, lean_object* v_b_588_){
_start:
{
lean_object* v_size_589_; lean_object* v_buckets_590_; lean_object* v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v_fold_595_; uint64_t v___x_596_; uint64_t v___x_597_; uint64_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v_bkt_604_; uint8_t v___x_605_; 
v_size_589_ = lean_ctor_get(v_m_586_, 0);
v_buckets_590_ = lean_ctor_get(v_m_586_, 1);
v___x_591_ = lean_array_get_size(v_buckets_590_);
v___x_592_ = l_Lean_Expr_hash(v_a_587_);
v___x_593_ = 32ULL;
v___x_594_ = lean_uint64_shift_right(v___x_592_, v___x_593_);
v_fold_595_ = lean_uint64_xor(v___x_592_, v___x_594_);
v___x_596_ = 16ULL;
v___x_597_ = lean_uint64_shift_right(v_fold_595_, v___x_596_);
v___x_598_ = lean_uint64_xor(v_fold_595_, v___x_597_);
v___x_599_ = lean_uint64_to_usize(v___x_598_);
v___x_600_ = lean_usize_of_nat(v___x_591_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_sub(v___x_600_, v___x_601_);
v___x_603_ = lean_usize_land(v___x_599_, v___x_602_);
v_bkt_604_ = lean_array_uget_borrowed(v_buckets_590_, v___x_603_);
v___x_605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_587_, v_bkt_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_626_; 
lean_inc_ref(v_buckets_590_);
lean_inc(v_size_589_);
v_isSharedCheck_626_ = !lean_is_exclusive(v_m_586_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; lean_object* v_unused_628_; 
v_unused_627_ = lean_ctor_get(v_m_586_, 1);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_m_586_, 0);
lean_dec(v_unused_628_);
v___x_607_ = v_m_586_;
v_isShared_608_ = v_isSharedCheck_626_;
goto v_resetjp_606_;
}
else
{
lean_dec(v_m_586_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_626_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v_size_x27_610_; lean_object* v___x_611_; lean_object* v_buckets_x27_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v_size_x27_610_ = lean_nat_add(v_size_589_, v___x_609_);
lean_dec(v_size_589_);
lean_inc(v_bkt_604_);
v___x_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_611_, 0, v_a_587_);
lean_ctor_set(v___x_611_, 1, v_b_588_);
lean_ctor_set(v___x_611_, 2, v_bkt_604_);
v_buckets_x27_612_ = lean_array_uset(v_buckets_590_, v___x_603_, v___x_611_);
v___x_613_ = lean_unsigned_to_nat(4u);
v___x_614_ = lean_nat_mul(v_size_x27_610_, v___x_613_);
v___x_615_ = lean_unsigned_to_nat(3u);
v___x_616_ = lean_nat_div(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_array_get_size(v_buckets_x27_612_);
v___x_618_ = lean_nat_dec_le(v___x_616_, v___x_617_);
lean_dec(v___x_616_);
if (v___x_618_ == 0)
{
lean_object* v_val_619_; lean_object* v___x_621_; 
v_val_619_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(v_buckets_x27_612_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_val_619_);
lean_ctor_set(v___x_607_, 0, v_size_x27_610_);
v___x_621_ = v___x_607_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_size_x27_610_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_val_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_624_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v_buckets_x27_612_);
lean_ctor_set(v___x_607_, 0, v_size_x27_610_);
v___x_624_ = v___x_607_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_size_x27_610_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_buckets_x27_612_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_dec(v_b_588_);
lean_dec_ref(v_a_587_);
return v_m_586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(lean_object* v_e_629_, lean_object* v___y_630_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Lean_Expr_hasMVar(v_e_629_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_e_629_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v_mctx_635_; lean_object* v___x_636_; lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_639_; lean_object* v_cache_640_; lean_object* v_zetaDeltaFVarIds_641_; lean_object* v_postponed_642_; lean_object* v_diag_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_652_; 
v___x_634_ = lean_st_ref_get(v___y_630_);
v_mctx_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_mctx_635_);
lean_dec(v___x_634_);
v___x_636_ = l_Lean_instantiateMVarsCore(v_mctx_635_, v_e_629_);
v_fst_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_fst_637_);
v_snd_638_ = lean_ctor_get(v___x_636_, 1);
lean_inc(v_snd_638_);
lean_dec_ref(v___x_636_);
v___x_639_ = lean_st_ref_take(v___y_630_);
v_cache_640_ = lean_ctor_get(v___x_639_, 1);
v_zetaDeltaFVarIds_641_ = lean_ctor_get(v___x_639_, 2);
v_postponed_642_ = lean_ctor_get(v___x_639_, 3);
v_diag_643_ = lean_ctor_get(v___x_639_, 4);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v___x_639_, 0);
lean_dec(v_unused_653_);
v___x_645_ = v___x_639_;
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_diag_643_);
lean_inc(v_postponed_642_);
lean_inc(v_zetaDeltaFVarIds_641_);
lean_inc(v_cache_640_);
lean_dec(v___x_639_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_snd_638_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_snd_638_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_cache_640_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_zetaDeltaFVarIds_641_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_postponed_642_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v_diag_643_);
v___x_648_ = v_reuseFailAlloc_651_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_st_ref_put(v___y_630_, v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v_fst_637_);
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg___boxed(lean_object* v_e_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_e_654_, v___y_655_);
lean_dec(v___y_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(size_t v_sz_658_, size_t v_i_659_, lean_object* v_bs_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_668_; 
v___x_668_ = lean_usize_dec_lt(v_i_659_, v_sz_658_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v_bs_660_);
return v___x_669_;
}
else
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v_bs_x27_672_; lean_object* v___x_673_; 
v_v_670_ = lean_array_uget(v_bs_660_, v_i_659_);
v___x_671_ = lean_unsigned_to_nat(0u);
v_bs_x27_672_ = lean_array_uset(v_bs_660_, v_i_659_, v___x_671_);
v___x_673_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_v_670_, v___y_664_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_add(v_i_659_, v___x_675_);
v___x_677_ = lean_array_uset(v_bs_x27_672_, v_i_659_, v_a_674_);
v_i_659_ = v___x_676_;
v_bs_660_ = v___x_677_;
goto _start;
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_bs_x27_672_);
v_a_679_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_673_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_673_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10___boxed(lean_object* v_sz_687_, lean_object* v_i_688_, lean_object* v_bs_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
size_t v_sz_boxed_697_; size_t v_i_boxed_698_; lean_object* v_res_699_; 
v_sz_boxed_697_ = lean_unbox_usize(v_sz_687_);
lean_dec(v_sz_687_);
v_i_boxed_698_ = lean_unbox_usize(v_i_688_);
lean_dec(v_i_688_);
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(v_sz_boxed_697_, v_i_boxed_698_, v_bs_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_699_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(lean_object* v_opts_700_, lean_object* v_opt_701_){
_start:
{
lean_object* v_name_702_; lean_object* v_defValue_703_; lean_object* v_map_704_; lean_object* v___x_705_; 
v_name_702_ = lean_ctor_get(v_opt_701_, 0);
v_defValue_703_ = lean_ctor_get(v_opt_701_, 1);
v_map_704_ = lean_ctor_get(v_opts_700_, 0);
v___x_705_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_704_, v_name_702_);
if (lean_obj_tag(v___x_705_) == 0)
{
uint8_t v___x_706_; 
v___x_706_ = lean_unbox(v_defValue_703_);
return v___x_706_;
}
else
{
lean_object* v_val_707_; 
v_val_707_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v___x_705_, 1);
if (lean_obj_tag(v_val_707_) == 1)
{
uint8_t v_v_708_; 
v_v_708_ = lean_ctor_get_uint8(v_val_707_, 0);
lean_dec_ref_known(v_val_707_, 0);
return v_v_708_;
}
else
{
uint8_t v___x_709_; 
lean_dec(v_val_707_);
v___x_709_ = lean_unbox(v_defValue_703_);
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21___boxed(lean_object* v_opts_710_, lean_object* v_opt_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_710_, v_opt_711_);
lean_dec_ref(v_opt_711_);
lean_dec_ref(v_opts_710_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_box(1);
v___x_715_ = l_Lean_MessageData_ofFormat(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2));
v___x_720_ = l_Lean_MessageData_ofFormat(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22(lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
if (lean_obj_tag(v_x_722_) == 0)
{
return v_x_721_;
}
else
{
lean_object* v_head_723_; lean_object* v_tail_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_746_; 
v_head_723_ = lean_ctor_get(v_x_722_, 0);
v_tail_724_ = lean_ctor_get(v_x_722_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_722_);
if (v_isSharedCheck_746_ == 0)
{
v___x_726_ = v_x_722_;
v_isShared_727_ = v_isSharedCheck_746_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_tail_724_);
lean_inc(v_head_723_);
lean_dec(v_x_722_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_746_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_before_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_744_; 
v_before_728_ = lean_ctor_get(v_head_723_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_head_723_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_head_723_, 1);
lean_dec(v_unused_745_);
v___x_730_ = v_head_723_;
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_before_728_);
lean_dec(v_head_723_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 7);
lean_ctor_set(v___x_730_, 1, v___x_732_);
lean_ctor_set(v___x_730_, 0, v_x_721_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_x_721_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_743_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 7);
lean_ctor_set(v___x_726_, 1, v___x_735_);
lean_ctor_set(v___x_726_, 0, v___x_734_);
v___x_737_ = v___x_726_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_742_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = l_Lean_MessageData_ofSyntax(v_before_728_);
v___x_739_ = l_Lean_indentD(v___x_738_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_737_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v_x_721_ = v___x_740_;
v_x_722_ = v_tail_724_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1));
v___x_751_ = l_Lean_MessageData_ofFormat(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(lean_object* v_msgData_752_, lean_object* v_macroStack_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_754_);
v___x_757_ = l_Lean_Elab_pp_macroStack;
v___x_758_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v___x_756_, v___x_757_);
lean_dec_ref(v___x_756_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec(v_macroStack_753_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v_msgData_752_);
return v___x_759_;
}
else
{
if (lean_obj_tag(v_macroStack_753_) == 0)
{
lean_object* v___x_760_; 
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v_msgData_752_);
return v___x_760_;
}
else
{
lean_object* v_head_761_; lean_object* v_after_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_777_; 
v_head_761_ = lean_ctor_get(v_macroStack_753_, 0);
lean_inc(v_head_761_);
v_after_762_ = lean_ctor_get(v_head_761_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_head_761_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v_head_761_, 0);
lean_dec(v_unused_778_);
v___x_764_ = v_head_761_;
v_isShared_765_ = v_isSharedCheck_777_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_after_762_);
lean_dec(v_head_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_777_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 7);
lean_ctor_set(v___x_764_, 1, v___x_766_);
lean_ctor_set(v___x_764_, 0, v_msgData_752_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_msgData_752_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_776_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_msgData_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_769_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = l_Lean_MessageData_ofSyntax(v_after_762_);
v___x_772_ = l_Lean_indentD(v___x_771_);
v_msgData_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_773_, 0, v___x_770_);
lean_ctor_set(v_msgData_773_, 1, v___x_772_);
v___x_774_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22(v_msgData_773_, v_macroStack_753_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___boxed(lean_object* v_msgData_779_, lean_object* v_macroStack_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_msgData_779_, v_macroStack_780_, v___y_781_);
lean_dec_ref(v___y_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(lean_object* v_msgData_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_env_791_; uint8_t v___x_792_; lean_object* v_env_793_; lean_object* v___x_794_; lean_object* v_toCold_795_; lean_object* v_mctx_796_; lean_object* v_lctx_797_; lean_object* v_options_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_790_ = lean_st_ref_get(v___y_788_);
v_env_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc_ref(v_env_791_);
lean_dec(v___x_790_);
v___x_792_ = 0;
v_env_793_ = l_Lean_Environment_setRecordingDeps(v_env_791_, v___x_792_);
v___x_794_ = lean_st_ref_get(v___y_786_);
v_toCold_795_ = lean_ctor_get(v___y_787_, 0);
v_mctx_796_ = lean_ctor_get(v___x_794_, 0);
lean_inc_ref(v_mctx_796_);
lean_dec(v___x_794_);
v_lctx_797_ = lean_ctor_get(v___y_785_, 2);
v_options_798_ = lean_ctor_get(v_toCold_795_, 2);
lean_inc_ref(v_options_798_);
lean_inc_ref(v_lctx_797_);
v___x_799_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_799_, 0, v_env_793_);
lean_ctor_set(v___x_799_, 1, v_mctx_796_);
lean_ctor_set(v___x_799_, 2, v_lctx_797_);
lean_ctor_set(v___x_799_, 3, v_options_798_);
v___x_800_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v_msgData_784_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4___boxed(lean_object* v_msgData_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msgData_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(lean_object* v_msg_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_ref_817_; lean_object* v_macroStack_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
v_ref_817_ = lean_ctor_get(v___y_814_, 2);
v_macroStack_818_ = lean_ctor_get(v___y_810_, 1);
v___x_819_ = l_Lean_Elab_getBetterRef(v_ref_817_, v_macroStack_818_);
v___x_820_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_809_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_820_);
lean_inc(v_macroStack_818_);
v___x_822_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_a_821_, v_macroStack_818_, v___y_814_);
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_831_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_819_);
lean_ctor_set(v___x_827_, 1, v_a_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 1);
lean_ctor_set(v___x_825_, 0, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg___boxed(lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v_msg_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_inc(v_x_841_);
return v_x_841_;
}
else
{
lean_object* v_key_843_; lean_object* v_tail_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_key_843_ = lean_ctor_get(v_x_842_, 0);
v_tail_844_ = lean_ctor_get(v_x_842_, 2);
v___x_845_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_x_841_, v_tail_844_);
lean_inc(v_key_843_);
v___x_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_846_, 0, v_key_843_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4___boxed(lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_x_847_, v_x_848_);
lean_dec(v_x_848_);
lean_dec(v_x_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(lean_object* v_as_850_, size_t v_i_851_, size_t v_stop_852_, lean_object* v_b_853_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_eq(v_i_851_, v_stop_852_);
if (v___x_854_ == 0)
{
size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = ((size_t)1ULL);
v___x_856_ = lean_usize_sub(v_i_851_, v___x_855_);
v___x_857_ = lean_array_uget_borrowed(v_as_850_, v___x_856_);
v___x_858_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_b_853_, v___x_857_);
lean_dec(v_b_853_);
v_i_851_ = v___x_856_;
v_b_853_ = v___x_858_;
goto _start;
}
else
{
return v_b_853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5___boxed(lean_object* v_as_860_, lean_object* v_i_861_, lean_object* v_stop_862_, lean_object* v_b_863_){
_start:
{
size_t v_i_boxed_864_; size_t v_stop_boxed_865_; lean_object* v_res_866_; 
v_i_boxed_864_ = lean_unbox_usize(v_i_861_);
lean_dec(v_i_861_);
v_stop_boxed_865_ = lean_unbox_usize(v_stop_862_);
lean_dec(v_stop_862_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_as_860_, v_i_boxed_864_, v_stop_boxed_865_, v_b_863_);
lean_dec_ref(v_as_860_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
if (lean_obj_tag(v_a_867_) == 0)
{
lean_object* v___x_869_; 
v___x_869_ = l_List_reverse___redArg(v_a_868_);
return v___x_869_;
}
else
{
lean_object* v_head_870_; lean_object* v_tail_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_880_; 
v_head_870_ = lean_ctor_get(v_a_867_, 0);
v_tail_871_ = lean_ctor_get(v_a_867_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_867_);
if (v_isSharedCheck_880_ == 0)
{
v___x_873_ = v_a_867_;
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_tail_871_);
lean_inc(v_head_870_);
lean_dec(v_a_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = l_Lean_MessageData_ofExpr(v_head_870_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 1, v_a_868_);
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_a_868_);
v___x_877_ = v_reuseFailAlloc_879_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
v_a_867_ = v_tail_871_;
v_a_868_ = v___x_877_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_881_; double v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_float_of_nat(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(lean_object* v_cls_885_, lean_object* v_msg_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_ref_892_; lean_object* v___x_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_939_; 
v_ref_892_ = lean_ctor_get(v___y_889_, 2);
v___x_893_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_939_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_939_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_939_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v_traceState_899_; lean_object* v_env_900_; lean_object* v_nextMacroScope_901_; lean_object* v_ngen_902_; lean_object* v_auxDeclNGen_903_; lean_object* v_cache_904_; lean_object* v_recordedDeps_905_; lean_object* v_messages_906_; lean_object* v_infoState_907_; lean_object* v_snapshotTasks_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_938_; 
v___x_898_ = lean_st_ref_take(v___y_890_);
v_traceState_899_ = lean_ctor_get(v___x_898_, 4);
v_env_900_ = lean_ctor_get(v___x_898_, 0);
v_nextMacroScope_901_ = lean_ctor_get(v___x_898_, 1);
v_ngen_902_ = lean_ctor_get(v___x_898_, 2);
v_auxDeclNGen_903_ = lean_ctor_get(v___x_898_, 3);
v_cache_904_ = lean_ctor_get(v___x_898_, 5);
v_recordedDeps_905_ = lean_ctor_get(v___x_898_, 6);
v_messages_906_ = lean_ctor_get(v___x_898_, 7);
v_infoState_907_ = lean_ctor_get(v___x_898_, 8);
v_snapshotTasks_908_ = lean_ctor_get(v___x_898_, 9);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_938_ == 0)
{
v___x_910_ = v___x_898_;
v_isShared_911_ = v_isSharedCheck_938_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_snapshotTasks_908_);
lean_inc(v_infoState_907_);
lean_inc(v_messages_906_);
lean_inc(v_recordedDeps_905_);
lean_inc(v_cache_904_);
lean_inc(v_traceState_899_);
lean_inc(v_auxDeclNGen_903_);
lean_inc(v_ngen_902_);
lean_inc(v_nextMacroScope_901_);
lean_inc(v_env_900_);
lean_dec(v___x_898_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_938_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
uint64_t v_tid_912_; lean_object* v_traces_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_937_; 
v_tid_912_ = lean_ctor_get_uint64(v_traceState_899_, sizeof(void*)*1);
v_traces_913_ = lean_ctor_get(v_traceState_899_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_traceState_899_);
if (v_isSharedCheck_937_ == 0)
{
v___x_915_ = v_traceState_899_;
v_isShared_916_ = v_isSharedCheck_937_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_traces_913_);
lean_dec(v_traceState_899_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_937_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; double v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_917_ = lean_box(0);
v___x_918_ = lean_box(0);
v___x_919_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
v___x_920_ = 0;
v___x_921_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_922_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_922_, 0, v_cls_885_);
lean_ctor_set(v___x_922_, 1, v___x_918_);
lean_ctor_set(v___x_922_, 2, v___x_921_);
lean_ctor_set_float(v___x_922_, sizeof(void*)*3, v___x_919_);
lean_ctor_set_float(v___x_922_, sizeof(void*)*3 + 8, v___x_919_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*3 + 16, v___x_920_);
v___x_923_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1));
v___x_924_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v_a_894_);
lean_ctor_set(v___x_924_, 2, v___x_923_);
lean_inc(v_ref_892_);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_ref_892_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l_Lean_PersistentArray_push___redArg(v_traces_913_, v___x_925_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_926_);
v___x_928_ = v___x_915_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_926_);
lean_ctor_set_uint64(v_reuseFailAlloc_936_, sizeof(void*)*1, v_tid_912_);
v___x_928_ = v_reuseFailAlloc_936_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 4, v___x_928_);
v___x_930_ = v___x_910_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_env_900_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_nextMacroScope_901_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_ngen_902_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_auxDeclNGen_903_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_935_, 5, v_cache_904_);
lean_ctor_set(v_reuseFailAlloc_935_, 6, v_recordedDeps_905_);
lean_ctor_set(v_reuseFailAlloc_935_, 7, v_messages_906_);
lean_ctor_set(v_reuseFailAlloc_935_, 8, v_infoState_907_);
lean_ctor_set(v_reuseFailAlloc_935_, 9, v_snapshotTasks_908_);
v___x_930_ = v_reuseFailAlloc_935_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_st_ref_put(v___y_890_, v___x_930_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_917_);
v___x_933_ = v___x_896_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_917_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___boxed(lean_object* v_cls_940_, lean_object* v_msg_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_940_, v_msg_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(lean_object* v_msg_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_ref_954_; lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_964_; 
v_ref_954_ = lean_ctor_get(v___y_951_, 2);
v___x_955_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_964_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_inc(v_ref_954_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_ref_954_);
lean_ctor_set(v___x_960_, 1, v_a_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 1);
lean_ctor_set(v___x_958_, 0, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg___boxed(lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v_msg_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_971_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(lean_object* v_a_972_, lean_object* v_as_973_, size_t v_i_974_, size_t v_stop_975_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = lean_usize_dec_eq(v_i_974_, v_stop_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = lean_array_uget_borrowed(v_as_973_, v_i_974_);
v___x_978_ = lean_nat_dec_eq(v_a_972_, v___x_977_);
if (v___x_978_ == 0)
{
size_t v___x_979_; size_t v___x_980_; 
v___x_979_ = ((size_t)1ULL);
v___x_980_ = lean_usize_add(v_i_974_, v___x_979_);
v_i_974_ = v___x_980_;
goto _start;
}
else
{
return v___x_978_;
}
}
else
{
uint8_t v___x_982_; 
v___x_982_ = 0;
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25___boxed(lean_object* v_a_983_, lean_object* v_as_984_, lean_object* v_i_985_, lean_object* v_stop_986_){
_start:
{
size_t v_i_boxed_987_; size_t v_stop_boxed_988_; uint8_t v_res_989_; lean_object* v_r_990_; 
v_i_boxed_987_ = lean_unbox_usize(v_i_985_);
lean_dec(v_i_985_);
v_stop_boxed_988_ = lean_unbox_usize(v_stop_986_);
lean_dec(v_stop_986_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(v_a_983_, v_as_984_, v_i_boxed_987_, v_stop_boxed_988_);
lean_dec_ref(v_as_984_);
lean_dec(v_a_983_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(lean_object* v_as_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v_as_991_);
v___x_995_ = lean_nat_dec_lt(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
return v___x_995_;
}
else
{
if (v___x_995_ == 0)
{
return v___x_995_;
}
else
{
size_t v___x_996_; size_t v___x_997_; uint8_t v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_994_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(v_a_992_, v_as_991_, v___x_996_, v___x_997_);
return v___x_998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20___boxed(lean_object* v_as_999_, lean_object* v_a_1000_){
_start:
{
uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_res_1001_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(v_as_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_as_999_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(lean_object* v___x_1006_, lean_object* v_fst_1007_, lean_object* v_range_1008_, lean_object* v_b_1009_, lean_object* v_i_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_stop_1018_; lean_object* v_step_1019_; uint8_t v___x_1020_; 
v_stop_1018_ = lean_ctor_get(v_range_1008_, 1);
v_step_1019_ = lean_ctor_get(v_range_1008_, 2);
v___x_1020_ = lean_nat_dec_lt(v_i_1010_, v_stop_1018_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec(v_i_1010_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_b_1009_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; uint8_t v___x_1026_; 
v___x_1022_ = lean_box(0);
v___x_1026_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(v___x_1006_, v_i_1010_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_a_1029_; uint8_t v___x_1030_; 
v___x_1027_ = lean_array_fget_borrowed(v_fst_1007_, v_i_1010_);
lean_inc(v___x_1027_);
v___x_1028_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v___x_1027_, v___y_1014_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = l_Lean_Expr_hasMVar(v_a_1029_);
lean_dec(v_a_1029_);
if (v___x_1030_ == 0)
{
goto v___jp_1023_;
}
else
{
if (v___x_1026_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec(v_i_1010_);
v___x_1031_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1032_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1031_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
return v___x_1032_;
}
else
{
goto v___jp_1023_;
}
}
}
else
{
goto v___jp_1023_;
}
v___jp_1023_:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_nat_add(v_i_1010_, v_step_1019_);
lean_dec(v_i_1010_);
v_b_1009_ = v___x_1022_;
v_i_1010_ = v___x_1024_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___boxed(lean_object* v___x_1033_, lean_object* v_fst_1034_, lean_object* v_range_1035_, lean_object* v_b_1036_, lean_object* v_i_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_1033_, v_fst_1034_, v_range_1035_, v_b_1036_, v_i_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec_ref(v_range_1035_);
lean_dec_ref(v_fst_1034_);
lean_dec_ref(v___x_1033_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(lean_object* v_fst_1046_, lean_object* v_className_1047_, lean_object* v_as_1048_, size_t v_sz_1049_, size_t v_i_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_a_1060_; uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_lt(v_i_1050_, v_sz_1049_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_b_1051_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1066_ = l_Lean_instInhabitedExpr;
v___x_1067_ = lean_box(0);
v_a_1068_ = lean_array_uget_borrowed(v_as_1048_, v_i_1050_);
v___x_1069_ = lean_array_get_borrowed(v___x_1066_, v_fst_1046_, v_a_1068_);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___x_1069_);
v___x_1070_ = lean_infer_type(v___x_1069_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
lean_inc(v___y_1057_);
lean_inc_ref(v___y_1056_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
v___x_1072_ = lean_whnf(v_a_1071_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_a_1073_, v___y_1055_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = l_Lean_Expr_isAppOfArity(v_a_1075_, v_className_1047_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec(v_a_1075_);
v___x_1078_ = l_Lean_Expr_mvarId_x21(v___x_1069_);
v___x_1079_ = l_Lean_Elab_Term_synthesizeInstMVarCore(v___x_1078_, v___x_1067_, v___x_1067_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; uint8_t v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_unbox(v_a_1080_);
lean_dec(v_a_1080_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1083_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1082_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_dec_ref_known(v___x_1083_, 1);
v_a_1060_ = v_b_1051_;
goto v___jp_1059_;
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v_b_1051_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
v_a_1060_ = v_b_1051_;
goto v___jp_1059_;
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v_b_1051_);
v_a_1092_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1079_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1079_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = l_Lean_Expr_appArg_x21(v_a_1075_);
lean_dec(v_a_1075_);
v___x_1101_ = lean_array_push(v_b_1051_, v___x_1100_);
v_a_1060_ = v___x_1101_;
goto v___jp_1059_;
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v_b_1051_);
v_a_1102_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1074_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1074_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_b_1051_);
v_a_1110_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1072_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1072_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v_b_1051_);
v_a_1118_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1070_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1070_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
v___jp_1059_:
{
size_t v___x_1061_; size_t v___x_1062_; 
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_add(v_i_1050_, v___x_1061_);
v_i_1050_ = v___x_1062_;
v_b_1051_ = v_a_1060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19___boxed(lean_object* v_fst_1126_, lean_object* v_className_1127_, lean_object* v_as_1128_, lean_object* v_sz_1129_, lean_object* v_i_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
size_t v_sz_boxed_1139_; size_t v_i_boxed_1140_; lean_object* v_res_1141_; 
v_sz_boxed_1139_ = lean_unbox_usize(v_sz_1129_);
lean_dec(v_sz_1129_);
v_i_boxed_1140_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v_fst_1126_, v_className_1127_, v_as_1128_, v_sz_boxed_1139_, v_i_boxed_1140_, v_b_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_as_1128_);
lean_dec(v_className_1127_);
lean_dec_ref(v_fst_1126_);
return v_res_1141_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(lean_object* v_className_1150_, lean_object* v_extraDeps_1151_, lean_object* v_plan_1152_, lean_object* v_processing_1153_, lean_object* v_depTypes_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
size_t v_sz_1162_; size_t v___x_1163_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___x_1207_; 
v_sz_1162_ = lean_array_size(v_depTypes_1154_);
v___x_1163_ = ((size_t)0ULL);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(v_sz_1162_, v___x_1163_, v_depTypes_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___x_1225_; size_t v_sz_1226_; lean_object* v___x_1227_; lean_object* v_fst_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1248_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v___x_1225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v_sz_1226_ = lean_array_size(v_a_1208_);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(v_a_1208_, v_sz_1226_, v___x_1163_, v___x_1225_);
v_fst_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1227_, 1);
lean_dec(v_unused_1249_);
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_fst_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
v___jp_1209_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_array_get_size(v_a_1208_);
v___x_1218_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v___x_1219_ = lean_nat_dec_lt(v___x_1216_, v___x_1217_);
if (v___x_1219_ == 0)
{
lean_dec(v_a_1208_);
v___y_1175_ = v___y_1210_;
v___y_1176_ = v___y_1213_;
v___y_1177_ = v___y_1212_;
v___y_1178_ = v___y_1214_;
v___y_1179_ = v___y_1215_;
v___y_1180_ = v___y_1211_;
v___y_1181_ = v___x_1218_;
goto v___jp_1174_;
}
else
{
uint8_t v___x_1220_; 
v___x_1220_ = lean_nat_dec_le(v___x_1217_, v___x_1217_);
if (v___x_1220_ == 0)
{
if (v___x_1219_ == 0)
{
lean_dec(v_a_1208_);
v___y_1175_ = v___y_1210_;
v___y_1176_ = v___y_1213_;
v___y_1177_ = v___y_1212_;
v___y_1178_ = v___y_1214_;
v___y_1179_ = v___y_1215_;
v___y_1180_ = v___y_1211_;
v___y_1181_ = v___x_1218_;
goto v___jp_1174_;
}
else
{
size_t v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_usize_of_nat(v___x_1217_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_1152_, v_a_1208_, v___x_1163_, v___x_1221_, v___x_1218_);
lean_dec(v_a_1208_);
v___y_1175_ = v___y_1210_;
v___y_1176_ = v___y_1213_;
v___y_1177_ = v___y_1212_;
v___y_1178_ = v___y_1214_;
v___y_1179_ = v___y_1215_;
v___y_1180_ = v___y_1211_;
v___y_1181_ = v___x_1222_;
goto v___jp_1174_;
}
}
else
{
size_t v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_usize_of_nat(v___x_1217_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_1152_, v_a_1208_, v___x_1163_, v___x_1223_, v___x_1218_);
lean_dec(v_a_1208_);
v___y_1175_ = v___y_1210_;
v___y_1176_ = v___y_1213_;
v___y_1177_ = v___y_1212_;
v___y_1178_ = v___y_1214_;
v___y_1179_ = v___y_1215_;
v___y_1180_ = v___y_1211_;
v___y_1181_ = v___x_1224_;
goto v___jp_1174_;
}
}
}
v_resetjp_1229_:
{
if (lean_obj_tag(v_fst_1228_) == 0)
{
lean_del_object(v___x_1230_);
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
v___y_1213_ = v_a_1158_;
v___y_1214_ = v_a_1159_;
v___y_1215_ = v_a_1160_;
goto v___jp_1209_;
}
else
{
lean_object* v_val_1232_; 
v_val_1232_ = lean_ctor_get(v_fst_1228_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v_fst_1228_, 1);
if (lean_obj_tag(v_val_1232_) == 1)
{
lean_object* v_val_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v_val_1233_ = lean_ctor_get(v_val_1232_, 0);
lean_inc(v_val_1233_);
lean_dec_ref_known(v_val_1232_, 1);
v___x_1234_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4);
v___x_1235_ = l_Lean_MessageData_ofExpr(v_val_1233_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 7);
lean_ctor_set(v___x_1230_, 1, v___x_1235_);
lean_ctor_set(v___x_1230_, 0, v___x_1234_);
v___x_1237_ = v___x_1230_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_1237_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_dec_ref_known(v___x_1238_, 1);
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
v___y_1213_ = v_a_1158_;
v___y_1214_ = v_a_1159_;
v___y_1215_ = v_a_1160_;
goto v___jp_1209_;
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v_a_1208_);
lean_dec_ref(v_processing_1153_);
lean_dec_ref(v_plan_1152_);
lean_dec_ref(v_extraDeps_1151_);
lean_dec(v_className_1150_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
else
{
lean_dec(v_val_1232_);
lean_del_object(v___x_1230_);
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
v___y_1213_ = v_a_1158_;
v___y_1214_ = v_a_1159_;
v___y_1215_ = v_a_1160_;
goto v___jp_1209_;
}
}
}
}
else
{
lean_dec_ref(v_processing_1153_);
lean_dec_ref(v_plan_1152_);
lean_dec_ref(v_extraDeps_1151_);
lean_dec(v_className_1150_);
return v___x_1207_;
}
v___jp_1164_:
{
size_t v_sz_1172_; lean_object* v___x_1173_; 
v_sz_1172_ = lean_array_size(v___y_1165_);
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_1153_, v_className_1150_, v_extraDeps_1151_, v___y_1165_, v_sz_1172_, v___x_1163_, v_plan_1152_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec_ref(v___y_1165_);
return v___x_1173_;
}
v___jp_1174_:
{
lean_object* v___x_1182_; size_t v_sz_1183_; lean_object* v___x_1184_; lean_object* v_fst_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1205_; 
v___x_1182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v_sz_1183_ = lean_array_size(v___y_1181_);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(v_processing_1153_, v___y_1181_, v_sz_1183_, v___x_1163_, v___x_1182_);
v_fst_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v___x_1184_, 1);
lean_dec(v_unused_1206_);
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1205_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_fst_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1205_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
if (lean_obj_tag(v_fst_1185_) == 0)
{
lean_del_object(v___x_1187_);
v___y_1165_ = v___y_1181_;
v___y_1166_ = v___y_1175_;
v___y_1167_ = v___y_1180_;
v___y_1168_ = v___y_1177_;
v___y_1169_ = v___y_1176_;
v___y_1170_ = v___y_1178_;
v___y_1171_ = v___y_1179_;
goto v___jp_1164_;
}
else
{
lean_object* v_val_1189_; 
v_val_1189_ = lean_ctor_get(v_fst_1185_, 0);
lean_inc(v_val_1189_);
lean_dec_ref_known(v_fst_1185_, 1);
if (lean_obj_tag(v_val_1189_) == 1)
{
lean_object* v_val_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v_val_1190_ = lean_ctor_get(v_val_1189_, 0);
lean_inc(v_val_1190_);
lean_dec_ref_known(v_val_1189_, 1);
v___x_1191_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1);
v___x_1192_ = l_Lean_MessageData_ofExpr(v_val_1190_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 7);
lean_ctor_set(v___x_1187_, 1, v___x_1192_);
lean_ctor_set(v___x_1187_, 0, v___x_1191_);
v___x_1194_ = v___x_1187_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_1194_, v___y_1175_, v___y_1180_, v___y_1177_, v___y_1176_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_dec_ref_known(v___x_1195_, 1);
v___y_1165_ = v___y_1181_;
v___y_1166_ = v___y_1175_;
v___y_1167_ = v___y_1180_;
v___y_1168_ = v___y_1177_;
v___y_1169_ = v___y_1176_;
v___y_1170_ = v___y_1178_;
v___y_1171_ = v___y_1179_;
goto v___jp_1164_;
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_processing_1153_);
lean_dec_ref(v_plan_1152_);
lean_dec_ref(v_extraDeps_1151_);
lean_dec(v_className_1150_);
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
else
{
lean_dec(v_val_1189_);
lean_del_object(v___x_1187_);
v___y_1165_ = v___y_1181_;
v___y_1166_ = v___y_1175_;
v___y_1167_ = v___y_1180_;
v___y_1168_ = v___y_1177_;
v___y_1169_ = v___y_1176_;
v___y_1170_ = v___y_1178_;
v___y_1171_ = v___y_1179_;
goto v___jp_1164_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3(void){
_start:
{
lean_object* v_cls_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_cls_1258_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1));
v___x_1260_ = l_Lean_Name_append(v___x_1259_, v_cls_1258_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6));
v___x_1266_ = l_Lean_stringToMessageData(v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8));
v___x_1269_ = l_Lean_stringToMessageData(v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(lean_object* v_className_1276_, lean_object* v_extraDeps_1277_, lean_object* v_plan_1278_, lean_object* v_processing_1279_, lean_object* v_cls_1280_, lean_object* v_inst_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_cls_1289_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___x_1460_; 
v_cls_1289_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1460_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1289_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; uint8_t v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = lean_unbox(v_a_1461_);
lean_dec(v_a_1461_);
if (v___x_1462_ == 0)
{
v___y_1378_ = v_a_1282_;
v___y_1379_ = v_a_1283_;
v___y_1380_ = v_a_1284_;
v___y_1381_ = v_a_1285_;
v___y_1382_ = v_a_1286_;
v___y_1383_ = v_a_1287_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1463_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13);
lean_inc_ref(v_cls_1280_);
v___x_1464_ = l_Lean_MessageData_ofExpr(v_cls_1280_);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1289_, v___x_1465_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_dec_ref_known(v___x_1466_, 1);
v___y_1378_ = v_a_1282_;
v___y_1379_ = v_a_1283_;
v___y_1380_ = v_a_1284_;
v___y_1381_ = v_a_1285_;
v___y_1382_ = v_a_1286_;
v___y_1383_ = v_a_1287_;
goto v___jp_1377_;
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1475_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1460_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1460_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
v___jp_1290_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; size_t v_sz_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v_sz_1301_ = lean_array_size(v___y_1298_);
v___x_1302_ = ((size_t)0ULL);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v___y_1296_, v_className_1276_, v___y_1298_, v_sz_1301_, v___x_1302_, v___x_1300_, v___y_1295_, v___y_1291_, v___y_1292_, v___y_1297_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = lean_array_get_size(v___y_1296_);
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1299_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
lean_ctor_set(v___x_1307_, 2, v___x_1306_);
v___x_1308_ = lean_box(0);
v___x_1309_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___y_1298_, v___y_1296_, v___x_1307_, v___x_1308_, v___x_1299_, v___y_1295_, v___y_1291_, v___y_1292_, v___y_1297_, v___y_1293_, v___y_1294_);
lean_dec_ref_known(v___x_1307_, 3);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v___y_1298_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_toCold_1310_; lean_object* v_options_1311_; uint8_t v_hasTrace_1312_; 
lean_dec_ref_known(v___x_1309_, 1);
v_toCold_1310_ = lean_ctor_get(v___y_1293_, 0);
v_options_1311_ = lean_ctor_get(v_toCold_1310_, 2);
v_hasTrace_1312_ = lean_ctor_get_uint8(v_options_1311_, sizeof(void*)*1);
if (v_hasTrace_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec_ref(v_cls_1280_);
v___x_1313_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1276_, v_extraDeps_1277_, v_plan_1278_, v_processing_1279_, v_a_1304_, v___y_1295_, v___y_1291_, v___y_1292_, v___y_1297_, v___y_1293_, v___y_1294_);
return v___x_1313_;
}
else
{
lean_object* v_inheritedTraceOptions_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_inheritedTraceOptions_1314_ = lean_ctor_get(v_toCold_1310_, 11);
v___x_1315_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_1316_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1314_, v_options_1311_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref(v_cls_1280_);
v___x_1317_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1276_, v_extraDeps_1277_, v_plan_1278_, v_processing_1279_, v_a_1304_, v___y_1295_, v___y_1291_, v___y_1292_, v___y_1297_, v___y_1293_, v___y_1294_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1318_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5);
v___x_1319_ = l_Lean_MessageData_ofExpr(v_cls_1280_);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
lean_inc(v_a_1304_);
v___x_1323_ = lean_array_to_list(v_a_1304_);
v___x_1324_ = lean_box(0);
v___x_1325_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1323_, v___x_1324_);
v___x_1326_ = l_Lean_MessageData_ofList(v___x_1325_);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1322_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1289_, v___x_1327_, v___y_1292_, v___y_1297_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v___x_1329_; 
lean_dec_ref_known(v___x_1328_, 1);
v___x_1329_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1276_, v_extraDeps_1277_, v_plan_1278_, v_processing_1279_, v_a_1304_, v___y_1295_, v___y_1291_, v___y_1292_, v___y_1297_, v___y_1293_, v___y_1294_);
return v___x_1329_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_a_1304_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1330_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1328_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1328_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_a_1304_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1338_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1309_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1309_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_dec_ref(v___y_1298_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
return v___x_1303_;
}
}
v___jp_1346_:
{
lean_object* v___x_1356_; 
lean_inc_ref(v_cls_1280_);
v___x_1356_ = l_Lean_Meta_isExprDefEq(v_cls_1280_, v___y_1347_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; uint8_t v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = lean_unbox(v_a_1357_);
lean_dec(v_a_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1360_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1359_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec_ref_known(v___x_1360_, 1);
v___y_1291_ = v___y_1351_;
v___y_1292_ = v___y_1352_;
v___y_1293_ = v___y_1354_;
v___y_1294_ = v___y_1355_;
v___y_1295_ = v___y_1350_;
v___y_1296_ = v___y_1348_;
v___y_1297_ = v___y_1353_;
v___y_1298_ = v___y_1349_;
goto v___jp_1290_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
v___y_1291_ = v___y_1351_;
v___y_1292_ = v___y_1352_;
v___y_1293_ = v___y_1354_;
v___y_1294_ = v___y_1355_;
v___y_1295_ = v___y_1350_;
v___y_1296_ = v___y_1348_;
v___y_1297_ = v___y_1353_;
v___y_1298_ = v___y_1349_;
goto v___jp_1290_;
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1369_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1356_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1356_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
v___jp_1377_:
{
lean_object* v_val_1384_; lean_object* v_synthOrder_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1459_; 
v_val_1384_ = lean_ctor_get(v_inst_1281_, 0);
v_synthOrder_1385_ = lean_ctor_get(v_inst_1281_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_inst_1281_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1387_ = v_inst_1281_;
v_isShared_1388_ = v_isSharedCheck_1459_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_synthOrder_1385_);
lean_inc(v_val_1384_);
lean_dec(v_inst_1281_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1459_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; 
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
v___x_1389_ = lean_infer_type(v_val_1384_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = lean_box(0);
v___x_1392_ = 0;
v___x_1393_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1390_, v___x_1391_, v___x_1392_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v_snd_1395_; lean_object* v_fst_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1442_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v_snd_1395_ = lean_ctor_get(v_a_1394_, 1);
v_fst_1396_ = lean_ctor_get(v_a_1394_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_a_1394_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1398_ = v_a_1394_;
v_isShared_1399_ = v_isSharedCheck_1442_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_snd_1395_);
lean_inc(v_fst_1396_);
lean_dec(v_a_1394_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1442_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_snd_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1440_; 
v_snd_1400_ = lean_ctor_get(v_snd_1395_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_snd_1395_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_snd_1395_, 0);
lean_dec(v_unused_1441_);
v___x_1402_ = v_snd_1395_;
v_isShared_1403_ = v_isSharedCheck_1440_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_snd_1400_);
lean_dec(v_snd_1395_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1440_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; 
v___x_1404_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1289_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; uint8_t v___x_1406_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = lean_unbox(v_a_1405_);
lean_dec(v_a_1405_);
if (v___x_1406_ == 0)
{
lean_del_object(v___x_1402_);
lean_del_object(v___x_1398_);
lean_del_object(v___x_1387_);
v___y_1347_ = v_snd_1400_;
v___y_1348_ = v_fst_1396_;
v___y_1349_ = v_synthOrder_1385_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1380_;
v___y_1353_ = v___y_1381_;
v___y_1354_ = v___y_1382_;
v___y_1355_ = v___y_1383_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1407_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9);
lean_inc(v_fst_1396_);
v___x_1408_ = lean_array_to_list(v_fst_1396_);
v___x_1409_ = lean_box(0);
v___x_1410_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1408_, v___x_1409_);
v___x_1411_ = l_Lean_MessageData_ofList(v___x_1410_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 7);
lean_ctor_set(v___x_1402_, 1, v___x_1411_);
lean_ctor_set(v___x_1402_, 0, v___x_1407_);
v___x_1413_ = v___x_1402_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11);
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 7);
lean_ctor_set(v___x_1398_, 1, v___x_1414_);
lean_ctor_set(v___x_1398_, 0, v___x_1413_);
v___x_1416_ = v___x_1398_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_inc(v_snd_1400_);
v___x_1417_ = l_Lean_MessageData_ofExpr(v_snd_1400_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 7);
lean_ctor_set(v___x_1387_, 1, v___x_1417_);
lean_ctor_set(v___x_1387_, 0, v___x_1416_);
v___x_1419_ = v___x_1387_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1289_, v___x_1419_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_dec_ref_known(v___x_1420_, 1);
v___y_1347_ = v_snd_1400_;
v___y_1348_ = v_fst_1396_;
v___y_1349_ = v_synthOrder_1385_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1380_;
v___y_1353_ = v___y_1381_;
v___y_1354_ = v___y_1382_;
v___y_1355_ = v___y_1383_;
goto v___jp_1346_;
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_snd_1400_);
lean_dec(v_fst_1396_);
lean_dec_ref(v_synthOrder_1385_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
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
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_del_object(v___x_1402_);
lean_dec(v_snd_1400_);
lean_del_object(v___x_1398_);
lean_dec(v_fst_1396_);
lean_del_object(v___x_1387_);
lean_dec_ref(v_synthOrder_1385_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1432_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1404_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1404_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_del_object(v___x_1387_);
lean_dec_ref(v_synthOrder_1385_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1443_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1393_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1393_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
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
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_del_object(v___x_1387_);
lean_dec_ref(v_synthOrder_1385_);
lean_dec_ref(v_cls_1280_);
lean_dec_ref(v_processing_1279_);
lean_dec_ref(v_plan_1278_);
lean_dec_ref(v_extraDeps_1277_);
lean_dec(v_className_1276_);
v_a_1451_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1389_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1389_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(lean_object* v_className_1483_, lean_object* v_extraDeps_1484_, lean_object* v_plan_1485_, lean_object* v_processing_1486_, lean_object* v_a_1487_, lean_object* v_as_1488_, size_t v_sz_1489_, size_t v_i_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_usize_dec_lt(v_i_1490_, v_sz_1489_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; 
lean_dec_ref(v_a_1487_);
lean_dec_ref(v_processing_1486_);
lean_dec_ref(v_plan_1485_);
lean_dec_ref(v_extraDeps_1484_);
lean_dec(v_className_1483_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_b_1491_);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_a_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v_b_1491_);
v___x_1501_ = lean_box(0);
v___x_1502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0));
v_a_1503_ = lean_array_uget_borrowed(v_as_1488_, v_i_1490_);
lean_inc(v_a_1503_);
lean_inc_ref(v_a_1487_);
lean_inc_ref(v_processing_1486_);
lean_inc_ref(v_plan_1485_);
lean_inc_ref(v_extraDeps_1484_);
lean_inc(v_className_1483_);
v___x_1504_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(v_className_1483_, v_extraDeps_1484_, v_plan_1485_, v_processing_1486_, v_a_1487_, v_a_1503_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v_a_1487_);
lean_dec_ref(v_processing_1486_);
lean_dec_ref(v_plan_1485_);
lean_dec_ref(v_extraDeps_1484_);
lean_dec(v_className_1483_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_a_1505_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1501_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1529_; 
v_a_1515_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1517_ = v___x_1504_;
v_isShared_1518_ = v_isSharedCheck_1529_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1504_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1529_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
uint8_t v___y_1520_; uint8_t v___x_1527_; 
v___x_1527_ = l_Lean_Exception_isInterrupt(v_a_1515_);
if (v___x_1527_ == 0)
{
uint8_t v___x_1528_; 
lean_inc(v_a_1515_);
v___x_1528_ = l_Lean_Exception_isRuntime(v_a_1515_);
v___y_1520_ = v___x_1528_;
goto v___jp_1519_;
}
else
{
v___y_1520_ = v___x_1527_;
goto v___jp_1519_;
}
v___jp_1519_:
{
if (v___y_1520_ == 0)
{
size_t v___x_1521_; size_t v___x_1522_; 
lean_del_object(v___x_1517_);
lean_dec(v_a_1515_);
v___x_1521_ = ((size_t)1ULL);
v___x_1522_ = lean_usize_add(v_i_1490_, v___x_1521_);
v_i_1490_ = v___x_1522_;
v_b_1491_ = v___x_1502_;
goto _start;
}
else
{
lean_object* v___x_1525_; 
lean_dec_ref(v_a_1487_);
lean_dec_ref(v_processing_1486_);
lean_dec_ref(v_plan_1485_);
lean_dec_ref(v_extraDeps_1484_);
lean_dec(v_className_1483_);
if (v_isShared_1518_ == 0)
{
v___x_1525_ = v___x_1517_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1515_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8));
v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
return v___x_1544_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10));
v___x_1547_ = l_Lean_stringToMessageData(v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(lean_object* v_className_1548_, lean_object* v_extraDeps_1549_, lean_object* v_plan_1550_, lean_object* v_processing_1551_, lean_object* v_type_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v_toCold_1578_; lean_object* v_currRecDepth_1579_; lean_object* v_ref_1580_; uint16_t v_optionFlags_1581_; uint8_t v_suppressElabErrors_1582_; uint8_t v_isRecordingDeps_1583_; lean_object* v_maxRecDepth_1584_; lean_object* v_cls_1585_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_toCold_1578_ = lean_ctor_get(v_a_1557_, 0);
v_currRecDepth_1579_ = lean_ctor_get(v_a_1557_, 1);
v_ref_1580_ = lean_ctor_get(v_a_1557_, 2);
v_optionFlags_1581_ = lean_ctor_get_uint16(v_a_1557_, sizeof(void*)*3);
v_suppressElabErrors_1582_ = lean_ctor_get_uint8(v_a_1557_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1583_ = lean_ctor_get_uint8(v_a_1557_, sizeof(void*)*3 + 3);
v_maxRecDepth_1584_ = lean_ctor_get(v_toCold_1578_, 3);
v_cls_1585_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_nat_dec_eq(v_maxRecDepth_1584_, v___x_1765_);
if (v___x_1766_ == 0)
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_nat_dec_eq(v_currRecDepth_1579_, v_maxRecDepth_1584_);
if (v___x_1767_ == 0)
{
goto v___jp_1735_;
}
else
{
lean_object* v___x_1768_; 
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
lean_inc(v_ref_1580_);
v___x_1768_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_1580_);
return v___x_1768_;
}
}
else
{
goto v___jp_1735_;
}
v___jp_1560_:
{
lean_object* v___x_1568_; 
v___x_1568_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1548_, v_extraDeps_1549_, v_plan_1550_, v_processing_1551_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec_ref(v___y_1566_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1577_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = lean_array_push(v_a_1569_, v_type_1552_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
else
{
lean_dec_ref(v_type_1552_);
return v___x_1568_;
}
}
v___jp_1586_:
{
lean_object* v___x_1595_; size_t v_sz_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v___x_1595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0));
v_sz_1596_ = lean_array_size(v___y_1588_);
v___x_1597_ = ((size_t)0ULL);
lean_inc_ref(v_processing_1551_);
lean_inc_ref(v_plan_1550_);
lean_inc_ref(v_extraDeps_1549_);
lean_inc(v_className_1548_);
v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_1548_, v_extraDeps_1549_, v_plan_1550_, v_processing_1551_, v___y_1587_, v___y_1588_, v_sz_1596_, v___x_1597_, v___x_1595_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec_ref(v___y_1588_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1643_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1643_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1643_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v_fst_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1641_; 
v_fst_1603_ = lean_ctor_get(v_a_1599_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_a_1599_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v_a_1599_, 1);
lean_dec(v_unused_1642_);
v___x_1605_ = v_a_1599_;
v_isShared_1606_ = v_isSharedCheck_1641_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_fst_1603_);
lean_dec(v_a_1599_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1641_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
if (lean_obj_tag(v_fst_1603_) == 0)
{
lean_object* v___x_1607_; 
lean_del_object(v___x_1601_);
lean_inc_ref(v_extraDeps_1549_);
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc_ref(v_type_1552_);
v___x_1607_ = lean_apply_8(v_extraDeps_1549_, v_type_1552_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, lean_box(0));
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_toCold_1608_; lean_object* v_options_1609_; uint8_t v_hasTrace_1610_; 
v_toCold_1608_ = lean_ctor_get(v___y_1593_, 0);
v_options_1609_ = lean_ctor_get(v_toCold_1608_, 2);
v_hasTrace_1610_ = lean_ctor_get_uint8(v_options_1609_, sizeof(void*)*1);
if (v_hasTrace_1610_ == 0)
{
lean_object* v_a_1611_; 
lean_del_object(v___x_1605_);
v_a_1611_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1607_, 1);
v___y_1561_ = v_a_1611_;
v___y_1562_ = v___y_1589_;
v___y_1563_ = v___y_1590_;
v___y_1564_ = v___y_1591_;
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1593_;
v___y_1567_ = v___y_1594_;
goto v___jp_1560_;
}
else
{
lean_object* v_a_1612_; lean_object* v_inheritedTraceOptions_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_a_1612_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1607_, 1);
v_inheritedTraceOptions_1613_ = lean_ctor_get(v_toCold_1608_, 11);
v___x_1614_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_1615_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1613_, v_options_1609_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_del_object(v___x_1605_);
v___y_1561_ = v_a_1612_;
v___y_1562_ = v___y_1589_;
v___y_1563_ = v___y_1590_;
v___y_1564_ = v___y_1591_;
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1593_;
v___y_1567_ = v___y_1594_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1);
lean_inc_ref(v_type_1552_);
v___x_1617_ = l_Lean_MessageData_ofExpr(v_type_1552_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 7);
lean_ctor_set(v___x_1605_, 1, v___x_1617_);
lean_ctor_set(v___x_1605_, 0, v___x_1616_);
v___x_1619_ = v___x_1605_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1620_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
lean_inc(v_a_1612_);
v___x_1622_ = lean_array_to_list(v_a_1612_);
v___x_1623_ = lean_box(0);
v___x_1624_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1622_, v___x_1623_);
v___x_1625_ = l_Lean_MessageData_ofList(v___x_1624_);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1621_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1585_, v___x_1626_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref_known(v___x_1627_, 1);
v___y_1561_ = v_a_1612_;
v___y_1562_ = v___y_1589_;
v___y_1563_ = v___y_1590_;
v___y_1564_ = v___y_1591_;
v___y_1565_ = v___y_1592_;
v___y_1566_ = v___y_1593_;
v___y_1567_ = v___y_1594_;
goto v___jp_1560_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_a_1612_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1605_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
return v___x_1607_;
}
}
else
{
lean_object* v_val_1637_; lean_object* v___x_1639_; 
lean_del_object(v___x_1605_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_val_1637_ = lean_ctor_get(v_fst_1603_, 0);
lean_inc(v_val_1637_);
lean_dec_ref_known(v_fst_1603_, 1);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v_val_1637_);
v___x_1639_ = v___x_1601_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_val_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_a_1644_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1598_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1598_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
v___jp_1652_:
{
uint8_t v___x_1659_; 
v___x_1659_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_plan_1550_, v_type_1552_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_mk_empty_array_with_capacity(v___x_1660_);
lean_inc_ref(v_type_1552_);
v___x_1662_ = lean_array_push(v___x_1661_, v_type_1552_);
lean_inc(v_className_1548_);
v___x_1663_ = l_Lean_Meta_mkAppM(v_className_1548_, v___x_1662_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_n(v_a_1664_, 2);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = l_Lean_Meta_SynthInstance_getInstances(v_a_1664_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1585_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; uint8_t v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = lean_unbox(v_a_1668_);
lean_dec(v_a_1668_);
if (v___x_1669_ == 0)
{
v___y_1587_ = v_a_1664_;
v___y_1588_ = v_a_1666_;
v___y_1589_ = v___y_1653_;
v___y_1590_ = v___y_1654_;
v___y_1591_ = v___y_1655_;
v___y_1592_ = v___y_1656_;
v___y_1593_ = v___y_1657_;
v___y_1594_ = v___y_1658_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1670_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5);
lean_inc(v_a_1664_);
v___x_1671_ = l_Lean_MessageData_ofExpr(v_a_1664_);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_array_get_size(v_a_1666_);
v___x_1676_ = l_Nat_reprFast(v___x_1675_);
v___x_1677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
v___x_1678_ = l_Lean_MessageData_ofFormat(v___x_1677_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1674_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1585_, v___x_1679_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_dec_ref_known(v___x_1680_, 1);
v___y_1587_ = v_a_1664_;
v___y_1588_ = v_a_1666_;
v___y_1589_ = v___y_1653_;
v___y_1590_ = v___y_1654_;
v___y_1591_ = v___y_1655_;
v___y_1592_ = v___y_1656_;
v___y_1593_ = v___y_1657_;
v___y_1594_ = v___y_1658_;
goto v___jp_1586_;
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1666_);
lean_dec(v_a_1664_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_a_1666_);
lean_dec(v_a_1664_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_a_1689_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1667_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1667_);
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
lean_dec(v_a_1664_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_a_1697_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1665_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1665_);
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
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_a_1705_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1663_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1663_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_object* v___x_1713_; 
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v_plan_1550_);
return v___x_1713_;
}
}
v___jp_1714_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1719_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___y_1718_, v___y_1715_);
v___x_1720_ = l_Lean_MessageData_ofList(v___x_1719_);
v___x_1721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___y_1716_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
lean_inc_ref(v_type_1552_);
v___x_1724_ = l_Lean_MessageData_ofExpr(v_type_1552_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1585_, v___x_1725_, v_a_1555_, v_a_1556_, v___y_1717_, v_a_1558_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_dec_ref_known(v___x_1726_, 1);
v___y_1653_ = v_a_1553_;
v___y_1654_ = v_a_1554_;
v___y_1655_ = v_a_1555_;
v___y_1656_ = v_a_1556_;
v___y_1657_ = v___y_1717_;
v___y_1658_ = v_a_1558_;
goto v___jp_1652_;
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v___y_1717_);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
v___jp_1735_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_add(v_currRecDepth_1579_, v___x_1736_);
lean_inc(v_ref_1580_);
lean_inc_ref(v_toCold_1578_);
v___x_1738_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1738_, 0, v_toCold_1578_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
lean_ctor_set(v___x_1738_, 2, v_ref_1580_);
lean_ctor_set_uint16(v___x_1738_, sizeof(void*)*3, v_optionFlags_1581_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*3 + 2, v_suppressElabErrors_1582_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*3 + 3, v_isRecordingDeps_1583_);
v___x_1739_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1585_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v___x_1738_, v_a_1558_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; uint8_t v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = lean_unbox(v_a_1740_);
lean_dec(v_a_1740_);
if (v___x_1741_ == 0)
{
v___y_1653_ = v_a_1553_;
v___y_1654_ = v_a_1554_;
v___y_1655_ = v_a_1555_;
v___y_1656_ = v_a_1556_;
v___y_1657_ = v___x_1738_;
v___y_1658_ = v_a_1558_;
goto v___jp_1652_;
}
else
{
lean_object* v_buckets_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v_buckets_1742_ = lean_ctor_get(v_processing_1551_, 1);
v___x_1743_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9);
lean_inc_ref(v_plan_1550_);
v___x_1744_ = lean_array_to_list(v_plan_1550_);
v___x_1745_ = lean_box(0);
v___x_1746_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1744_, v___x_1745_);
v___x_1747_ = l_Lean_MessageData_ofList(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1743_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = lean_array_get_size(v_buckets_1742_);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_nat_dec_lt(v___x_1752_, v___x_1751_);
if (v___x_1753_ == 0)
{
v___y_1715_ = v___x_1745_;
v___y_1716_ = v___x_1750_;
v___y_1717_ = v___x_1738_;
v___y_1718_ = v___x_1745_;
goto v___jp_1714_;
}
else
{
size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_usize_of_nat(v___x_1751_);
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_buckets_1742_, v___x_1754_, v___x_1755_, v___x_1745_);
v___y_1715_ = v___x_1745_;
v___y_1716_ = v___x_1750_;
v___y_1717_ = v___x_1738_;
v___y_1718_ = v___x_1756_;
goto v___jp_1714_;
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref_known(v___x_1738_, 3);
lean_dec_ref(v_type_1552_);
lean_dec_ref(v_processing_1551_);
lean_dec_ref(v_plan_1550_);
lean_dec_ref(v_extraDeps_1549_);
lean_dec(v_className_1548_);
v_a_1757_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1739_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1739_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(lean_object* v_processing_1769_, lean_object* v_className_1770_, lean_object* v_extraDeps_1771_, lean_object* v_as_1772_, size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_usize_dec_lt(v_i_1774_, v_sz_1773_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; 
lean_dec_ref(v_extraDeps_1771_);
lean_dec(v_className_1770_);
lean_dec_ref(v_processing_1769_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v_b_1775_);
return v___x_1784_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_a_1785_ = lean_array_uget_borrowed(v_as_1772_, v_i_1774_);
v___x_1786_ = lean_box(0);
lean_inc_n(v_a_1785_, 2);
lean_inc_ref(v_processing_1769_);
v___x_1787_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v_processing_1769_, v_a_1785_, v___x_1786_);
lean_inc_ref(v_extraDeps_1771_);
lean_inc(v_className_1770_);
v___x_1788_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_1770_, v_extraDeps_1771_, v_b_1775_, v___x_1787_, v_a_1785_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; size_t v___x_1790_; size_t v___x_1791_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = ((size_t)1ULL);
v___x_1791_ = lean_usize_add(v_i_1774_, v___x_1790_);
v_i_1774_ = v___x_1791_;
v_b_1775_ = v_a_1789_;
goto _start;
}
else
{
lean_dec_ref(v_extraDeps_1771_);
lean_dec(v_className_1770_);
lean_dec_ref(v_processing_1769_);
return v___x_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11___boxed(lean_object* v_processing_1793_, lean_object* v_className_1794_, lean_object* v_extraDeps_1795_, lean_object* v_as_1796_, lean_object* v_sz_1797_, lean_object* v_i_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
size_t v_sz_boxed_1807_; size_t v_i_boxed_1808_; lean_object* v_res_1809_; 
v_sz_boxed_1807_ = lean_unbox_usize(v_sz_1797_);
lean_dec(v_sz_1797_);
v_i_boxed_1808_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_1793_, v_className_1794_, v_extraDeps_1795_, v_as_1796_, v_sz_boxed_1807_, v_i_boxed_1808_, v_b_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_as_1796_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___boxed(lean_object* v_className_1810_, lean_object* v_extraDeps_1811_, lean_object* v_plan_1812_, lean_object* v_processing_1813_, lean_object* v_a_1814_, lean_object* v_as_1815_, lean_object* v_sz_1816_, lean_object* v_i_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
size_t v_sz_boxed_1826_; size_t v_i_boxed_1827_; lean_object* v_res_1828_; 
v_sz_boxed_1826_ = lean_unbox_usize(v_sz_1816_);
lean_dec(v_sz_1816_);
v_i_boxed_1827_ = lean_unbox_usize(v_i_1817_);
lean_dec(v_i_1817_);
v_res_1828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_1810_, v_extraDeps_1811_, v_plan_1812_, v_processing_1813_, v_a_1814_, v_as_1815_, v_sz_boxed_1826_, v_i_boxed_1827_, v_b_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v_as_1815_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___boxed(lean_object* v_className_1829_, lean_object* v_extraDeps_1830_, lean_object* v_plan_1831_, lean_object* v_processing_1832_, lean_object* v_depTypes_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1829_, v_extraDeps_1830_, v_plan_1831_, v_processing_1832_, v_depTypes_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___boxed(lean_object* v_className_1842_, lean_object* v_extraDeps_1843_, lean_object* v_plan_1844_, lean_object* v_processing_1845_, lean_object* v_cls_1846_, lean_object* v_inst_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(v_className_1842_, v_extraDeps_1843_, v_plan_1844_, v_processing_1845_, v_cls_1846_, v_inst_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___boxed(lean_object* v_className_1856_, lean_object* v_extraDeps_1857_, lean_object* v_plan_1858_, lean_object* v_processing_1859_, lean_object* v_type_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_1856_, v_extraDeps_1857_, v_plan_1858_, v_processing_1859_, v_type_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(lean_object* v_e_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_e_1869_, v___y_1873_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___boxed(lean_object* v_e_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(v_e_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(lean_object* v_cls_1887_, lean_object* v_msg_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1887_, v_msg_1888_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___boxed(lean_object* v_cls_1897_, lean_object* v_msg_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(v_cls_1897_, v_msg_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8(lean_object* v_00_u03b2_1907_, lean_object* v_m_1908_, lean_object* v_a_1909_, lean_object* v_b_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v_m_1908_, v_a_1909_, v_b_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(lean_object* v_00_u03b2_1912_, lean_object* v_m_1913_, lean_object* v_a_1914_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(v_m_1913_, v_a_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___boxed(lean_object* v_00_u03b2_1916_, lean_object* v_m_1917_, lean_object* v_a_1918_){
_start:
{
uint8_t v_res_1919_; lean_object* v_r_1920_; 
v_res_1919_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(v_00_u03b2_1916_, v_m_1917_, v_a_1918_);
lean_dec_ref(v_a_1918_);
lean_dec_ref(v_m_1917_);
v_r_1920_ = lean_box(v_res_1919_);
return v_r_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(lean_object* v_00_u03b1_1921_, lean_object* v_msg_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v_msg_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___boxed(lean_object* v_00_u03b1_1931_, lean_object* v_msg_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(v_00_u03b1_1931_, v_msg_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(lean_object* v_00_u03b1_1941_, lean_object* v_msg_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v_msg_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___boxed(lean_object* v_00_u03b1_1949_, lean_object* v_msg_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(v_00_u03b1_1949_, v_msg_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(lean_object* v___x_1957_, lean_object* v_fst_1958_, lean_object* v_range_1959_, lean_object* v_b_1960_, lean_object* v_i_1961_, lean_object* v_hs_1962_, lean_object* v_hl_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_1957_, v_fst_1958_, v_range_1959_, v_b_1960_, v_i_1961_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___boxed(lean_object* v___x_1972_, lean_object* v_fst_1973_, lean_object* v_range_1974_, lean_object* v_b_1975_, lean_object* v_i_1976_, lean_object* v_hs_1977_, lean_object* v_hl_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(v___x_1972_, v_fst_1973_, v_range_1974_, v_b_1975_, v_i_1976_, v_hs_1977_, v_hl_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec_ref(v_range_1974_);
lean_dec_ref(v_fst_1973_);
lean_dec_ref(v___x_1972_);
return v_res_1986_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(lean_object* v_00_u03b2_1987_, lean_object* v_a_1988_, lean_object* v_x_1989_){
_start:
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_1988_, v_x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1991_, lean_object* v_a_1992_, lean_object* v_x_1993_){
_start:
{
uint8_t v_res_1994_; lean_object* v_r_1995_; 
v_res_1994_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(v_00_u03b2_1991_, v_a_1992_, v_x_1993_);
lean_dec(v_x_1993_);
lean_dec_ref(v_a_1992_);
v_r_1995_ = lean_box(v_res_1994_);
return v_r_1995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11(lean_object* v_00_u03b2_1996_, lean_object* v_data_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(v_data_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(lean_object* v_msgData_1999_, lean_object* v_macroStack_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_msgData_1999_, v_macroStack_2000_, v___y_2005_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___boxed(lean_object* v_msgData_2009_, lean_object* v_macroStack_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(v_msgData_2009_, v_macroStack_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14(lean_object* v_00_u03b2_2019_, lean_object* v_i_2020_, lean_object* v_source_2021_, lean_object* v_target_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(v_i_2020_, v_source_2021_, v_target_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26(lean_object* v_00_u03b2_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(v_x_2025_, v_x_2026_);
return v___x_2027_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_unsigned_to_nat(32u);
v___x_2029_ = lean_mk_empty_array_with_capacity(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2031_ = ((size_t)5ULL);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_unsigned_to_nat(32u);
v___x_2034_ = lean_mk_empty_array_with_capacity(v___x_2033_);
v___x_2035_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0);
v___x_2036_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v___x_2034_);
lean_ctor_set(v___x_2036_, 2, v___x_2032_);
lean_ctor_set(v___x_2036_, 3, v___x_2032_);
lean_ctor_set_usize(v___x_2036_, 4, v___x_2031_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; lean_object* v_traceState_2040_; lean_object* v_traces_2041_; lean_object* v___x_2042_; lean_object* v_traceState_2043_; lean_object* v_env_2044_; lean_object* v_nextMacroScope_2045_; lean_object* v_ngen_2046_; lean_object* v_auxDeclNGen_2047_; lean_object* v_cache_2048_; lean_object* v_recordedDeps_2049_; lean_object* v_messages_2050_; lean_object* v_infoState_2051_; lean_object* v_snapshotTasks_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2071_; 
v___x_2039_ = lean_st_ref_get(v___y_2037_);
v_traceState_2040_ = lean_ctor_get(v___x_2039_, 4);
lean_inc_ref(v_traceState_2040_);
lean_dec(v___x_2039_);
v_traces_2041_ = lean_ctor_get(v_traceState_2040_, 0);
lean_inc_ref(v_traces_2041_);
lean_dec_ref(v_traceState_2040_);
v___x_2042_ = lean_st_ref_take(v___y_2037_);
v_traceState_2043_ = lean_ctor_get(v___x_2042_, 4);
v_env_2044_ = lean_ctor_get(v___x_2042_, 0);
v_nextMacroScope_2045_ = lean_ctor_get(v___x_2042_, 1);
v_ngen_2046_ = lean_ctor_get(v___x_2042_, 2);
v_auxDeclNGen_2047_ = lean_ctor_get(v___x_2042_, 3);
v_cache_2048_ = lean_ctor_get(v___x_2042_, 5);
v_recordedDeps_2049_ = lean_ctor_get(v___x_2042_, 6);
v_messages_2050_ = lean_ctor_get(v___x_2042_, 7);
v_infoState_2051_ = lean_ctor_get(v___x_2042_, 8);
v_snapshotTasks_2052_ = lean_ctor_get(v___x_2042_, 9);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2054_ = v___x_2042_;
v_isShared_2055_ = v_isSharedCheck_2071_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_snapshotTasks_2052_);
lean_inc(v_infoState_2051_);
lean_inc(v_messages_2050_);
lean_inc(v_recordedDeps_2049_);
lean_inc(v_cache_2048_);
lean_inc(v_traceState_2043_);
lean_inc(v_auxDeclNGen_2047_);
lean_inc(v_ngen_2046_);
lean_inc(v_nextMacroScope_2045_);
lean_inc(v_env_2044_);
lean_dec(v___x_2042_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2071_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
uint64_t v_tid_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2069_; 
v_tid_2056_ = lean_ctor_get_uint64(v_traceState_2043_, sizeof(void*)*1);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_traceState_2043_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; 
v_unused_2070_ = lean_ctor_get(v_traceState_2043_, 0);
lean_dec(v_unused_2070_);
v___x_2058_ = v_traceState_2043_;
v_isShared_2059_ = v_isSharedCheck_2069_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v_traceState_2043_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2069_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2060_);
lean_ctor_set_uint64(v_reuseFailAlloc_2068_, sizeof(void*)*1, v_tid_2056_);
v___x_2062_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2064_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 4, v___x_2062_);
v___x_2064_ = v___x_2054_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_env_2044_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_nextMacroScope_2045_);
lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_ngen_2046_);
lean_ctor_set(v_reuseFailAlloc_2067_, 3, v_auxDeclNGen_2047_);
lean_ctor_set(v_reuseFailAlloc_2067_, 4, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2067_, 5, v_cache_2048_);
lean_ctor_set(v_reuseFailAlloc_2067_, 6, v_recordedDeps_2049_);
lean_ctor_set(v_reuseFailAlloc_2067_, 7, v_messages_2050_);
lean_ctor_set(v_reuseFailAlloc_2067_, 8, v_infoState_2051_);
lean_ctor_set(v_reuseFailAlloc_2067_, 9, v_snapshotTasks_2052_);
v___x_2064_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_st_ref_put(v___y_2037_, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_traces_2041_);
return v___x_2066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___boxed(lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_2072_);
lean_dec(v___y_2072_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_2080_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___boxed(lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2090_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0));
v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
return v___x_2093_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2));
v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(lean_object* v_className_2097_, lean_object* v_type_2098_, lean_object* v_r_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___y_2118_; 
v___x_2107_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1);
v___x_2108_ = 0;
v___x_2109_ = l_Lean_MessageData_ofConstName(v_className_2097_, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2107_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = l_Lean_MessageData_ofExpr(v_type_2098_);
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
if (lean_obj_tag(v_r_2099_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v_r_2099_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v_r_2099_, 1);
v___x_2122_ = l_Lean_Exception_toMessageData(v_a_2121_);
v___y_2118_ = v___x_2122_;
goto v___jp_2117_;
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_a_2123_ = lean_ctor_get(v_r_2099_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v_r_2099_, 1);
v___x_2124_ = lean_array_to_list(v_a_2123_);
v___x_2125_ = lean_box(0);
v___x_2126_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_2124_, v___x_2125_);
v___x_2127_ = l_Lean_MessageData_ofList(v___x_2126_);
v___y_2118_ = v___x_2127_;
goto v___jp_2117_;
}
v___jp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2116_);
lean_ctor_set(v___x_2119_, 1, v___y_2118_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed(lean_object* v_className_2128_, lean_object* v_type_2129_, lean_object* v_r_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(v_className_2128_, v_type_2129_, v_r_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(lean_object* v_opts_2139_, lean_object* v_opt_2140_){
_start:
{
lean_object* v_name_2141_; lean_object* v_defValue_2142_; lean_object* v_map_2143_; lean_object* v___x_2144_; 
v_name_2141_ = lean_ctor_get(v_opt_2140_, 0);
v_defValue_2142_ = lean_ctor_get(v_opt_2140_, 1);
v_map_2143_ = lean_ctor_get(v_opts_2139_, 0);
v___x_2144_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2143_, v_name_2141_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_inc(v_defValue_2142_);
return v_defValue_2142_;
}
else
{
lean_object* v_val_2145_; 
v_val_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v___x_2144_, 1);
if (lean_obj_tag(v_val_2145_) == 3)
{
lean_object* v_v_2146_; 
v_v_2146_ = lean_ctor_get(v_val_2145_, 0);
lean_inc(v_v_2146_);
lean_dec_ref_known(v_val_2145_, 1);
return v_v_2146_;
}
else
{
lean_dec(v_val_2145_);
lean_inc(v_defValue_2142_);
return v_defValue_2142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4___boxed(lean_object* v_opts_2147_, lean_object* v_opt_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2147_, v_opt_2148_);
lean_dec_ref(v_opt_2148_);
lean_dec_ref(v_opts_2147_);
return v_res_2149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(lean_object* v_e_2150_){
_start:
{
if (lean_obj_tag(v_e_2150_) == 0)
{
uint8_t v___x_2151_; 
v___x_2151_ = 2;
return v___x_2151_;
}
else
{
uint8_t v___x_2152_; 
v___x_2152_ = 0;
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___boxed(lean_object* v_e_2153_){
_start:
{
uint8_t v_res_2154_; lean_object* v_r_2155_; 
v_res_2154_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_e_2153_);
lean_dec_ref(v_e_2153_);
v_r_2155_ = lean_box(v_res_2154_);
return v_r_2155_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(lean_object* v_x_2156_){
_start:
{
if (lean_obj_tag(v_x_2156_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
v_a_2158_ = lean_ctor_get(v_x_2156_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_x_2156_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v_x_2156_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v_x_2156_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 1);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
v_a_2166_ = lean_ctor_get(v_x_2156_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_x_2156_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v_x_2156_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v_x_2156_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set_tag(v___x_2168_, 0);
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg___boxed(lean_object* v_x_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_x_2174_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(size_t v_sz_2177_, size_t v_i_2178_, lean_object* v_bs_2179_){
_start:
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_usize_dec_lt(v_i_2178_, v_sz_2177_);
if (v___x_2180_ == 0)
{
return v_bs_2179_;
}
else
{
lean_object* v_v_2181_; lean_object* v_msg_2182_; lean_object* v___x_2183_; lean_object* v_bs_x27_2184_; size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v_v_2181_ = lean_array_uget_borrowed(v_bs_2179_, v_i_2178_);
v_msg_2182_ = lean_ctor_get(v_v_2181_, 1);
lean_inc_ref(v_msg_2182_);
v___x_2183_ = lean_unsigned_to_nat(0u);
v_bs_x27_2184_ = lean_array_uset(v_bs_2179_, v_i_2178_, v___x_2183_);
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_add(v_i_2178_, v___x_2185_);
v___x_2187_ = lean_array_uset(v_bs_x27_2184_, v_i_2178_, v_msg_2182_);
v_i_2178_ = v___x_2186_;
v_bs_2179_ = v___x_2187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2189_, lean_object* v_i_2190_, lean_object* v_bs_2191_){
_start:
{
size_t v_sz_boxed_2192_; size_t v_i_boxed_2193_; lean_object* v_res_2194_; 
v_sz_boxed_2192_ = lean_unbox_usize(v_sz_2189_);
lean_dec(v_sz_2189_);
v_i_boxed_2193_ = lean_unbox_usize(v_i_2190_);
lean_dec(v_i_2190_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(v_sz_boxed_2192_, v_i_boxed_2193_, v_bs_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(lean_object* v_oldTraces_2195_, lean_object* v_data_2196_, lean_object* v_ref_2197_, lean_object* v_msg_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_toCold_2204_; lean_object* v_currRecDepth_2205_; lean_object* v_ref_2206_; uint16_t v_optionFlags_2207_; uint8_t v_suppressElabErrors_2208_; uint8_t v_isRecordingDeps_2209_; lean_object* v_ref_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_traceState_2213_; lean_object* v_traces_2214_; lean_object* v___x_2215_; size_t v_sz_2216_; size_t v___x_2217_; lean_object* v___x_2218_; lean_object* v_msg_2219_; lean_object* v___x_2220_; lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2259_; 
v_toCold_2204_ = lean_ctor_get(v___y_2201_, 0);
v_currRecDepth_2205_ = lean_ctor_get(v___y_2201_, 1);
v_ref_2206_ = lean_ctor_get(v___y_2201_, 2);
v_optionFlags_2207_ = lean_ctor_get_uint16(v___y_2201_, sizeof(void*)*3);
v_suppressElabErrors_2208_ = lean_ctor_get_uint8(v___y_2201_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2209_ = lean_ctor_get_uint8(v___y_2201_, sizeof(void*)*3 + 3);
v_ref_2210_ = l_Lean_replaceRef(v_ref_2197_, v_ref_2206_);
lean_inc(v_currRecDepth_2205_);
lean_inc_ref(v_toCold_2204_);
v___x_2211_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2211_, 0, v_toCold_2204_);
lean_ctor_set(v___x_2211_, 1, v_currRecDepth_2205_);
lean_ctor_set(v___x_2211_, 2, v_ref_2210_);
lean_ctor_set_uint16(v___x_2211_, sizeof(void*)*3, v_optionFlags_2207_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*3 + 2, v_suppressElabErrors_2208_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*3 + 3, v_isRecordingDeps_2209_);
v___x_2212_ = lean_st_ref_get(v___y_2202_);
v_traceState_2213_ = lean_ctor_get(v___x_2212_, 4);
lean_inc_ref(v_traceState_2213_);
lean_dec(v___x_2212_);
v_traces_2214_ = lean_ctor_get(v_traceState_2213_, 0);
lean_inc_ref(v_traces_2214_);
lean_dec_ref(v_traceState_2213_);
v___x_2215_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2214_);
lean_dec_ref(v_traces_2214_);
v_sz_2216_ = lean_array_size(v___x_2215_);
v___x_2217_ = ((size_t)0ULL);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(v_sz_2216_, v___x_2217_, v___x_2215_);
v_msg_2219_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2219_, 0, v_data_2196_);
lean_ctor_set(v_msg_2219_, 1, v_msg_2198_);
lean_ctor_set(v_msg_2219_, 2, v___x_2218_);
v___x_2220_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_2219_, v___y_2199_, v___y_2200_, v___x_2211_, v___y_2202_);
lean_dec_ref_known(v___x_2211_, 3);
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2259_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2259_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v_traceState_2226_; lean_object* v_env_2227_; lean_object* v_nextMacroScope_2228_; lean_object* v_ngen_2229_; lean_object* v_auxDeclNGen_2230_; lean_object* v_cache_2231_; lean_object* v_recordedDeps_2232_; lean_object* v_messages_2233_; lean_object* v_infoState_2234_; lean_object* v_snapshotTasks_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2258_; 
v___x_2225_ = lean_st_ref_take(v___y_2202_);
v_traceState_2226_ = lean_ctor_get(v___x_2225_, 4);
v_env_2227_ = lean_ctor_get(v___x_2225_, 0);
v_nextMacroScope_2228_ = lean_ctor_get(v___x_2225_, 1);
v_ngen_2229_ = lean_ctor_get(v___x_2225_, 2);
v_auxDeclNGen_2230_ = lean_ctor_get(v___x_2225_, 3);
v_cache_2231_ = lean_ctor_get(v___x_2225_, 5);
v_recordedDeps_2232_ = lean_ctor_get(v___x_2225_, 6);
v_messages_2233_ = lean_ctor_get(v___x_2225_, 7);
v_infoState_2234_ = lean_ctor_get(v___x_2225_, 8);
v_snapshotTasks_2235_ = lean_ctor_get(v___x_2225_, 9);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2237_ = v___x_2225_;
v_isShared_2238_ = v_isSharedCheck_2258_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_snapshotTasks_2235_);
lean_inc(v_infoState_2234_);
lean_inc(v_messages_2233_);
lean_inc(v_recordedDeps_2232_);
lean_inc(v_cache_2231_);
lean_inc(v_traceState_2226_);
lean_inc(v_auxDeclNGen_2230_);
lean_inc(v_ngen_2229_);
lean_inc(v_nextMacroScope_2228_);
lean_inc(v_env_2227_);
lean_dec(v___x_2225_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2258_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
uint64_t v_tid_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2256_; 
v_tid_2239_ = lean_ctor_get_uint64(v_traceState_2226_, sizeof(void*)*1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_traceState_2226_);
if (v_isSharedCheck_2256_ == 0)
{
lean_object* v_unused_2257_; 
v_unused_2257_ = lean_ctor_get(v_traceState_2226_, 0);
lean_dec(v_unused_2257_);
v___x_2241_ = v_traceState_2226_;
v_isShared_2242_ = v_isSharedCheck_2256_;
goto v_resetjp_2240_;
}
else
{
lean_dec(v_traceState_2226_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2256_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2244_, 0, v_ref_2197_);
lean_ctor_set(v___x_2244_, 1, v_a_2221_);
v___x_2245_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2195_, v___x_2244_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2245_);
v___x_2247_ = v___x_2241_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2245_);
lean_ctor_set_uint64(v_reuseFailAlloc_2255_, sizeof(void*)*1, v_tid_2239_);
v___x_2247_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 4, v___x_2247_);
v___x_2249_ = v___x_2237_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_env_2227_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_nextMacroScope_2228_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_ngen_2229_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_auxDeclNGen_2230_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2254_, 5, v_cache_2231_);
lean_ctor_set(v_reuseFailAlloc_2254_, 6, v_recordedDeps_2232_);
lean_ctor_set(v_reuseFailAlloc_2254_, 7, v_messages_2233_);
lean_ctor_set(v_reuseFailAlloc_2254_, 8, v_infoState_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 9, v_snapshotTasks_2235_);
v___x_2249_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_st_ref_put(v___y_2202_, v___x_2249_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2243_);
v___x_2252_ = v___x_2223_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2243_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg___boxed(lean_object* v_oldTraces_2260_, lean_object* v_data_2261_, lean_object* v_ref_2262_, lean_object* v_msg_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2260_, v_data_2261_, v_ref_2262_, v_msg_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
return v_res_2269_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0));
v___x_2272_ = l_Lean_stringToMessageData(v___x_2271_);
return v___x_2272_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2273_; double v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(1000u);
v___x_2274_ = lean_float_of_nat(v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(lean_object* v_cls_2275_, uint8_t v_collapsed_2276_, lean_object* v_tag_2277_, lean_object* v_opts_2278_, uint8_t v_clsEnabled_2279_, lean_object* v_oldTraces_2280_, lean_object* v_msg_2281_, lean_object* v_resStartStop_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_fst_2290_; lean_object* v_snd_2291_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v_data_2295_; lean_object* v_fst_2306_; lean_object* v_snd_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; lean_object* v___y_2311_; lean_object* v_a_2312_; uint8_t v___y_2327_; double v___y_2359_; 
v_fst_2290_ = lean_ctor_get(v_resStartStop_2282_, 0);
lean_inc(v_fst_2290_);
v_snd_2291_ = lean_ctor_get(v_resStartStop_2282_, 1);
lean_inc(v_snd_2291_);
lean_dec_ref(v_resStartStop_2282_);
v_fst_2306_ = lean_ctor_get(v_snd_2291_, 0);
lean_inc(v_fst_2306_);
v_snd_2307_ = lean_ctor_get(v_snd_2291_, 1);
lean_inc(v_snd_2307_);
lean_dec(v_snd_2291_);
v___x_2308_ = l_Lean_trace_profiler;
v___x_2309_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_2278_, v___x_2308_);
if (v___x_2309_ == 0)
{
v___y_2327_ = v___x_2309_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2365_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_2278_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; double v___x_2368_; double v___x_2369_; double v___x_2370_; 
v___x_2366_ = l_Lean_trace_profiler_threshold;
v___x_2367_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2278_, v___x_2366_);
v___x_2368_ = lean_float_of_nat(v___x_2367_);
v___x_2369_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2);
v___x_2370_ = lean_float_div(v___x_2368_, v___x_2369_);
v___y_2359_ = v___x_2370_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; double v___x_2373_; 
v___x_2371_ = l_Lean_trace_profiler_threshold;
v___x_2372_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2278_, v___x_2371_);
v___x_2373_ = lean_float_of_nat(v___x_2372_);
v___y_2359_ = v___x_2373_;
goto v___jp_2358_;
}
}
v___jp_2292_:
{
lean_object* v___x_2296_; 
lean_inc(v___y_2294_);
v___x_2296_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2280_, v_data_2295_, v___y_2294_, v___y_2293_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2297_; 
lean_dec_ref_known(v___x_2296_, 1);
v___x_2297_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_fst_2290_);
return v___x_2297_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_fst_2290_);
v_a_2298_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2296_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
v___jp_2310_:
{
uint8_t v_result_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; double v___x_2316_; lean_object* v_data_2317_; 
v_result_2313_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_fst_2290_);
v___x_2314_ = lean_box(v_result_2313_);
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
v___x_2316_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_2277_);
lean_inc_ref(v___x_2315_);
lean_inc(v_cls_2275_);
v_data_2317_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2317_, 0, v_cls_2275_);
lean_ctor_set(v_data_2317_, 1, v___x_2315_);
lean_ctor_set(v_data_2317_, 2, v_tag_2277_);
lean_ctor_set_float(v_data_2317_, sizeof(void*)*3, v___x_2316_);
lean_ctor_set_float(v_data_2317_, sizeof(void*)*3 + 8, v___x_2316_);
lean_ctor_set_uint8(v_data_2317_, sizeof(void*)*3 + 16, v_collapsed_2276_);
if (v___x_2309_ == 0)
{
lean_dec_ref_known(v___x_2315_, 1);
lean_dec(v_snd_2307_);
lean_dec(v_fst_2306_);
lean_dec_ref(v_tag_2277_);
lean_dec(v_cls_2275_);
v___y_2293_ = v_a_2312_;
v___y_2294_ = v___y_2311_;
v_data_2295_ = v_data_2317_;
goto v___jp_2292_;
}
else
{
lean_object* v_data_2318_; double v___x_2319_; double v___x_2320_; 
lean_dec_ref_known(v_data_2317_, 3);
v_data_2318_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2318_, 0, v_cls_2275_);
lean_ctor_set(v_data_2318_, 1, v___x_2315_);
lean_ctor_set(v_data_2318_, 2, v_tag_2277_);
v___x_2319_ = lean_unbox_float(v_fst_2306_);
lean_dec(v_fst_2306_);
lean_ctor_set_float(v_data_2318_, sizeof(void*)*3, v___x_2319_);
v___x_2320_ = lean_unbox_float(v_snd_2307_);
lean_dec(v_snd_2307_);
lean_ctor_set_float(v_data_2318_, sizeof(void*)*3 + 8, v___x_2320_);
lean_ctor_set_uint8(v_data_2318_, sizeof(void*)*3 + 16, v_collapsed_2276_);
v___y_2293_ = v_a_2312_;
v___y_2294_ = v___y_2311_;
v_data_2295_ = v_data_2318_;
goto v___jp_2292_;
}
}
v___jp_2321_:
{
lean_object* v_ref_2322_; lean_object* v___x_2323_; 
v_ref_2322_ = lean_ctor_get(v___y_2287_, 2);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2287_);
lean_inc(v___y_2286_);
lean_inc_ref(v___y_2285_);
lean_inc(v___y_2284_);
lean_inc_ref(v___y_2283_);
lean_inc(v_fst_2290_);
v___x_2323_ = lean_apply_8(v_msg_2281_, v_fst_2290_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, lean_box(0));
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___y_2311_ = v_ref_2322_;
v_a_2312_ = v_a_2324_;
goto v___jp_2310_;
}
else
{
lean_object* v___x_2325_; 
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1);
v___y_2311_ = v_ref_2322_;
v_a_2312_ = v___x_2325_;
goto v___jp_2310_;
}
}
v___jp_2326_:
{
if (v_clsEnabled_2279_ == 0)
{
if (v___y_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v_traceState_2329_; lean_object* v_env_2330_; lean_object* v_nextMacroScope_2331_; lean_object* v_ngen_2332_; lean_object* v_auxDeclNGen_2333_; lean_object* v_cache_2334_; lean_object* v_recordedDeps_2335_; lean_object* v_messages_2336_; lean_object* v_infoState_2337_; lean_object* v_snapshotTasks_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_snd_2307_);
lean_dec(v_fst_2306_);
lean_dec_ref(v_msg_2281_);
lean_dec_ref(v_tag_2277_);
lean_dec(v_cls_2275_);
v___x_2328_ = lean_st_ref_take(v___y_2288_);
v_traceState_2329_ = lean_ctor_get(v___x_2328_, 4);
v_env_2330_ = lean_ctor_get(v___x_2328_, 0);
v_nextMacroScope_2331_ = lean_ctor_get(v___x_2328_, 1);
v_ngen_2332_ = lean_ctor_get(v___x_2328_, 2);
v_auxDeclNGen_2333_ = lean_ctor_get(v___x_2328_, 3);
v_cache_2334_ = lean_ctor_get(v___x_2328_, 5);
v_recordedDeps_2335_ = lean_ctor_get(v___x_2328_, 6);
v_messages_2336_ = lean_ctor_get(v___x_2328_, 7);
v_infoState_2337_ = lean_ctor_get(v___x_2328_, 8);
v_snapshotTasks_2338_ = lean_ctor_get(v___x_2328_, 9);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2340_ = v___x_2328_;
v_isShared_2341_ = v_isSharedCheck_2357_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_snapshotTasks_2338_);
lean_inc(v_infoState_2337_);
lean_inc(v_messages_2336_);
lean_inc(v_recordedDeps_2335_);
lean_inc(v_cache_2334_);
lean_inc(v_traceState_2329_);
lean_inc(v_auxDeclNGen_2333_);
lean_inc(v_ngen_2332_);
lean_inc(v_nextMacroScope_2331_);
lean_inc(v_env_2330_);
lean_dec(v___x_2328_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2357_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
uint64_t v_tid_2342_; lean_object* v_traces_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2356_; 
v_tid_2342_ = lean_ctor_get_uint64(v_traceState_2329_, sizeof(void*)*1);
v_traces_2343_ = lean_ctor_get(v_traceState_2329_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_traceState_2329_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2345_ = v_traceState_2329_;
v_isShared_2346_ = v_isSharedCheck_2356_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_traces_2343_);
lean_dec(v_traceState_2329_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2356_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2347_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2280_, v_traces_2343_);
lean_dec_ref(v_traces_2343_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2347_);
v___x_2349_ = v___x_2345_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2347_);
lean_ctor_set_uint64(v_reuseFailAlloc_2355_, sizeof(void*)*1, v_tid_2342_);
v___x_2349_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 4, v___x_2349_);
v___x_2351_ = v___x_2340_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_env_2330_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_nextMacroScope_2331_);
lean_ctor_set(v_reuseFailAlloc_2354_, 2, v_ngen_2332_);
lean_ctor_set(v_reuseFailAlloc_2354_, 3, v_auxDeclNGen_2333_);
lean_ctor_set(v_reuseFailAlloc_2354_, 4, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2354_, 5, v_cache_2334_);
lean_ctor_set(v_reuseFailAlloc_2354_, 6, v_recordedDeps_2335_);
lean_ctor_set(v_reuseFailAlloc_2354_, 7, v_messages_2336_);
lean_ctor_set(v_reuseFailAlloc_2354_, 8, v_infoState_2337_);
lean_ctor_set(v_reuseFailAlloc_2354_, 9, v_snapshotTasks_2338_);
v___x_2351_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_st_ref_put(v___y_2288_, v___x_2351_);
v___x_2353_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_fst_2290_);
return v___x_2353_;
}
}
}
}
}
else
{
goto v___jp_2321_;
}
}
else
{
goto v___jp_2321_;
}
}
v___jp_2358_:
{
double v___x_2360_; double v___x_2361_; double v___x_2362_; uint8_t v___x_2363_; 
v___x_2360_ = lean_unbox_float(v_snd_2307_);
v___x_2361_ = lean_unbox_float(v_fst_2306_);
v___x_2362_ = lean_float_sub(v___x_2360_, v___x_2361_);
v___x_2363_ = lean_float_decLt(v___y_2359_, v___x_2362_);
v___y_2327_ = v___x_2363_;
goto v___jp_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___boxed(lean_object* v_cls_2374_, lean_object* v_collapsed_2375_, lean_object* v_tag_2376_, lean_object* v_opts_2377_, lean_object* v_clsEnabled_2378_, lean_object* v_oldTraces_2379_, lean_object* v_msg_2380_, lean_object* v_resStartStop_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
uint8_t v_collapsed_boxed_2389_; uint8_t v_clsEnabled_boxed_2390_; lean_object* v_res_2391_; 
v_collapsed_boxed_2389_ = lean_unbox(v_collapsed_2375_);
v_clsEnabled_boxed_2390_ = lean_unbox(v_clsEnabled_2378_);
v_res_2391_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v_cls_2374_, v_collapsed_boxed_2389_, v_tag_2376_, v_opts_2377_, v_clsEnabled_boxed_2390_, v_oldTraces_2379_, v_msg_2380_, v_resStartStop_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v_opts_2377_);
return v_res_2391_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = lean_box(0);
v___x_2393_ = lean_unsigned_to_nat(16u);
v___x_2394_ = lean_mk_array(v___x_2393_, v___x_2392_);
return v___x_2394_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0);
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set(v___x_2397_, 1, v___x_2395_);
return v___x_2397_;
}
}
static double _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2(void){
_start:
{
lean_object* v___x_2398_; double v___x_2399_; 
v___x_2398_ = lean_unsigned_to_nat(1000000000u);
v___x_2399_ = lean_float_of_nat(v___x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(lean_object* v_className_2400_, lean_object* v_type_2401_, lean_object* v_extraDeps_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_toCold_2410_; lean_object* v_options_2411_; lean_object* v_inheritedTraceOptions_2412_; uint8_t v_hasTrace_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_toCold_2410_ = lean_ctor_get(v_a_2407_, 0);
v_options_2411_ = lean_ctor_get(v_toCold_2410_, 2);
v_inheritedTraceOptions_2412_ = lean_ctor_get(v_toCold_2410_, 11);
v_hasTrace_2413_ = lean_ctor_get_uint8(v_options_2411_, sizeof(void*)*1);
v___x_2414_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v___x_2415_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1);
v___x_2416_ = lean_box(0);
lean_inc_ref(v_type_2401_);
v___x_2417_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v___x_2415_, v_type_2401_, v___x_2416_);
if (v_hasTrace_2413_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2400_, v_extraDeps_2402_, v___x_2414_, v___x_2417_, v_type_2401_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v___x_2418_;
}
else
{
lean_object* v___f_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v_a_2427_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v_a_2442_; 
lean_inc_ref(v_type_2401_);
lean_inc(v_className_2400_);
v___f_2419_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2419_, 0, v_className_2400_);
lean_closure_set(v___f_2419_, 1, v_type_2401_);
v___x_2420_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_2422_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2423_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2412_, v_options_2411_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2492_ = l_Lean_trace_profiler;
v___x_2493_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_2411_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref(v___f_2419_);
v___x_2494_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2400_, v_extraDeps_2402_, v___x_2414_, v___x_2417_, v_type_2401_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v___x_2494_;
}
else
{
goto v___jp_2451_;
}
}
else
{
goto v___jp_2451_;
}
v___jp_2424_:
{
lean_object* v___x_2428_; double v___x_2429_; double v___x_2430_; double v___x_2431_; double v___x_2432_; double v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2428_ = lean_io_mono_nanos_now();
v___x_2429_ = lean_float_of_nat(v___y_2426_);
v___x_2430_ = lean_float_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2);
v___x_2431_ = lean_float_div(v___x_2429_, v___x_2430_);
v___x_2432_ = lean_float_of_nat(v___x_2428_);
v___x_2433_ = lean_float_div(v___x_2432_, v___x_2430_);
v___x_2434_ = lean_box_float(v___x_2431_);
v___x_2435_ = lean_box_float(v___x_2433_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2437_, 0, v_a_2427_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_2420_, v_hasTrace_2413_, v___x_2421_, v_options_2411_, v___x_2423_, v___y_2425_, v___f_2419_, v___x_2437_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v___x_2438_;
}
v___jp_2439_:
{
lean_object* v___x_2443_; double v___x_2444_; double v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2443_ = lean_io_get_num_heartbeats();
v___x_2444_ = lean_float_of_nat(v___y_2440_);
v___x_2445_ = lean_float_of_nat(v___x_2443_);
v___x_2446_ = lean_box_float(v___x_2444_);
v___x_2447_ = lean_box_float(v___x_2445_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v_a_2442_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_2420_, v_hasTrace_2413_, v___x_2421_, v_options_2411_, v___x_2423_, v___y_2441_, v___f_2419_, v___x_2449_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v___x_2450_;
}
v___jp_2451_:
{
lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2452_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v_a_2408_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v___x_2454_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2455_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_2411_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_io_mono_nanos_now();
v___x_2457_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2400_, v_extraDeps_2402_, v___x_2414_, v___x_2417_, v_type_2401_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 1);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
v___y_2425_ = v_a_2453_;
v___y_2426_ = v___x_2456_;
v_a_2427_ = v___x_2463_;
goto v___jp_2424_;
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_a_2466_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2457_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2457_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set_tag(v___x_2468_, 0);
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
v___y_2425_ = v_a_2453_;
v___y_2426_ = v___x_2456_;
v_a_2427_ = v___x_2471_;
goto v___jp_2424_;
}
}
}
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_io_get_num_heartbeats();
v___x_2475_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2400_, v_extraDeps_2402_, v___x_2414_, v___x_2417_, v_type_2401_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 1);
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
v___y_2440_ = v___x_2474_;
v___y_2441_ = v_a_2453_;
v_a_2442_ = v___x_2481_;
goto v___jp_2439_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_a_2484_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2475_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2475_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 0);
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
v___y_2440_ = v___x_2474_;
v___y_2441_ = v_a_2453_;
v_a_2442_ = v___x_2489_;
goto v___jp_2439_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed(lean_object* v_className_2495_, lean_object* v_type_2496_, lean_object* v_extraDeps_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(v_className_2495_, v_type_2496_, v_extraDeps_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(lean_object* v_00_u03b1_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_x_2507_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(v_00_u03b1_2516_, v_x_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(lean_object* v_oldTraces_2526_, lean_object* v_data_2527_, lean_object* v_ref_2528_, lean_object* v_msg_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2526_, v_data_2527_, v_ref_2528_, v_msg_2529_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___boxed(lean_object* v_oldTraces_2538_, lean_object* v_data_2539_, lean_object* v_ref_2540_, lean_object* v_msg_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(v_oldTraces_2538_, v_data_2539_, v_ref_2540_, v_msg_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2549_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
v___x_2556_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
lean_ctor_set(v___x_2556_, 2, v___x_2555_);
lean_ctor_set(v___x_2556_, 3, v___x_2555_);
lean_ctor_set(v___x_2556_, 4, v___x_2555_);
lean_ctor_set(v___x_2556_, 5, v___x_2555_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(lean_object* v_env_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; lean_object* v_nextMacroScope_2562_; lean_object* v_ngen_2563_; lean_object* v_auxDeclNGen_2564_; lean_object* v_traceState_2565_; lean_object* v_recordedDeps_2566_; lean_object* v_messages_2567_; lean_object* v_infoState_2568_; lean_object* v_snapshotTasks_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2595_; 
v___x_2561_ = lean_st_ref_take(v___y_2559_);
v_nextMacroScope_2562_ = lean_ctor_get(v___x_2561_, 1);
v_ngen_2563_ = lean_ctor_get(v___x_2561_, 2);
v_auxDeclNGen_2564_ = lean_ctor_get(v___x_2561_, 3);
v_traceState_2565_ = lean_ctor_get(v___x_2561_, 4);
v_recordedDeps_2566_ = lean_ctor_get(v___x_2561_, 6);
v_messages_2567_ = lean_ctor_get(v___x_2561_, 7);
v_infoState_2568_ = lean_ctor_get(v___x_2561_, 8);
v_snapshotTasks_2569_ = lean_ctor_get(v___x_2561_, 9);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; lean_object* v_unused_2597_; 
v_unused_2596_ = lean_ctor_get(v___x_2561_, 5);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v___x_2561_, 0);
lean_dec(v_unused_2597_);
v___x_2571_ = v___x_2561_;
v_isShared_2572_ = v_isSharedCheck_2595_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_snapshotTasks_2569_);
lean_inc(v_infoState_2568_);
lean_inc(v_messages_2567_);
lean_inc(v_recordedDeps_2566_);
lean_inc(v_traceState_2565_);
lean_inc(v_auxDeclNGen_2564_);
lean_inc(v_ngen_2563_);
lean_inc(v_nextMacroScope_2562_);
lean_dec(v___x_2561_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2595_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 5, v___x_2573_);
lean_ctor_set(v___x_2571_, 0, v_env_2557_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_env_2557_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_nextMacroScope_2562_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v_ngen_2563_);
lean_ctor_set(v_reuseFailAlloc_2594_, 3, v_auxDeclNGen_2564_);
lean_ctor_set(v_reuseFailAlloc_2594_, 4, v_traceState_2565_);
lean_ctor_set(v_reuseFailAlloc_2594_, 5, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2594_, 6, v_recordedDeps_2566_);
lean_ctor_set(v_reuseFailAlloc_2594_, 7, v_messages_2567_);
lean_ctor_set(v_reuseFailAlloc_2594_, 8, v_infoState_2568_);
lean_ctor_set(v_reuseFailAlloc_2594_, 9, v_snapshotTasks_2569_);
v___x_2575_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v_mctx_2578_; lean_object* v_zetaDeltaFVarIds_2579_; lean_object* v_postponed_2580_; lean_object* v_diag_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2592_; 
v___x_2576_ = lean_st_ref_put(v___y_2559_, v___x_2575_);
v___x_2577_ = lean_st_ref_take(v___y_2558_);
v_mctx_2578_ = lean_ctor_get(v___x_2577_, 0);
v_zetaDeltaFVarIds_2579_ = lean_ctor_get(v___x_2577_, 2);
v_postponed_2580_ = lean_ctor_get(v___x_2577_, 3);
v_diag_2581_ = lean_ctor_get(v___x_2577_, 4);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2592_ == 0)
{
lean_object* v_unused_2593_; 
v_unused_2593_ = lean_ctor_get(v___x_2577_, 1);
lean_dec(v_unused_2593_);
v___x_2583_ = v___x_2577_;
v_isShared_2584_ = v_isSharedCheck_2592_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_diag_2581_);
lean_inc(v_postponed_2580_);
lean_inc(v_zetaDeltaFVarIds_2579_);
lean_inc(v_mctx_2578_);
lean_dec(v___x_2577_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2592_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2585_ = lean_box(0);
v___x_2586_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 1, v___x_2586_);
v___x_2588_ = v___x_2583_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_mctx_2578_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_zetaDeltaFVarIds_2579_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_postponed_2580_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_diag_2581_);
v___x_2588_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = lean_st_ref_put(v___y_2558_, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2585_);
return v___x_2590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___boxed(lean_object* v_env_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v_env_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec(v___y_2599_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(lean_object* v_env_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v_env_2603_, v___y_2607_, v___y_2609_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___boxed(lean_object* v_env_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(v_env_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2620_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0));
v___x_2623_ = l_Lean_stringToMessageData(v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(lean_object* v_mkCmd_2624_, lean_object* v_a_2625_, lean_object* v___x_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc(v___y_2630_);
lean_inc_ref(v___y_2629_);
lean_inc(v___y_2628_);
lean_inc_ref(v___y_2627_);
lean_inc_ref(v_a_2625_);
v___x_2634_ = lean_apply_5(v_mkCmd_2624_, v_a_2625_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
v___x_2635_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_2634_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v_a_2625_);
return v___x_2635_;
}
else
{
lean_object* v_a_2636_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; uint8_t v___y_2662_; uint8_t v___x_2686_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v___x_2686_ = l_Lean_Exception_isInterrupt(v_a_2636_);
if (v___x_2686_ == 0)
{
uint8_t v___x_2687_; 
lean_inc(v_a_2636_);
v___x_2687_ = l_Lean_Exception_isRuntime(v_a_2636_);
v___y_2662_ = v___x_2687_;
goto v___jp_2661_;
}
else
{
v___y_2662_ = v___x_2686_;
goto v___jp_2661_;
}
v___jp_2637_:
{
lean_object* v___x_2644_; 
lean_dec_ref(v___y_2638_);
v___x_2644_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v___x_2626_, v___y_2641_, v___y_2643_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v___x_2644_, 0);
lean_dec(v_unused_2652_);
v___x_2646_ = v___x_2644_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v___x_2644_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 1);
lean_ctor_set(v___x_2646_, 0, v_a_2636_);
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2636_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec(v_a_2636_);
v_a_2653_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2644_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2644_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
v___jp_2661_:
{
if (v___y_2662_ == 0)
{
lean_object* v_toCold_2663_; lean_object* v_options_2664_; uint8_t v_hasTrace_2665_; 
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v_toCold_2663_ = lean_ctor_get(v___y_2631_, 0);
v_options_2664_ = lean_ctor_get(v_toCold_2663_, 2);
v_hasTrace_2665_ = lean_ctor_get_uint8(v_options_2664_, sizeof(void*)*1);
if (v_hasTrace_2665_ == 0)
{
lean_dec_ref(v_a_2625_);
v___y_2638_ = v___y_2627_;
v___y_2639_ = v___y_2628_;
v___y_2640_ = v___y_2629_;
v___y_2641_ = v___y_2630_;
v___y_2642_ = v___y_2631_;
v___y_2643_ = v___y_2632_;
goto v___jp_2637_;
}
else
{
lean_object* v_inheritedTraceOptions_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v_inheritedTraceOptions_2666_ = lean_ctor_get(v_toCold_2663_, 11);
v___x_2667_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2668_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2666_, v_options_2664_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_dec_ref(v_a_2625_);
v___y_2638_ = v___y_2627_;
v___y_2639_ = v___y_2628_;
v___y_2640_ = v___y_2629_;
v___y_2641_ = v___y_2630_;
v___y_2642_ = v___y_2631_;
v___y_2643_ = v___y_2632_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1);
v___x_2671_ = l_Lean_MessageData_ofExpr(v_a_2625_);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
lean_inc(v_a_2636_);
v___x_2675_ = l_Lean_Exception_toMessageData(v_a_2636_);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v___x_2667_, v___x_2676_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_dec_ref_known(v___x_2677_, 1);
v___y_2638_ = v___y_2627_;
v___y_2639_ = v___y_2628_;
v___y_2640_ = v___y_2629_;
v___y_2641_ = v___y_2630_;
v___y_2642_ = v___y_2631_;
v___y_2643_ = v___y_2632_;
goto v___jp_2637_;
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_a_2636_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___x_2626_);
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
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
}
else
{
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v_a_2625_);
return v___x_2635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed(lean_object* v_mkCmd_2688_, lean_object* v_a_2689_, lean_object* v___x_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(v_mkCmd_2688_, v_a_2689_, v___x_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
return v_res_2698_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2701_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2702_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
lean_ctor_set(v___x_2704_, 2, v___x_2703_);
lean_ctor_set(v___x_2704_, 3, v___x_2703_);
lean_ctor_set(v___x_2704_, 4, v___x_2702_);
lean_ctor_set(v___x_2704_, 5, v___x_2702_);
lean_ctor_set(v___x_2704_, 6, v___x_2702_);
lean_ctor_set(v___x_2704_, 7, v___x_2702_);
lean_ctor_set(v___x_2704_, 8, v___x_2702_);
lean_ctor_set(v___x_2704_, 9, v___x_2702_);
lean_ctor_set(v___x_2704_, 10, v___x_2702_);
lean_ctor_set(v___x_2704_, 11, v___x_2701_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_unsigned_to_nat(32u);
v___x_2706_ = lean_mk_empty_array_with_capacity(v___x_2705_);
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3(void){
_start:
{
size_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2708_ = ((size_t)5ULL);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_unsigned_to_nat(32u);
v___x_2711_ = lean_mk_empty_array_with_capacity(v___x_2710_);
v___x_2712_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2);
v___x_2713_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___x_2711_);
lean_ctor_set(v___x_2713_, 2, v___x_2709_);
lean_ctor_set(v___x_2713_, 3, v___x_2709_);
lean_ctor_set_usize(v___x_2713_, 4, v___x_2708_);
return v___x_2713_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2714_ = lean_box(1);
v___x_2715_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3);
v___x_2716_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0);
v___x_2717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2715_);
lean_ctor_set(v___x_2717_, 2, v___x_2714_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(lean_object* v_msgData_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; lean_object* v_env_2722_; uint8_t v___x_2723_; lean_object* v_env_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v_scopes_2727_; lean_object* v___x_2728_; lean_object* v_opts_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2721_ = lean_st_ref_get(v___y_2719_);
v_env_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_ref(v_env_2722_);
lean_dec(v___x_2721_);
v___x_2723_ = 0;
v_env_2724_ = l_Lean_Environment_setRecordingDeps(v_env_2722_, v___x_2723_);
v___x_2725_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2726_ = lean_st_ref_get(v___y_2719_);
v_scopes_2727_ = lean_ctor_get(v___x_2726_, 2);
lean_inc(v_scopes_2727_);
lean_dec(v___x_2726_);
v___x_2728_ = l_List_head_x21___redArg(v___x_2725_, v_scopes_2727_);
lean_dec(v_scopes_2727_);
v_opts_2729_ = lean_ctor_get(v___x_2728_, 1);
lean_inc_ref(v_opts_2729_);
lean_dec(v___x_2728_);
v___x_2730_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
v___x_2731_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4);
v___x_2732_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2732_, 0, v_env_2724_);
lean_ctor_set(v___x_2732_, 1, v___x_2730_);
lean_ctor_set(v___x_2732_, 2, v___x_2731_);
lean_ctor_set(v___x_2732_, 3, v_opts_2729_);
v___x_2733_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_msgData_2718_);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msgData_2735_, v___y_2736_);
lean_dec(v___y_2736_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(lean_object* v_cls_2739_, lean_object* v_msg_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Elab_Command_getRef___redArg(v___y_2741_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2795_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msg_2740_, v___y_2742_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2795_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2795_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v_traceState_2752_; lean_object* v_env_2753_; lean_object* v_messages_2754_; lean_object* v_scopes_2755_; lean_object* v_usedQuotCtxts_2756_; lean_object* v_nextMacroScope_2757_; lean_object* v_maxRecDepth_2758_; lean_object* v_ngen_2759_; lean_object* v_auxDeclNGen_2760_; lean_object* v_infoState_2761_; lean_object* v_snapshotTasks_2762_; lean_object* v_prevLinterStates_2763_; lean_object* v_codeQualityEntryTasks_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2794_; 
v___x_2751_ = lean_st_ref_take(v___y_2742_);
v_traceState_2752_ = lean_ctor_get(v___x_2751_, 9);
v_env_2753_ = lean_ctor_get(v___x_2751_, 0);
v_messages_2754_ = lean_ctor_get(v___x_2751_, 1);
v_scopes_2755_ = lean_ctor_get(v___x_2751_, 2);
v_usedQuotCtxts_2756_ = lean_ctor_get(v___x_2751_, 3);
v_nextMacroScope_2757_ = lean_ctor_get(v___x_2751_, 4);
v_maxRecDepth_2758_ = lean_ctor_get(v___x_2751_, 5);
v_ngen_2759_ = lean_ctor_get(v___x_2751_, 6);
v_auxDeclNGen_2760_ = lean_ctor_get(v___x_2751_, 7);
v_infoState_2761_ = lean_ctor_get(v___x_2751_, 8);
v_snapshotTasks_2762_ = lean_ctor_get(v___x_2751_, 10);
v_prevLinterStates_2763_ = lean_ctor_get(v___x_2751_, 11);
v_codeQualityEntryTasks_2764_ = lean_ctor_get(v___x_2751_, 12);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2766_ = v___x_2751_;
v_isShared_2767_ = v_isSharedCheck_2794_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2764_);
lean_inc(v_prevLinterStates_2763_);
lean_inc(v_snapshotTasks_2762_);
lean_inc(v_traceState_2752_);
lean_inc(v_infoState_2761_);
lean_inc(v_auxDeclNGen_2760_);
lean_inc(v_ngen_2759_);
lean_inc(v_maxRecDepth_2758_);
lean_inc(v_nextMacroScope_2757_);
lean_inc(v_usedQuotCtxts_2756_);
lean_inc(v_scopes_2755_);
lean_inc(v_messages_2754_);
lean_inc(v_env_2753_);
lean_dec(v___x_2751_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2794_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint64_t v_tid_2768_; lean_object* v_traces_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2793_; 
v_tid_2768_ = lean_ctor_get_uint64(v_traceState_2752_, sizeof(void*)*1);
v_traces_2769_ = lean_ctor_get(v_traceState_2752_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_traceState_2752_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2771_ = v_traceState_2752_;
v_isShared_2772_ = v_isSharedCheck_2793_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_traces_2769_);
lean_dec(v_traceState_2752_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2793_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; double v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_box(0);
v___x_2775_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
v___x_2776_ = 0;
v___x_2777_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_2778_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2778_, 0, v_cls_2739_);
lean_ctor_set(v___x_2778_, 1, v___x_2774_);
lean_ctor_set(v___x_2778_, 2, v___x_2777_);
lean_ctor_set_float(v___x_2778_, sizeof(void*)*3, v___x_2775_);
lean_ctor_set_float(v___x_2778_, sizeof(void*)*3 + 8, v___x_2775_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*3 + 16, v___x_2776_);
v___x_2779_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1));
v___x_2780_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v_a_2747_);
lean_ctor_set(v___x_2780_, 2, v___x_2779_);
v___x_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2781_, 0, v_a_2745_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = l_Lean_PersistentArray_push___redArg(v_traces_2769_, v___x_2781_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2782_);
v___x_2784_ = v___x_2771_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2782_);
lean_ctor_set_uint64(v_reuseFailAlloc_2792_, sizeof(void*)*1, v_tid_2768_);
v___x_2784_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2786_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 9, v___x_2784_);
v___x_2786_ = v___x_2766_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_env_2753_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_messages_2754_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_scopes_2755_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_usedQuotCtxts_2756_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v_nextMacroScope_2757_);
lean_ctor_set(v_reuseFailAlloc_2791_, 5, v_maxRecDepth_2758_);
lean_ctor_set(v_reuseFailAlloc_2791_, 6, v_ngen_2759_);
lean_ctor_set(v_reuseFailAlloc_2791_, 7, v_auxDeclNGen_2760_);
lean_ctor_set(v_reuseFailAlloc_2791_, 8, v_infoState_2761_);
lean_ctor_set(v_reuseFailAlloc_2791_, 9, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2791_, 10, v_snapshotTasks_2762_);
lean_ctor_set(v_reuseFailAlloc_2791_, 11, v_prevLinterStates_2763_);
lean_ctor_set(v_reuseFailAlloc_2791_, 12, v_codeQualityEntryTasks_2764_);
v___x_2786_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2787_ = lean_st_ref_put(v___y_2742_, v___x_2786_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2773_);
v___x_2789_ = v___x_2749_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2773_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_msg_2740_);
lean_dec(v_cls_2739_);
v_a_2796_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2744_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2744_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1___boxed(lean_object* v_cls_2804_, lean_object* v_msg_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(v_cls_2804_, v_msg_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
return v_res_2809_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0));
v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
return v___x_2812_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2));
v___x_2815_ = l_Lean_stringToMessageData(v___x_2814_);
return v___x_2815_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4));
v___x_2818_ = l_Lean_stringToMessageData(v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(lean_object* v_mkCmd_2819_, lean_object* v___x_2820_, lean_object* v_className_2821_, lean_object* v_as_2822_, size_t v_sz_2823_, size_t v_i_2824_, lean_object* v_b_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_a_2830_; uint8_t v___x_2834_; 
v___x_2834_ = lean_usize_dec_lt(v_i_2824_, v_sz_2823_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
lean_dec(v_className_2821_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v_mkCmd_2819_);
v___x_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_b_2825_);
return v___x_2835_;
}
else
{
lean_object* v___x_2836_; lean_object* v_a_2837_; lean_object* v___f_2838_; lean_object* v___x_2839_; 
v___x_2836_ = lean_box(0);
v_a_2837_ = lean_array_uget_borrowed(v_as_2822_, v_i_2824_);
lean_inc_ref(v___x_2820_);
lean_inc(v_a_2837_);
lean_inc_ref(v_mkCmd_2819_);
v___f_2838_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2838_, 0, v_mkCmd_2819_);
lean_closure_set(v___f_2838_, 1, v_a_2837_);
lean_closure_set(v___f_2838_, 2, v___x_2820_);
v___x_2839_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2838_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = l_Lean_Elab_Command_elabCommand(v_a_2840_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v_scopes_2847_; lean_object* v___x_2848_; lean_object* v_opts_2849_; uint8_t v_hasTrace_2850_; 
lean_dec_ref_known(v___x_2841_, 1);
v___x_2842_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2843_ = l_Lean_inheritedTraceOptions;
v___x_2844_ = lean_st_ref_get(v___x_2843_);
v___x_2845_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2846_ = lean_st_ref_get(v___y_2827_);
v_scopes_2847_ = lean_ctor_get(v___x_2846_, 2);
lean_inc(v_scopes_2847_);
lean_dec(v___x_2846_);
v___x_2848_ = l_List_head_x21___redArg(v___x_2845_, v_scopes_2847_);
lean_dec(v_scopes_2847_);
v_opts_2849_ = lean_ctor_get(v___x_2848_, 1);
lean_inc_ref(v_opts_2849_);
lean_dec(v___x_2848_);
v_hasTrace_2850_ = lean_ctor_get_uint8(v_opts_2849_, sizeof(void*)*1);
if (v_hasTrace_2850_ == 0)
{
lean_dec_ref(v_opts_2849_);
lean_dec(v___x_2844_);
v_a_2830_ = v___x_2836_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2851_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2852_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2844_, v_opts_2849_, v___x_2851_);
lean_dec_ref(v_opts_2849_);
lean_dec(v___x_2844_);
if (v___x_2852_ == 0)
{
v_a_2830_ = v___x_2836_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1);
v___x_2854_ = 0;
lean_inc(v_className_2821_);
v___x_2855_ = l_Lean_MessageData_ofConstName(v_className_2821_, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2853_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3);
v___x_2858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
lean_inc(v_a_2837_);
v___x_2859_ = l_Lean_MessageData_ofExpr(v_a_2837_);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(v___x_2842_, v___x_2862_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_dec_ref_known(v___x_2863_, 1);
v_a_2830_ = v___x_2836_;
goto v___jp_2829_;
}
else
{
lean_dec(v_className_2821_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v_mkCmd_2819_);
return v___x_2863_;
}
}
}
}
else
{
lean_dec(v_className_2821_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v_mkCmd_2819_);
return v___x_2841_;
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_className_2821_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v_mkCmd_2819_);
v_a_2864_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2839_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2839_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
v___jp_2829_:
{
size_t v___x_2831_; size_t v___x_2832_; 
v___x_2831_ = ((size_t)1ULL);
v___x_2832_ = lean_usize_add(v_i_2824_, v___x_2831_);
v_i_2824_ = v___x_2832_;
v_b_2825_ = v_a_2830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___boxed(lean_object* v_mkCmd_2872_, lean_object* v___x_2873_, lean_object* v_className_2874_, lean_object* v_as_2875_, lean_object* v_sz_2876_, lean_object* v_i_2877_, lean_object* v_b_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
size_t v_sz_boxed_2882_; size_t v_i_boxed_2883_; lean_object* v_res_2884_; 
v_sz_boxed_2882_ = lean_unbox_usize(v_sz_2876_);
lean_dec(v_sz_2876_);
v_i_boxed_2883_ = lean_unbox_usize(v_i_2877_);
lean_dec(v_i_2877_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(v_mkCmd_2872_, v___x_2873_, v_className_2874_, v_as_2875_, v_sz_boxed_2882_, v_i_boxed_2883_, v_b_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_as_2875_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_withClassInstDeps(lean_object* v_className_2885_, lean_object* v_type_2886_, lean_object* v_extraDeps_2887_, lean_object* v_mkCmd_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
lean_inc(v_className_2885_);
v___x_2892_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed), 10, 3);
lean_closure_set(v___x_2892_, 0, v_className_2885_);
lean_closure_set(v___x_2892_, 1, v_type_2886_);
lean_closure_set(v___x_2892_, 2, v_extraDeps_2887_);
v___x_2893_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2892_, v_a_2889_, v_a_2890_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v_env_2896_; lean_object* v___x_2897_; size_t v_sz_2898_; size_t v___x_2899_; lean_object* v___x_2900_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = lean_st_ref_get(v_a_2890_);
v_env_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc_ref(v_env_2896_);
lean_dec(v___x_2895_);
v___x_2897_ = lean_box(0);
v_sz_2898_ = lean_array_size(v_a_2894_);
v___x_2899_ = ((size_t)0ULL);
v___x_2900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(v_mkCmd_2888_, v_env_2896_, v_className_2885_, v_a_2894_, v_sz_2898_, v___x_2899_, v___x_2897_, v_a_2889_, v_a_2890_);
lean_dec(v_a_2894_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v___x_2900_, 0);
lean_dec(v_unused_2908_);
v___x_2902_ = v___x_2900_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_dec(v___x_2900_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2897_);
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2897_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
return v___x_2900_;
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec_ref(v_mkCmd_2888_);
lean_dec(v_className_2885_);
v_a_2909_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2893_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2893_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_withClassInstDeps___boxed(lean_object* v_className_2917_, lean_object* v_type_2918_, lean_object* v_extraDeps_2919_, lean_object* v_mkCmd_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Elab_ConfigEval_withClassInstDeps(v_className_2917_, v_type_2918_, v_extraDeps_2919_, v_mkCmd_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(lean_object* v_msgData_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msgData_2925_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___boxed(lean_object* v_msgData_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(v_msgData_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3000_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_3001_ = 0;
v___x_3002_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_));
v___x_3003_ = l_Lean_registerTraceClass(v___x_3000_, v___x_3001_, v___x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2____boxed(lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_();
return v_res_3005_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_Util(builtin);
}
#ifdef __cplusplus
}
#endif
