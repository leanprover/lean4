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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5;
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
v_ref_27_ = lean_ctor_get(v___y_16_, 5);
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
v_ref_97_ = lean_ctor_get(v_a_75_, 5);
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
lean_object* v_options_382_; uint8_t v_hasTrace_383_; 
v_options_382_ = lean_ctor_get(v___y_379_, 2);
v_hasTrace_383_ = lean_ctor_get_uint8(v_options_382_, sizeof(void*)*1);
if (v_hasTrace_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_cls_374_);
v___x_384_ = lean_box(v_hasTrace_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v_inheritedTraceOptions_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_inheritedTraceOptions_386_ = lean_ctor_get(v___y_379_, 13);
v___x_387_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1));
v___x_388_ = l_Lean_Name_append(v___x_387_, v_cls_374_);
v___x_389_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_386_, v_options_382_, v___x_388_);
lean_dec(v___x_388_);
v___x_390_ = lean_box(v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___boxed(lean_object* v_cls_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(lean_object* v_as_404_, size_t v_sz_405_, size_t v_i_406_, lean_object* v_b_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = lean_usize_dec_lt(v_i_406_, v_sz_405_);
if (v___x_408_ == 0)
{
lean_inc_ref(v_b_407_);
return v_b_407_;
}
else
{
lean_object* v___x_409_; lean_object* v_a_410_; uint8_t v___x_411_; 
v___x_409_ = lean_box(0);
v_a_410_ = lean_array_uget_borrowed(v_as_404_, v_i_406_);
v___x_411_ = l_Lean_Expr_hasMVar(v_a_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; 
v___x_412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_406_, v___x_413_);
v_i_406_ = v___x_414_;
v_b_407_ = v___x_412_;
goto _start;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_inc(v_a_410_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_a_410_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_409_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___boxed(lean_object* v_as_419_, lean_object* v_sz_420_, lean_object* v_i_421_, lean_object* v_b_422_){
_start:
{
size_t v_sz_boxed_423_; size_t v_i_boxed_424_; lean_object* v_res_425_; 
v_sz_boxed_423_ = lean_unbox_usize(v_sz_420_);
lean_dec(v_sz_420_);
v_i_boxed_424_ = lean_unbox_usize(v_i_421_);
lean_dec(v_i_421_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(v_as_419_, v_sz_boxed_423_, v_i_boxed_424_, v_b_422_);
lean_dec_ref(v_b_422_);
lean_dec_ref(v_as_419_);
return v_res_425_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(lean_object* v_a_426_, lean_object* v_as_427_, size_t v_i_428_, size_t v_stop_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_eq(v_i_428_, v_stop_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_array_uget_borrowed(v_as_427_, v_i_428_);
v___x_432_ = lean_expr_eqv(v_a_426_, v___x_431_);
if (v___x_432_ == 0)
{
size_t v___x_433_; size_t v___x_434_; 
v___x_433_ = ((size_t)1ULL);
v___x_434_ = lean_usize_add(v_i_428_, v___x_433_);
v_i_428_ = v___x_434_;
goto _start;
}
else
{
return v___x_432_;
}
}
else
{
uint8_t v___x_436_; 
v___x_436_ = 0;
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0___boxed(lean_object* v_a_437_, lean_object* v_as_438_, lean_object* v_i_439_, lean_object* v_stop_440_){
_start:
{
size_t v_i_boxed_441_; size_t v_stop_boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v_i_boxed_441_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_stop_boxed_442_ = lean_unbox_usize(v_stop_440_);
lean_dec(v_stop_440_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(v_a_437_, v_as_438_, v_i_boxed_441_, v_stop_boxed_442_);
lean_dec_ref(v_as_438_);
lean_dec_ref(v_a_437_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(lean_object* v_as_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_array_get_size(v_as_445_);
v___x_449_ = lean_nat_dec_lt(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
return v___x_449_;
}
else
{
if (v___x_449_ == 0)
{
return v___x_449_;
}
else
{
size_t v___x_450_; size_t v___x_451_; uint8_t v___x_452_; 
v___x_450_ = ((size_t)0ULL);
v___x_451_ = lean_usize_of_nat(v___x_448_);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0_spec__0(v_a_446_, v_as_445_, v___x_450_, v___x_451_);
return v___x_452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0___boxed(lean_object* v_as_453_, lean_object* v_a_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_as_453_, v_a_454_);
lean_dec_ref(v_a_454_);
lean_dec_ref(v_as_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(lean_object* v_plan_457_, lean_object* v_as_458_, size_t v_i_459_, size_t v_stop_460_, lean_object* v_b_461_){
_start:
{
lean_object* v___y_463_; uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_eq(v_i_459_, v_stop_460_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_array_uget_borrowed(v_as_458_, v_i_459_);
v___x_469_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_plan_457_, v___x_468_);
v___x_470_ = lean_bool_not(v___x_469_);
if (v___x_470_ == 0)
{
v___y_463_ = v_b_461_;
goto v___jp_462_;
}
else
{
lean_object* v___x_471_; 
lean_inc(v___x_468_);
v___x_471_ = lean_array_push(v_b_461_, v___x_468_);
v___y_463_ = v___x_471_;
goto v___jp_462_;
}
}
else
{
return v_b_461_;
}
v___jp_462_:
{
size_t v___x_464_; size_t v___x_465_; 
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_add(v_i_459_, v___x_464_);
v_i_459_ = v___x_465_;
v_b_461_ = v___y_463_;
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
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_nbuckets_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_578_ = lean_array_get_size(v_data_577_);
v___x_579_ = lean_unsigned_to_nat(2u);
v_nbuckets_580_ = lean_nat_mul(v___x_578_, v___x_579_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_box(0);
v___x_583_ = lean_mk_array(v_nbuckets_580_, v___x_582_);
v___x_584_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(v___x_581_, v_data_577_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(lean_object* v_m_585_, lean_object* v_a_586_, lean_object* v_b_587_){
_start:
{
lean_object* v_size_588_; lean_object* v_buckets_589_; lean_object* v___x_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v_fold_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; lean_object* v_bkt_603_; uint8_t v___x_604_; 
v_size_588_ = lean_ctor_get(v_m_585_, 0);
v_buckets_589_ = lean_ctor_get(v_m_585_, 1);
v___x_590_ = lean_array_get_size(v_buckets_589_);
v___x_591_ = l_Lean_Expr_hash(v_a_586_);
v___x_592_ = 32ULL;
v___x_593_ = lean_uint64_shift_right(v___x_591_, v___x_592_);
v_fold_594_ = lean_uint64_xor(v___x_591_, v___x_593_);
v___x_595_ = 16ULL;
v___x_596_ = lean_uint64_shift_right(v_fold_594_, v___x_595_);
v___x_597_ = lean_uint64_xor(v_fold_594_, v___x_596_);
v___x_598_ = lean_uint64_to_usize(v___x_597_);
v___x_599_ = lean_usize_of_nat(v___x_590_);
v___x_600_ = ((size_t)1ULL);
v___x_601_ = lean_usize_sub(v___x_599_, v___x_600_);
v___x_602_ = lean_usize_land(v___x_598_, v___x_601_);
v_bkt_603_ = lean_array_uget_borrowed(v_buckets_589_, v___x_602_);
v___x_604_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_586_, v_bkt_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_625_; 
lean_inc_ref(v_buckets_589_);
lean_inc(v_size_588_);
v_isSharedCheck_625_ = !lean_is_exclusive(v_m_585_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; lean_object* v_unused_627_; 
v_unused_626_ = lean_ctor_get(v_m_585_, 1);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v_m_585_, 0);
lean_dec(v_unused_627_);
v___x_606_ = v_m_585_;
v_isShared_607_ = v_isSharedCheck_625_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_m_585_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_625_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v_size_x27_609_; lean_object* v___x_610_; lean_object* v_buckets_x27_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v_size_x27_609_ = lean_nat_add(v_size_588_, v___x_608_);
lean_dec(v_size_588_);
lean_inc(v_bkt_603_);
v___x_610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_610_, 0, v_a_586_);
lean_ctor_set(v___x_610_, 1, v_b_587_);
lean_ctor_set(v___x_610_, 2, v_bkt_603_);
v_buckets_x27_611_ = lean_array_uset(v_buckets_589_, v___x_602_, v___x_610_);
v___x_612_ = lean_unsigned_to_nat(4u);
v___x_613_ = lean_nat_mul(v_size_x27_609_, v___x_612_);
v___x_614_ = lean_unsigned_to_nat(3u);
v___x_615_ = lean_nat_div(v___x_613_, v___x_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_array_get_size(v_buckets_x27_611_);
v___x_617_ = lean_nat_dec_le(v___x_615_, v___x_616_);
lean_dec(v___x_615_);
if (v___x_617_ == 0)
{
lean_object* v_val_618_; lean_object* v___x_620_; 
v_val_618_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(v_buckets_x27_611_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_val_618_);
lean_ctor_set(v___x_606_, 0, v_size_x27_609_);
v___x_620_ = v___x_606_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_size_x27_609_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_val_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
else
{
lean_object* v___x_623_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_buckets_x27_611_);
lean_ctor_set(v___x_606_, 0, v_size_x27_609_);
v___x_623_ = v___x_606_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_size_x27_609_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_buckets_x27_611_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_dec(v_b_587_);
lean_dec_ref(v_a_586_);
return v_m_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(lean_object* v_e_628_, lean_object* v___y_629_){
_start:
{
uint8_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = l_Lean_Expr_hasMVar(v_e_628_);
v___x_632_ = lean_bool_not(v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v_mctx_634_; lean_object* v___x_635_; lean_object* v_fst_636_; lean_object* v_snd_637_; lean_object* v___x_638_; lean_object* v_cache_639_; lean_object* v_zetaDeltaFVarIds_640_; lean_object* v_postponed_641_; lean_object* v_diag_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_651_; 
v___x_633_ = lean_st_ref_get(v___y_629_);
v_mctx_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_mctx_634_);
lean_dec(v___x_633_);
v___x_635_ = l_Lean_instantiateMVarsCore(v_mctx_634_, v_e_628_);
v_fst_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_fst_636_);
v_snd_637_ = lean_ctor_get(v___x_635_, 1);
lean_inc(v_snd_637_);
lean_dec_ref(v___x_635_);
v___x_638_ = lean_st_ref_take(v___y_629_);
v_cache_639_ = lean_ctor_get(v___x_638_, 1);
v_zetaDeltaFVarIds_640_ = lean_ctor_get(v___x_638_, 2);
v_postponed_641_ = lean_ctor_get(v___x_638_, 3);
v_diag_642_ = lean_ctor_get(v___x_638_, 4);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_638_, 0);
lean_dec(v_unused_652_);
v___x_644_ = v___x_638_;
v_isShared_645_ = v_isSharedCheck_651_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_diag_642_);
lean_inc(v_postponed_641_);
lean_inc(v_zetaDeltaFVarIds_640_);
lean_inc(v_cache_639_);
lean_dec(v___x_638_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_651_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_snd_637_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_snd_637_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_cache_639_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_zetaDeltaFVarIds_640_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_postponed_641_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_diag_642_);
v___x_647_ = v_reuseFailAlloc_650_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_st_ref_set(v___y_629_, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v_fst_636_);
return v___x_649_;
}
}
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_e_628_);
return v___x_653_;
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
lean_object* v_v_670_; lean_object* v___x_671_; 
v_v_670_ = lean_array_uget_borrowed(v_bs_660_, v_i_659_);
lean_inc(v_v_670_);
v___x_671_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_v_670_, v___y_664_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v_bs_x27_674_; size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = lean_unsigned_to_nat(0u);
v_bs_x27_674_ = lean_array_uset(v_bs_660_, v_i_659_, v___x_673_);
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_add(v_i_659_, v___x_675_);
v___x_677_ = lean_array_uset(v_bs_x27_674_, v_i_659_, v_a_672_);
v_i_659_ = v___x_676_;
v_bs_660_ = v___x_677_;
goto _start;
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_bs_660_);
v_a_679_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_671_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_671_);
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
lean_object* v_options_756_; lean_object* v___x_757_; uint8_t v___x_758_; uint8_t v___x_759_; 
v_options_756_ = lean_ctor_get(v___y_754_, 2);
v___x_757_ = l_Lean_Elab_pp_macroStack;
v___x_758_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_756_, v___x_757_);
v___x_759_ = lean_bool_not(v___x_758_);
if (v___x_759_ == 0)
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
else
{
lean_object* v___x_779_; 
lean_dec(v_macroStack_753_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_msgData_752_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___boxed(lean_object* v_msgData_780_, lean_object* v_macroStack_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_msgData_780_, v_macroStack_781_, v___y_782_);
lean_dec_ref(v___y_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(lean_object* v_msgData_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; lean_object* v_env_792_; lean_object* v___x_793_; lean_object* v_mctx_794_; lean_object* v_lctx_795_; lean_object* v_options_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_791_ = lean_st_ref_get(v___y_789_);
v_env_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc_ref(v_env_792_);
lean_dec(v___x_791_);
v___x_793_ = lean_st_ref_get(v___y_787_);
v_mctx_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc_ref(v_mctx_794_);
lean_dec(v___x_793_);
v_lctx_795_ = lean_ctor_get(v___y_786_, 2);
v_options_796_ = lean_ctor_get(v___y_788_, 2);
lean_inc_ref(v_options_796_);
lean_inc_ref(v_lctx_795_);
v___x_797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_797_, 0, v_env_792_);
lean_ctor_set(v___x_797_, 1, v_mctx_794_);
lean_ctor_set(v___x_797_, 2, v_lctx_795_);
lean_ctor_set(v___x_797_, 3, v_options_796_);
v___x_798_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_msgData_785_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4___boxed(lean_object* v_msgData_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msgData_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_ref_815_; lean_object* v___x_816_; lean_object* v_a_817_; lean_object* v_macroStack_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
v_ref_815_ = lean_ctor_get(v___y_812_, 5);
v___x_816_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_807_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
v_macroStack_818_ = lean_ctor_get(v___y_808_, 1);
v___x_819_ = l_Lean_Elab_getBetterRef(v_ref_815_, v_macroStack_818_);
lean_inc(v_macroStack_818_);
v___x_820_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_a_817_, v_macroStack_818_, v___y_812_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_819_);
lean_ctor_set(v___x_825_, 1, v_a_821_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 1);
lean_ctor_set(v___x_823_, 0, v___x_825_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg___boxed(lean_object* v_msg_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v_msg_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_inc(v_x_839_);
return v_x_839_;
}
else
{
lean_object* v_key_841_; lean_object* v_tail_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_key_841_ = lean_ctor_get(v_x_840_, 0);
v_tail_842_ = lean_ctor_get(v_x_840_, 2);
v___x_843_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_x_839_, v_tail_842_);
lean_inc(v_key_841_);
v___x_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_844_, 0, v_key_841_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4___boxed(lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_x_845_, v_x_846_);
lean_dec(v_x_846_);
lean_dec(v_x_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(lean_object* v_as_848_, size_t v_i_849_, size_t v_stop_850_, lean_object* v_b_851_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_eq(v_i_849_, v_stop_850_);
if (v___x_852_ == 0)
{
size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_sub(v_i_849_, v___x_853_);
v___x_855_ = lean_array_uget_borrowed(v_as_848_, v___x_854_);
v___x_856_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_b_851_, v___x_855_);
lean_dec(v_b_851_);
v_i_849_ = v___x_854_;
v_b_851_ = v___x_856_;
goto _start;
}
else
{
return v_b_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5___boxed(lean_object* v_as_858_, lean_object* v_i_859_, lean_object* v_stop_860_, lean_object* v_b_861_){
_start:
{
size_t v_i_boxed_862_; size_t v_stop_boxed_863_; lean_object* v_res_864_; 
v_i_boxed_862_ = lean_unbox_usize(v_i_859_);
lean_dec(v_i_859_);
v_stop_boxed_863_ = lean_unbox_usize(v_stop_860_);
lean_dec(v_stop_860_);
v_res_864_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_as_858_, v_i_boxed_862_, v_stop_boxed_863_, v_b_861_);
lean_dec_ref(v_as_858_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
if (lean_obj_tag(v_a_865_) == 0)
{
lean_object* v___x_867_; 
v___x_867_ = l_List_reverse___redArg(v_a_866_);
return v___x_867_;
}
else
{
lean_object* v_head_868_; lean_object* v_tail_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_878_; 
v_head_868_ = lean_ctor_get(v_a_865_, 0);
v_tail_869_ = lean_ctor_get(v_a_865_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_a_865_);
if (v_isSharedCheck_878_ == 0)
{
v___x_871_ = v_a_865_;
v_isShared_872_ = v_isSharedCheck_878_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_tail_869_);
lean_inc(v_head_868_);
lean_dec(v_a_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_878_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_Lean_MessageData_ofExpr(v_head_868_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v_a_866_);
lean_ctor_set(v___x_871_, 0, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_a_866_);
v___x_875_ = v_reuseFailAlloc_877_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v_a_865_ = v_tail_869_;
v_a_866_ = v___x_875_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_879_; double v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_float_of_nat(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(lean_object* v_cls_883_, lean_object* v_msg_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_ref_890_; lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_936_; 
v_ref_890_ = lean_ctor_get(v___y_887_, 5);
v___x_891_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_936_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_936_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_936_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v_traceState_897_; lean_object* v_env_898_; lean_object* v_nextMacroScope_899_; lean_object* v_ngen_900_; lean_object* v_auxDeclNGen_901_; lean_object* v_cache_902_; lean_object* v_messages_903_; lean_object* v_infoState_904_; lean_object* v_snapshotTasks_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_935_; 
v___x_896_ = lean_st_ref_take(v___y_888_);
v_traceState_897_ = lean_ctor_get(v___x_896_, 4);
v_env_898_ = lean_ctor_get(v___x_896_, 0);
v_nextMacroScope_899_ = lean_ctor_get(v___x_896_, 1);
v_ngen_900_ = lean_ctor_get(v___x_896_, 2);
v_auxDeclNGen_901_ = lean_ctor_get(v___x_896_, 3);
v_cache_902_ = lean_ctor_get(v___x_896_, 5);
v_messages_903_ = lean_ctor_get(v___x_896_, 6);
v_infoState_904_ = lean_ctor_get(v___x_896_, 7);
v_snapshotTasks_905_ = lean_ctor_get(v___x_896_, 8);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_935_ == 0)
{
v___x_907_ = v___x_896_;
v_isShared_908_ = v_isSharedCheck_935_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_snapshotTasks_905_);
lean_inc(v_infoState_904_);
lean_inc(v_messages_903_);
lean_inc(v_cache_902_);
lean_inc(v_traceState_897_);
lean_inc(v_auxDeclNGen_901_);
lean_inc(v_ngen_900_);
lean_inc(v_nextMacroScope_899_);
lean_inc(v_env_898_);
lean_dec(v___x_896_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_935_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
uint64_t v_tid_909_; lean_object* v_traces_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_934_; 
v_tid_909_ = lean_ctor_get_uint64(v_traceState_897_, sizeof(void*)*1);
v_traces_910_ = lean_ctor_get(v_traceState_897_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_traceState_897_);
if (v_isSharedCheck_934_ == 0)
{
v___x_912_ = v_traceState_897_;
v_isShared_913_ = v_isSharedCheck_934_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_traces_910_);
lean_dec(v_traceState_897_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_934_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; double v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_914_ = lean_box(0);
v___x_915_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
v___x_916_ = 0;
v___x_917_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_918_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_918_, 0, v_cls_883_);
lean_ctor_set(v___x_918_, 1, v___x_914_);
lean_ctor_set(v___x_918_, 2, v___x_917_);
lean_ctor_set_float(v___x_918_, sizeof(void*)*3, v___x_915_);
lean_ctor_set_float(v___x_918_, sizeof(void*)*3 + 8, v___x_915_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*3 + 16, v___x_916_);
v___x_919_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1));
v___x_920_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v_a_892_);
lean_ctor_set(v___x_920_, 2, v___x_919_);
lean_inc(v_ref_890_);
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_ref_890_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l_Lean_PersistentArray_push___redArg(v_traces_910_, v___x_921_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_922_);
v___x_924_ = v___x_912_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_922_);
lean_ctor_set_uint64(v_reuseFailAlloc_933_, sizeof(void*)*1, v_tid_909_);
v___x_924_ = v_reuseFailAlloc_933_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 4, v___x_924_);
v___x_926_ = v___x_907_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_env_898_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_nextMacroScope_899_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_ngen_900_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_auxDeclNGen_901_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_932_, 5, v_cache_902_);
lean_ctor_set(v_reuseFailAlloc_932_, 6, v_messages_903_);
lean_ctor_set(v_reuseFailAlloc_932_, 7, v_infoState_904_);
lean_ctor_set(v_reuseFailAlloc_932_, 8, v_snapshotTasks_905_);
v___x_926_ = v_reuseFailAlloc_932_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_927_ = lean_st_ref_set(v___y_888_, v___x_926_);
v___x_928_ = lean_box(0);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_928_);
v___x_930_ = v___x_894_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___boxed(lean_object* v_cls_937_, lean_object* v_msg_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_937_, v_msg_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(lean_object* v_msg_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_ref_951_; lean_object* v___x_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
v_ref_951_ = lean_ctor_get(v___y_948_, 5);
v___x_952_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_961_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
lean_inc(v_ref_951_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_ref_951_);
lean_ctor_set(v___x_957_, 1, v_a_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 1);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg___boxed(lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v_msg_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_968_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(lean_object* v_a_969_, lean_object* v_as_970_, size_t v_i_971_, size_t v_stop_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_eq(v_i_971_, v_stop_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_974_ = lean_array_uget_borrowed(v_as_970_, v_i_971_);
v___x_975_ = lean_nat_dec_eq(v_a_969_, v___x_974_);
if (v___x_975_ == 0)
{
size_t v___x_976_; size_t v___x_977_; 
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_add(v_i_971_, v___x_976_);
v_i_971_ = v___x_977_;
goto _start;
}
else
{
return v___x_975_;
}
}
else
{
uint8_t v___x_979_; 
v___x_979_ = 0;
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25___boxed(lean_object* v_a_980_, lean_object* v_as_981_, lean_object* v_i_982_, lean_object* v_stop_983_){
_start:
{
size_t v_i_boxed_984_; size_t v_stop_boxed_985_; uint8_t v_res_986_; lean_object* v_r_987_; 
v_i_boxed_984_ = lean_unbox_usize(v_i_982_);
lean_dec(v_i_982_);
v_stop_boxed_985_ = lean_unbox_usize(v_stop_983_);
lean_dec(v_stop_983_);
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(v_a_980_, v_as_981_, v_i_boxed_984_, v_stop_boxed_985_);
lean_dec_ref(v_as_981_);
lean_dec(v_a_980_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(lean_object* v_as_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_array_get_size(v_as_988_);
v___x_992_ = lean_nat_dec_lt(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
return v___x_992_;
}
else
{
if (v___x_992_ == 0)
{
return v___x_992_;
}
else
{
size_t v___x_993_; size_t v___x_994_; uint8_t v___x_995_; 
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_991_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(v_a_989_, v_as_988_, v___x_993_, v___x_994_);
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20___boxed(lean_object* v_as_996_, lean_object* v_a_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(v_as_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_as_996_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(lean_object* v___x_1003_, lean_object* v_fst_1004_, lean_object* v_range_1005_, lean_object* v_b_1006_, lean_object* v_i_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_stop_1015_; lean_object* v_step_1016_; uint8_t v___x_1017_; 
v_stop_1015_ = lean_ctor_get(v_range_1005_, 1);
v_step_1016_ = lean_ctor_get(v_range_1005_, 2);
v___x_1017_ = lean_nat_dec_lt(v_i_1007_, v_stop_1015_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_i_1007_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1006_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; uint8_t v___x_1023_; 
v___x_1019_ = lean_box(0);
v___x_1023_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(v___x_1003_, v_i_1007_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; uint8_t v___x_1027_; uint8_t v___x_1028_; 
v___x_1024_ = lean_array_fget_borrowed(v_fst_1004_, v_i_1007_);
lean_inc(v___x_1024_);
v___x_1025_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v___x_1024_, v___y_1011_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = l_Lean_Expr_hasMVar(v_a_1026_);
lean_dec(v_a_1026_);
v___x_1028_ = lean_bool_not(v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec(v_i_1007_);
v___x_1029_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1030_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1029_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1030_;
}
else
{
goto v___jp_1020_;
}
}
else
{
goto v___jp_1020_;
}
v___jp_1020_:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_nat_add(v_i_1007_, v_step_1016_);
lean_dec(v_i_1007_);
v_b_1006_ = v___x_1019_;
v_i_1007_ = v___x_1021_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___boxed(lean_object* v___x_1031_, lean_object* v_fst_1032_, lean_object* v_range_1033_, lean_object* v_b_1034_, lean_object* v_i_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_1031_, v_fst_1032_, v_range_1033_, v_b_1034_, v_i_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_range_1033_);
lean_dec_ref(v_fst_1032_);
lean_dec_ref(v___x_1031_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(lean_object* v_fst_1044_, lean_object* v_className_1045_, lean_object* v_as_1046_, size_t v_sz_1047_, size_t v_i_1048_, lean_object* v_b_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_a_1058_; uint8_t v___x_1062_; 
v___x_1062_ = lean_usize_dec_lt(v_i_1048_, v_sz_1047_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_b_1049_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = l_Lean_instInhabitedExpr;
v_a_1065_ = lean_array_uget_borrowed(v_as_1046_, v_i_1048_);
v___x_1066_ = lean_array_get_borrowed(v___x_1064_, v_fst_1044_, v_a_1065_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___x_1066_);
v___x_1067_ = lean_infer_type(v___x_1066_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
v___x_1069_ = lean_whnf(v_a_1068_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1071_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_a_1070_, v___y_1053_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = l_Lean_Expr_isAppOfArity(v_a_1072_, v_className_1045_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_a_1072_);
v___x_1075_ = lean_box(0);
v___x_1076_ = l_Lean_Expr_mvarId_x21(v___x_1066_);
v___x_1077_ = l_Lean_Elab_Term_synthesizeInstMVarCore(v___x_1076_, v___x_1075_, v___x_1075_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; uint8_t v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = lean_unbox(v_a_1078_);
lean_dec(v_a_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1081_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1080_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_dec_ref_known(v___x_1081_, 1);
v_a_1058_ = v_b_1049_;
goto v___jp_1057_;
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v_b_1049_);
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
v_a_1058_ = v_b_1049_;
goto v___jp_1057_;
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v_b_1049_);
v_a_1090_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1077_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1077_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = l_Lean_Expr_appArg_x21(v_a_1072_);
lean_dec(v_a_1072_);
v___x_1099_ = lean_array_push(v_b_1049_, v___x_1098_);
v_a_1058_ = v___x_1099_;
goto v___jp_1057_;
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v_b_1049_);
v_a_1100_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1071_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1071_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_b_1049_);
v_a_1108_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1069_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1069_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_b_1049_);
v_a_1116_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1067_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1067_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
v___jp_1057_:
{
size_t v___x_1059_; size_t v___x_1060_; 
v___x_1059_ = ((size_t)1ULL);
v___x_1060_ = lean_usize_add(v_i_1048_, v___x_1059_);
v_i_1048_ = v___x_1060_;
v_b_1049_ = v_a_1058_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19___boxed(lean_object* v_fst_1124_, lean_object* v_className_1125_, lean_object* v_as_1126_, lean_object* v_sz_1127_, lean_object* v_i_1128_, lean_object* v_b_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
size_t v_sz_boxed_1137_; size_t v_i_boxed_1138_; lean_object* v_res_1139_; 
v_sz_boxed_1137_ = lean_unbox_usize(v_sz_1127_);
lean_dec(v_sz_1127_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v_fst_1124_, v_className_1125_, v_as_1126_, v_sz_boxed_1137_, v_i_boxed_1138_, v_b_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v_as_1126_);
lean_dec(v_className_1125_);
lean_dec_ref(v_fst_1124_);
return v_res_1139_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0));
v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
return v___x_1142_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(lean_object* v_className_1148_, lean_object* v_extraDeps_1149_, lean_object* v_plan_1150_, lean_object* v_processing_1151_, lean_object* v_depTypes_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
size_t v_sz_1160_; size_t v___x_1161_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___x_1205_; 
v_sz_1160_ = lean_array_size(v_depTypes_1152_);
v___x_1161_ = ((size_t)0ULL);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(v_sz_1160_, v___x_1161_, v_depTypes_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___x_1223_; size_t v_sz_1224_; lean_object* v___x_1225_; lean_object* v_fst_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1246_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v_sz_1224_ = lean_array_size(v_a_1206_);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(v_a_1206_, v_sz_1224_, v___x_1161_, v___x_1223_);
v_fst_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1225_, 1);
lean_dec(v_unused_1247_);
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_fst_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1246_;
goto v_resetjp_1227_;
}
v___jp_1207_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_array_get_size(v_a_1206_);
v___x_1216_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v___x_1217_ = lean_nat_dec_lt(v___x_1214_, v___x_1215_);
if (v___x_1217_ == 0)
{
lean_dec(v_a_1206_);
v___y_1173_ = v___y_1210_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1208_;
v___y_1176_ = v___y_1213_;
v___y_1177_ = v___y_1209_;
v___y_1178_ = v___y_1211_;
v___y_1179_ = v___x_1216_;
goto v___jp_1172_;
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = lean_nat_dec_le(v___x_1215_, v___x_1215_);
if (v___x_1218_ == 0)
{
if (v___x_1217_ == 0)
{
lean_dec(v_a_1206_);
v___y_1173_ = v___y_1210_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1208_;
v___y_1176_ = v___y_1213_;
v___y_1177_ = v___y_1209_;
v___y_1178_ = v___y_1211_;
v___y_1179_ = v___x_1216_;
goto v___jp_1172_;
}
else
{
size_t v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_usize_of_nat(v___x_1215_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_1150_, v_a_1206_, v___x_1161_, v___x_1219_, v___x_1216_);
lean_dec(v_a_1206_);
v___y_1173_ = v___y_1210_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1208_;
v___y_1176_ = v___y_1213_;
v___y_1177_ = v___y_1209_;
v___y_1178_ = v___y_1211_;
v___y_1179_ = v___x_1220_;
goto v___jp_1172_;
}
}
else
{
size_t v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_usize_of_nat(v___x_1215_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_1150_, v_a_1206_, v___x_1161_, v___x_1221_, v___x_1216_);
lean_dec(v_a_1206_);
v___y_1173_ = v___y_1210_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1208_;
v___y_1176_ = v___y_1213_;
v___y_1177_ = v___y_1209_;
v___y_1178_ = v___y_1211_;
v___y_1179_ = v___x_1222_;
goto v___jp_1172_;
}
}
}
v_resetjp_1227_:
{
if (lean_obj_tag(v_fst_1226_) == 0)
{
lean_del_object(v___x_1228_);
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
v___y_1213_ = v_a_1158_;
goto v___jp_1207_;
}
else
{
lean_object* v_val_1230_; 
v_val_1230_ = lean_ctor_get(v_fst_1226_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v_fst_1226_, 1);
if (lean_obj_tag(v_val_1230_) == 1)
{
lean_object* v_val_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v_val_1231_ = lean_ctor_get(v_val_1230_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v_val_1230_, 1);
v___x_1232_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4);
v___x_1233_ = l_Lean_MessageData_ofExpr(v_val_1231_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 7);
lean_ctor_set(v___x_1228_, 1, v___x_1233_);
lean_ctor_set(v___x_1228_, 0, v___x_1232_);
v___x_1235_ = v___x_1228_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_1235_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_dec_ref_known(v___x_1236_, 1);
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
v___y_1213_ = v_a_1158_;
goto v___jp_1207_;
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_a_1206_);
lean_dec_ref(v_processing_1151_);
lean_dec_ref(v_plan_1150_);
lean_dec_ref(v_extraDeps_1149_);
lean_dec(v_className_1148_);
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
else
{
lean_dec(v_val_1230_);
lean_del_object(v___x_1228_);
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
v___y_1213_ = v_a_1158_;
goto v___jp_1207_;
}
}
}
}
else
{
lean_dec_ref(v_processing_1151_);
lean_dec_ref(v_plan_1150_);
lean_dec_ref(v_extraDeps_1149_);
lean_dec(v_className_1148_);
return v___x_1205_;
}
v___jp_1162_:
{
size_t v_sz_1170_; lean_object* v___x_1171_; 
v_sz_1170_ = lean_array_size(v___y_1163_);
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_1151_, v_className_1148_, v_extraDeps_1149_, v___y_1163_, v_sz_1170_, v___x_1161_, v_plan_1150_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec_ref(v___y_1163_);
return v___x_1171_;
}
v___jp_1172_:
{
lean_object* v___x_1180_; size_t v_sz_1181_; lean_object* v___x_1182_; lean_object* v_fst_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1203_; 
v___x_1180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v_sz_1181_ = lean_array_size(v___y_1179_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(v_processing_1151_, v___y_1179_, v_sz_1181_, v___x_1161_, v___x_1180_);
v_fst_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v___x_1182_, 1);
lean_dec(v_unused_1204_);
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1203_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_fst_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1203_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
if (lean_obj_tag(v_fst_1183_) == 0)
{
lean_del_object(v___x_1185_);
v___y_1163_ = v___y_1179_;
v___y_1164_ = v___y_1175_;
v___y_1165_ = v___y_1177_;
v___y_1166_ = v___y_1173_;
v___y_1167_ = v___y_1178_;
v___y_1168_ = v___y_1174_;
v___y_1169_ = v___y_1176_;
goto v___jp_1162_;
}
else
{
lean_object* v_val_1187_; 
v_val_1187_ = lean_ctor_get(v_fst_1183_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v_fst_1183_, 1);
if (lean_obj_tag(v_val_1187_) == 1)
{
lean_object* v_val_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v_val_1188_ = lean_ctor_get(v_val_1187_, 0);
lean_inc(v_val_1188_);
lean_dec_ref_known(v_val_1187_, 1);
v___x_1189_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1);
v___x_1190_ = l_Lean_MessageData_ofExpr(v_val_1188_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 7);
lean_ctor_set(v___x_1185_, 1, v___x_1190_);
lean_ctor_set(v___x_1185_, 0, v___x_1189_);
v___x_1192_ = v___x_1185_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_1192_, v___y_1175_, v___y_1177_, v___y_1173_, v___y_1178_, v___y_1174_, v___y_1176_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_dec_ref_known(v___x_1193_, 1);
v___y_1163_ = v___y_1179_;
v___y_1164_ = v___y_1175_;
v___y_1165_ = v___y_1177_;
v___y_1166_ = v___y_1173_;
v___y_1167_ = v___y_1178_;
v___y_1168_ = v___y_1174_;
v___y_1169_ = v___y_1176_;
goto v___jp_1162_;
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v___y_1179_);
lean_dec_ref(v_processing_1151_);
lean_dec_ref(v_plan_1150_);
lean_dec_ref(v_extraDeps_1149_);
lean_dec(v_className_1148_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
else
{
lean_dec(v_val_1187_);
lean_del_object(v___x_1185_);
v___y_1163_ = v___y_1179_;
v___y_1164_ = v___y_1175_;
v___y_1165_ = v___y_1177_;
v___y_1166_ = v___y_1173_;
v___y_1167_ = v___y_1178_;
v___y_1168_ = v___y_1174_;
v___y_1169_ = v___y_1176_;
goto v___jp_1162_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3(void){
_start:
{
lean_object* v_cls_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_cls_1256_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1257_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1));
v___x_1258_ = l_Lean_Name_append(v___x_1257_, v_cls_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4));
v___x_1261_ = l_Lean_stringToMessageData(v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6));
v___x_1264_ = l_Lean_stringToMessageData(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(lean_object* v_className_1274_, lean_object* v_extraDeps_1275_, lean_object* v_plan_1276_, lean_object* v_processing_1277_, lean_object* v_cls_1278_, lean_object* v_inst_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_cls_1287_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___x_1457_; 
v_cls_1287_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1457_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1287_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; uint8_t v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = lean_unbox(v_a_1458_);
lean_dec(v_a_1458_);
if (v___x_1459_ == 0)
{
v___y_1375_ = v_a_1280_;
v___y_1376_ = v_a_1281_;
v___y_1377_ = v_a_1282_;
v___y_1378_ = v_a_1283_;
v___y_1379_ = v_a_1284_;
v___y_1380_ = v_a_1285_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13);
lean_inc_ref(v_cls_1278_);
v___x_1461_ = l_Lean_MessageData_ofExpr(v_cls_1278_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1287_, v___x_1462_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec_ref_known(v___x_1463_, 1);
v___y_1375_ = v_a_1280_;
v___y_1376_ = v_a_1281_;
v___y_1377_ = v_a_1282_;
v___y_1378_ = v_a_1283_;
v___y_1379_ = v_a_1284_;
v___y_1380_ = v_a_1285_;
goto v___jp_1374_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_inst_1279_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v_inst_1279_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1472_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1457_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1457_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
v___jp_1288_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; size_t v_sz_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v_sz_1299_ = lean_array_size(v___y_1296_);
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v___y_1289_, v_className_1274_, v___y_1296_, v_sz_1299_, v___x_1300_, v___x_1298_, v___y_1290_, v___y_1293_, v___y_1292_, v___y_1295_, v___y_1291_, v___y_1294_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1303_ = lean_array_get_size(v___y_1289_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1297_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1304_);
v___x_1306_ = lean_box(0);
v___x_1307_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___y_1296_, v___y_1289_, v___x_1305_, v___x_1306_, v___x_1297_, v___y_1290_, v___y_1293_, v___y_1292_, v___y_1295_, v___y_1291_, v___y_1294_);
lean_dec_ref_known(v___x_1305_, 3);
lean_dec_ref(v___y_1289_);
lean_dec_ref(v___y_1296_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_options_1308_; uint8_t v_hasTrace_1309_; 
lean_dec_ref_known(v___x_1307_, 1);
v_options_1308_ = lean_ctor_get(v___y_1291_, 2);
v_hasTrace_1309_ = lean_ctor_get_uint8(v_options_1308_, sizeof(void*)*1);
if (v_hasTrace_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_dec_ref(v_cls_1278_);
v___x_1310_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1274_, v_extraDeps_1275_, v_plan_1276_, v_processing_1277_, v_a_1302_, v___y_1290_, v___y_1293_, v___y_1292_, v___y_1295_, v___y_1291_, v___y_1294_);
return v___x_1310_;
}
else
{
lean_object* v_inheritedTraceOptions_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_inheritedTraceOptions_1311_ = lean_ctor_get(v___y_1291_, 13);
v___x_1312_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_1313_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1311_, v_options_1308_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v_cls_1278_);
v___x_1314_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1274_, v_extraDeps_1275_, v_plan_1276_, v_processing_1277_, v_a_1302_, v___y_1290_, v___y_1293_, v___y_1292_, v___y_1295_, v___y_1291_, v___y_1294_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1315_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5);
v___x_1316_ = l_Lean_MessageData_ofExpr(v_cls_1278_);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
lean_inc(v_a_1302_);
v___x_1320_ = lean_array_to_list(v_a_1302_);
v___x_1321_ = lean_box(0);
v___x_1322_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1320_, v___x_1321_);
v___x_1323_ = l_Lean_MessageData_ofList(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1319_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1287_, v___x_1324_, v___y_1292_, v___y_1295_, v___y_1291_, v___y_1294_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1326_; 
lean_dec_ref_known(v___x_1325_, 1);
v___x_1326_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1274_, v_extraDeps_1275_, v_plan_1276_, v_processing_1277_, v_a_1302_, v___y_1290_, v___y_1293_, v___y_1292_, v___y_1295_, v___y_1291_, v___y_1294_);
return v___x_1326_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_a_1302_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1327_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1325_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1325_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v_a_1302_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1335_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1307_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1307_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_dec_ref(v___y_1296_);
lean_dec_ref(v___y_1289_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
return v___x_1301_;
}
}
v___jp_1343_:
{
lean_object* v___x_1353_; 
lean_inc_ref(v_cls_1278_);
v___x_1353_ = l_Lean_Meta_isExprDefEq(v_cls_1278_, v___y_1345_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; uint8_t v___x_1355_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1355_ = lean_unbox(v_a_1354_);
lean_dec(v_a_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1357_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1356_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
v___y_1289_ = v___y_1344_;
v___y_1290_ = v___y_1347_;
v___y_1291_ = v___y_1351_;
v___y_1292_ = v___y_1349_;
v___y_1293_ = v___y_1348_;
v___y_1294_ = v___y_1352_;
v___y_1295_ = v___y_1350_;
v___y_1296_ = v___y_1346_;
goto v___jp_1288_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v___y_1346_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
else
{
v___y_1289_ = v___y_1344_;
v___y_1290_ = v___y_1347_;
v___y_1291_ = v___y_1351_;
v___y_1292_ = v___y_1349_;
v___y_1293_ = v___y_1348_;
v___y_1294_ = v___y_1352_;
v___y_1295_ = v___y_1350_;
v___y_1296_ = v___y_1346_;
goto v___jp_1288_;
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v___y_1346_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1366_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1353_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1353_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
v___jp_1374_:
{
lean_object* v_val_1381_; lean_object* v_synthOrder_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1456_; 
v_val_1381_ = lean_ctor_get(v_inst_1279_, 0);
v_synthOrder_1382_ = lean_ctor_get(v_inst_1279_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_inst_1279_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1384_ = v_inst_1279_;
v_isShared_1385_ = v_isSharedCheck_1456_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_synthOrder_1382_);
lean_inc(v_val_1381_);
lean_dec(v_inst_1279_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1456_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; 
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
v___x_1386_ = lean_infer_type(v_val_1381_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = lean_box(0);
v___x_1389_ = 0;
v___x_1390_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1387_, v___x_1388_, v___x_1389_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v_snd_1392_; lean_object* v_fst_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1439_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v_snd_1392_ = lean_ctor_get(v_a_1391_, 1);
v_fst_1393_ = lean_ctor_get(v_a_1391_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_a_1391_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1395_ = v_a_1391_;
v_isShared_1396_ = v_isSharedCheck_1439_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_snd_1392_);
lean_inc(v_fst_1393_);
lean_dec(v_a_1391_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1439_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_snd_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1437_; 
v_snd_1397_ = lean_ctor_get(v_snd_1392_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_snd_1392_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_snd_1392_, 0);
lean_dec(v_unused_1438_);
v___x_1399_ = v_snd_1392_;
v_isShared_1400_ = v_isSharedCheck_1437_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_snd_1397_);
lean_dec(v_snd_1392_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1437_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; 
v___x_1401_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1287_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; uint8_t v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1403_ = lean_unbox(v_a_1402_);
lean_dec(v_a_1402_);
if (v___x_1403_ == 0)
{
lean_del_object(v___x_1399_);
lean_del_object(v___x_1395_);
lean_del_object(v___x_1384_);
v___y_1344_ = v_fst_1393_;
v___y_1345_ = v_snd_1397_;
v___y_1346_ = v_synthOrder_1382_;
v___y_1347_ = v___y_1375_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___y_1377_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1380_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1404_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9);
lean_inc(v_fst_1393_);
v___x_1405_ = lean_array_to_list(v_fst_1393_);
v___x_1406_ = lean_box(0);
v___x_1407_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1405_, v___x_1406_);
v___x_1408_ = l_Lean_MessageData_ofList(v___x_1407_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 7);
lean_ctor_set(v___x_1399_, 1, v___x_1408_);
lean_ctor_set(v___x_1399_, 0, v___x_1404_);
v___x_1410_ = v___x_1399_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11);
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 7);
lean_ctor_set(v___x_1395_, 1, v___x_1411_);
lean_ctor_set(v___x_1395_, 0, v___x_1410_);
v___x_1413_ = v___x_1395_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
lean_inc(v_snd_1397_);
v___x_1414_ = l_Lean_MessageData_ofExpr(v_snd_1397_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set_tag(v___x_1384_, 7);
lean_ctor_set(v___x_1384_, 1, v___x_1414_);
lean_ctor_set(v___x_1384_, 0, v___x_1413_);
v___x_1416_ = v___x_1384_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1287_, v___x_1416_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref_known(v___x_1417_, 1);
v___y_1344_ = v_fst_1393_;
v___y_1345_ = v_snd_1397_;
v___y_1346_ = v_synthOrder_1382_;
v___y_1347_ = v___y_1375_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___y_1377_;
v___y_1350_ = v___y_1378_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1380_;
goto v___jp_1343_;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_snd_1397_);
lean_dec(v_fst_1393_);
lean_dec_ref(v_synthOrder_1382_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
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
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_del_object(v___x_1399_);
lean_dec(v_snd_1397_);
lean_del_object(v___x_1395_);
lean_dec(v_fst_1393_);
lean_del_object(v___x_1384_);
lean_dec_ref(v_synthOrder_1382_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1429_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1401_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1401_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_del_object(v___x_1384_);
lean_dec_ref(v_synthOrder_1382_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1440_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1390_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1390_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_del_object(v___x_1384_);
lean_dec_ref(v_synthOrder_1382_);
lean_dec_ref(v_cls_1278_);
lean_dec_ref(v_processing_1277_);
lean_dec_ref(v_plan_1276_);
lean_dec_ref(v_extraDeps_1275_);
lean_dec(v_className_1274_);
v_a_1448_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1386_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1386_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(lean_object* v_className_1480_, lean_object* v_extraDeps_1481_, lean_object* v_plan_1482_, lean_object* v_processing_1483_, lean_object* v_a_1484_, lean_object* v_as_1485_, size_t v_sz_1486_, size_t v_i_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_usize_dec_lt(v_i_1487_, v_sz_1486_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
lean_dec_ref(v_a_1484_);
lean_dec_ref(v_processing_1483_);
lean_dec_ref(v_plan_1482_);
lean_dec_ref(v_extraDeps_1481_);
lean_dec(v_className_1480_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_b_1488_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; lean_object* v_a_1499_; lean_object* v___x_1500_; 
lean_dec_ref(v_b_1488_);
v___x_1498_ = lean_box(0);
v_a_1499_ = lean_array_uget_borrowed(v_as_1485_, v_i_1487_);
lean_inc(v_a_1499_);
lean_inc_ref(v_a_1484_);
lean_inc_ref(v_processing_1483_);
lean_inc_ref(v_plan_1482_);
lean_inc_ref(v_extraDeps_1481_);
lean_inc(v_className_1480_);
v___x_1500_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(v_className_1480_, v_extraDeps_1481_, v_plan_1482_, v_processing_1483_, v_a_1484_, v_a_1499_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref(v_a_1484_);
lean_dec_ref(v_processing_1483_);
lean_dec_ref(v_plan_1482_);
lean_dec_ref(v_extraDeps_1481_);
lean_dec(v_className_1480_);
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1510_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1510_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_a_1501_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v___x_1498_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1506_);
v___x_1508_ = v___x_1503_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1526_; 
v_a_1511_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1513_ = v___x_1500_;
v_isShared_1514_ = v_isSharedCheck_1526_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1500_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1526_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; uint8_t v___y_1517_; uint8_t v___x_1524_; 
v___x_1515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0));
v___x_1524_ = l_Lean_Exception_isInterrupt(v_a_1511_);
if (v___x_1524_ == 0)
{
uint8_t v___x_1525_; 
lean_inc(v_a_1511_);
v___x_1525_ = l_Lean_Exception_isRuntime(v_a_1511_);
v___y_1517_ = v___x_1525_;
goto v___jp_1516_;
}
else
{
v___y_1517_ = v___x_1524_;
goto v___jp_1516_;
}
v___jp_1516_:
{
if (v___y_1517_ == 0)
{
size_t v___x_1518_; size_t v___x_1519_; 
lean_del_object(v___x_1513_);
lean_dec(v_a_1511_);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1487_, v___x_1518_);
v_i_1487_ = v___x_1519_;
v_b_1488_ = v___x_1515_;
goto _start;
}
else
{
lean_object* v___x_1522_; 
lean_dec_ref(v_a_1484_);
lean_dec_ref(v_processing_1483_);
lean_dec_ref(v_plan_1482_);
lean_dec_ref(v_extraDeps_1481_);
lean_dec(v_className_1480_);
if (v_isShared_1514_ == 0)
{
v___x_1522_ = v___x_1513_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1511_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
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
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11(void){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10));
v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(lean_object* v_className_1545_, lean_object* v_extraDeps_1546_, lean_object* v_plan_1547_, lean_object* v_processing_1548_, lean_object* v_type_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v_fileName_1575_; lean_object* v_fileMap_1576_; lean_object* v_options_1577_; lean_object* v_currRecDepth_1578_; lean_object* v_maxRecDepth_1579_; lean_object* v_ref_1580_; lean_object* v_currNamespace_1581_; lean_object* v_openDecls_1582_; lean_object* v_initHeartbeats_1583_; lean_object* v_maxHeartbeats_1584_; lean_object* v_quotContext_1585_; lean_object* v_currMacroScope_1586_; uint8_t v_diag_1587_; lean_object* v_cancelTk_x3f_1588_; uint8_t v_suppressElabErrors_1589_; lean_object* v_inheritedTraceOptions_1590_; lean_object* v_cls_1591_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; uint8_t v___y_1741_; lean_object* v___x_1772_; uint8_t v___x_1773_; uint8_t v___x_1774_; 
v_fileName_1575_ = lean_ctor_get(v_a_1554_, 0);
v_fileMap_1576_ = lean_ctor_get(v_a_1554_, 1);
v_options_1577_ = lean_ctor_get(v_a_1554_, 2);
v_currRecDepth_1578_ = lean_ctor_get(v_a_1554_, 3);
v_maxRecDepth_1579_ = lean_ctor_get(v_a_1554_, 4);
v_ref_1580_ = lean_ctor_get(v_a_1554_, 5);
v_currNamespace_1581_ = lean_ctor_get(v_a_1554_, 6);
v_openDecls_1582_ = lean_ctor_get(v_a_1554_, 7);
v_initHeartbeats_1583_ = lean_ctor_get(v_a_1554_, 8);
v_maxHeartbeats_1584_ = lean_ctor_get(v_a_1554_, 9);
v_quotContext_1585_ = lean_ctor_get(v_a_1554_, 10);
v_currMacroScope_1586_ = lean_ctor_get(v_a_1554_, 11);
v_diag_1587_ = lean_ctor_get_uint8(v_a_1554_, sizeof(void*)*14);
v_cancelTk_x3f_1588_ = lean_ctor_get(v_a_1554_, 12);
v_suppressElabErrors_1589_ = lean_ctor_get_uint8(v_a_1554_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1590_ = lean_ctor_get(v_a_1554_, 13);
v_cls_1591_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_nat_dec_eq(v_maxRecDepth_1579_, v___x_1772_);
v___x_1774_ = lean_bool_not(v___x_1773_);
if (v___x_1774_ == 0)
{
v___y_1741_ = v___x_1774_;
goto v___jp_1740_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_eq(v_currRecDepth_1578_, v_maxRecDepth_1579_);
v___y_1741_ = v___x_1775_;
goto v___jp_1740_;
}
v___jp_1557_:
{
lean_object* v___x_1565_; 
v___x_1565_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1545_, v_extraDeps_1546_, v_plan_1547_, v_processing_1548_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec_ref(v___y_1563_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1574_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_array_push(v_a_1566_, v_type_1549_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1570_);
v___x_1572_ = v___x_1568_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
lean_dec_ref(v_type_1549_);
return v___x_1565_;
}
}
v___jp_1592_:
{
lean_object* v___x_1601_; size_t v_sz_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v___x_1601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0));
v_sz_1602_ = lean_array_size(v___y_1594_);
v___x_1603_ = ((size_t)0ULL);
lean_inc_ref(v_processing_1548_);
lean_inc_ref(v_plan_1547_);
lean_inc_ref(v_extraDeps_1546_);
lean_inc(v_className_1545_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_1545_, v_extraDeps_1546_, v_plan_1547_, v_processing_1548_, v___y_1593_, v___y_1594_, v_sz_1602_, v___x_1603_, v___x_1601_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec_ref(v___y_1594_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1648_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1648_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1648_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_fst_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1646_; 
v_fst_1609_ = lean_ctor_get(v_a_1605_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_a_1605_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v_a_1605_, 1);
lean_dec(v_unused_1647_);
v___x_1611_ = v_a_1605_;
v_isShared_1612_ = v_isSharedCheck_1646_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_fst_1609_);
lean_dec(v_a_1605_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1646_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
if (lean_obj_tag(v_fst_1609_) == 0)
{
lean_object* v___x_1613_; 
lean_del_object(v___x_1607_);
lean_inc_ref(v_extraDeps_1546_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
lean_inc_ref(v_type_1549_);
v___x_1613_ = lean_apply_8(v_extraDeps_1546_, v_type_1549_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, lean_box(0));
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_options_1614_; uint8_t v_hasTrace_1615_; 
v_options_1614_ = lean_ctor_get(v___y_1599_, 2);
v_hasTrace_1615_ = lean_ctor_get_uint8(v_options_1614_, sizeof(void*)*1);
if (v_hasTrace_1615_ == 0)
{
lean_object* v_a_1616_; 
lean_del_object(v___x_1611_);
v_a_1616_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1613_, 1);
v___y_1558_ = v_a_1616_;
v___y_1559_ = v___y_1595_;
v___y_1560_ = v___y_1596_;
v___y_1561_ = v___y_1597_;
v___y_1562_ = v___y_1598_;
v___y_1563_ = v___y_1599_;
v___y_1564_ = v___y_1600_;
goto v___jp_1557_;
}
else
{
lean_object* v_a_1617_; lean_object* v_inheritedTraceOptions_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_a_1617_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1613_, 1);
v_inheritedTraceOptions_1618_ = lean_ctor_get(v___y_1599_, 13);
v___x_1619_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_1620_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1618_, v_options_1614_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_del_object(v___x_1611_);
v___y_1558_ = v_a_1617_;
v___y_1559_ = v___y_1595_;
v___y_1560_ = v___y_1596_;
v___y_1561_ = v___y_1597_;
v___y_1562_ = v___y_1598_;
v___y_1563_ = v___y_1599_;
v___y_1564_ = v___y_1600_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1621_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1);
lean_inc_ref(v_type_1549_);
v___x_1622_ = l_Lean_MessageData_ofExpr(v_type_1549_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 7);
lean_ctor_set(v___x_1611_, 1, v___x_1622_);
lean_ctor_set(v___x_1611_, 0, v___x_1621_);
v___x_1624_ = v___x_1611_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1625_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
lean_inc(v_a_1617_);
v___x_1627_ = lean_array_to_list(v_a_1617_);
v___x_1628_ = lean_box(0);
v___x_1629_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1627_, v___x_1628_);
v___x_1630_ = l_Lean_MessageData_ofList(v___x_1629_);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1626_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1591_, v___x_1631_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_dec_ref_known(v___x_1632_, 1);
v___y_1558_ = v_a_1617_;
v___y_1559_ = v___y_1595_;
v___y_1560_ = v___y_1596_;
v___y_1561_ = v___y_1597_;
v___y_1562_ = v___y_1598_;
v___y_1563_ = v___y_1599_;
v___y_1564_ = v___y_1600_;
goto v___jp_1557_;
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_a_1617_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1611_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
return v___x_1613_;
}
}
else
{
lean_object* v_val_1642_; lean_object* v___x_1644_; 
lean_del_object(v___x_1611_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_val_1642_ = lean_ctor_get(v_fst_1609_, 0);
lean_inc(v_val_1642_);
lean_dec_ref_known(v_fst_1609_, 1);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v_val_1642_);
v___x_1644_ = v___x_1607_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_val_1642_);
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
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1649_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1604_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1604_);
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
v___jp_1657_:
{
uint8_t v___x_1664_; 
v___x_1664_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_plan_1547_, v_type_1549_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_mk_empty_array_with_capacity(v___x_1665_);
lean_inc_ref(v_type_1549_);
v___x_1667_ = lean_array_push(v___x_1666_, v_type_1549_);
lean_inc(v_className_1545_);
v___x_1668_ = l_Lean_Meta_mkAppM(v_className_1545_, v___x_1667_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc_n(v_a_1669_, 2);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = l_Lean_Meta_SynthInstance_getInstances(v_a_1669_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v___x_1672_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1591_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; uint8_t v___x_1674_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = lean_unbox(v_a_1673_);
lean_dec(v_a_1673_);
if (v___x_1674_ == 0)
{
v___y_1593_ = v_a_1669_;
v___y_1594_ = v_a_1671_;
v___y_1595_ = v___y_1658_;
v___y_1596_ = v___y_1659_;
v___y_1597_ = v___y_1660_;
v___y_1598_ = v___y_1661_;
v___y_1599_ = v___y_1662_;
v___y_1600_ = v___y_1663_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1675_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5);
lean_inc(v_a_1669_);
v___x_1676_ = l_Lean_MessageData_ofExpr(v_a_1669_);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_array_get_size(v_a_1671_);
v___x_1681_ = l_Nat_reprFast(v___x_1680_);
v___x_1682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
v___x_1683_ = l_Lean_MessageData_ofFormat(v___x_1682_);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1679_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1591_, v___x_1684_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_dec_ref_known(v___x_1685_, 1);
v___y_1593_ = v_a_1669_;
v___y_1594_ = v_a_1671_;
v___y_1595_ = v___y_1658_;
v___y_1596_ = v___y_1659_;
v___y_1597_ = v___y_1660_;
v___y_1598_ = v___y_1661_;
v___y_1599_ = v___y_1662_;
v___y_1600_ = v___y_1663_;
goto v___jp_1592_;
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_a_1671_);
lean_dec(v_a_1669_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_a_1671_);
lean_dec(v_a_1669_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1694_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1672_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1672_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1669_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1702_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1670_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1670_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1710_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1668_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1668_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v___x_1718_; 
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_plan_1547_);
return v___x_1718_;
}
}
v___jp_1719_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1724_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___y_1723_, v___y_1721_);
v___x_1725_ = l_Lean_MessageData_ofList(v___x_1724_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___y_1722_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
lean_inc_ref(v_type_1549_);
v___x_1729_ = l_Lean_MessageData_ofExpr(v_type_1549_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1591_, v___x_1730_, v_a_1552_, v_a_1553_, v___y_1720_, v_a_1555_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_dec_ref_known(v___x_1731_, 1);
v___y_1658_ = v_a_1550_;
v___y_1659_ = v_a_1551_;
v___y_1660_ = v_a_1552_;
v___y_1661_ = v_a_1553_;
v___y_1662_ = v___y_1720_;
v___y_1663_ = v_a_1555_;
goto v___jp_1657_;
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref(v___y_1720_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
v___jp_1740_:
{
if (v___y_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_currRecDepth_1578_, v___x_1742_);
lean_inc_ref(v_inheritedTraceOptions_1590_);
lean_inc(v_cancelTk_x3f_1588_);
lean_inc(v_currMacroScope_1586_);
lean_inc(v_quotContext_1585_);
lean_inc(v_maxHeartbeats_1584_);
lean_inc(v_initHeartbeats_1583_);
lean_inc(v_openDecls_1582_);
lean_inc(v_currNamespace_1581_);
lean_inc(v_ref_1580_);
lean_inc(v_maxRecDepth_1579_);
lean_inc_ref(v_options_1577_);
lean_inc_ref(v_fileMap_1576_);
lean_inc_ref(v_fileName_1575_);
v___x_1744_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1744_, 0, v_fileName_1575_);
lean_ctor_set(v___x_1744_, 1, v_fileMap_1576_);
lean_ctor_set(v___x_1744_, 2, v_options_1577_);
lean_ctor_set(v___x_1744_, 3, v___x_1743_);
lean_ctor_set(v___x_1744_, 4, v_maxRecDepth_1579_);
lean_ctor_set(v___x_1744_, 5, v_ref_1580_);
lean_ctor_set(v___x_1744_, 6, v_currNamespace_1581_);
lean_ctor_set(v___x_1744_, 7, v_openDecls_1582_);
lean_ctor_set(v___x_1744_, 8, v_initHeartbeats_1583_);
lean_ctor_set(v___x_1744_, 9, v_maxHeartbeats_1584_);
lean_ctor_set(v___x_1744_, 10, v_quotContext_1585_);
lean_ctor_set(v___x_1744_, 11, v_currMacroScope_1586_);
lean_ctor_set(v___x_1744_, 12, v_cancelTk_x3f_1588_);
lean_ctor_set(v___x_1744_, 13, v_inheritedTraceOptions_1590_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*14, v_diag_1587_);
lean_ctor_set_uint8(v___x_1744_, sizeof(void*)*14 + 1, v_suppressElabErrors_1589_);
v___x_1745_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1591_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v___x_1744_, v_a_1555_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; uint8_t v___x_1747_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = lean_unbox(v_a_1746_);
lean_dec(v_a_1746_);
if (v___x_1747_ == 0)
{
v___y_1658_ = v_a_1550_;
v___y_1659_ = v_a_1551_;
v___y_1660_ = v_a_1552_;
v___y_1661_ = v_a_1553_;
v___y_1662_ = v___x_1744_;
v___y_1663_ = v_a_1555_;
goto v___jp_1657_;
}
else
{
lean_object* v_buckets_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_buckets_1748_ = lean_ctor_get(v_processing_1548_, 1);
v___x_1749_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9);
lean_inc_ref(v_plan_1547_);
v___x_1750_ = lean_array_to_list(v_plan_1547_);
v___x_1751_ = lean_box(0);
v___x_1752_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1750_, v___x_1751_);
v___x_1753_ = l_Lean_MessageData_ofList(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1749_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_array_get_size(v_buckets_1748_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_nat_dec_lt(v___x_1758_, v___x_1757_);
if (v___x_1759_ == 0)
{
v___y_1720_ = v___x_1744_;
v___y_1721_ = v___x_1751_;
v___y_1722_ = v___x_1756_;
v___y_1723_ = v___x_1751_;
goto v___jp_1719_;
}
else
{
size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_usize_of_nat(v___x_1757_);
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_buckets_1748_, v___x_1760_, v___x_1761_, v___x_1751_);
v___y_1720_ = v___x_1744_;
v___y_1721_ = v___x_1751_;
v___y_1722_ = v___x_1756_;
v___y_1723_ = v___x_1762_;
goto v___jp_1719_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref_known(v___x_1744_, 14);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1763_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1745_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1745_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v___x_1771_; 
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
lean_inc(v_ref_1580_);
v___x_1771_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_1580_);
return v___x_1771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(lean_object* v_processing_1776_, lean_object* v_className_1777_, lean_object* v_extraDeps_1778_, lean_object* v_as_1779_, size_t v_sz_1780_, size_t v_i_1781_, lean_object* v_b_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
uint8_t v___x_1790_; 
v___x_1790_ = lean_usize_dec_lt(v_i_1781_, v_sz_1780_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref(v_extraDeps_1778_);
lean_dec(v_className_1777_);
lean_dec_ref(v_processing_1776_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_b_1782_);
return v___x_1791_;
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_a_1792_ = lean_array_uget_borrowed(v_as_1779_, v_i_1781_);
v___x_1793_ = lean_box(0);
lean_inc_n(v_a_1792_, 2);
lean_inc_ref(v_processing_1776_);
v___x_1794_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v_processing_1776_, v_a_1792_, v___x_1793_);
lean_inc_ref(v_extraDeps_1778_);
lean_inc(v_className_1777_);
v___x_1795_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_1777_, v_extraDeps_1778_, v_b_1782_, v___x_1794_, v_a_1792_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; size_t v___x_1797_; size_t v___x_1798_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_i_1781_, v___x_1797_);
v_i_1781_ = v___x_1798_;
v_b_1782_ = v_a_1796_;
goto _start;
}
else
{
lean_dec_ref(v_extraDeps_1778_);
lean_dec(v_className_1777_);
lean_dec_ref(v_processing_1776_);
return v___x_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11___boxed(lean_object* v_processing_1800_, lean_object* v_className_1801_, lean_object* v_extraDeps_1802_, lean_object* v_as_1803_, lean_object* v_sz_1804_, lean_object* v_i_1805_, lean_object* v_b_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
size_t v_sz_boxed_1814_; size_t v_i_boxed_1815_; lean_object* v_res_1816_; 
v_sz_boxed_1814_ = lean_unbox_usize(v_sz_1804_);
lean_dec(v_sz_1804_);
v_i_boxed_1815_ = lean_unbox_usize(v_i_1805_);
lean_dec(v_i_1805_);
v_res_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_1800_, v_className_1801_, v_extraDeps_1802_, v_as_1803_, v_sz_boxed_1814_, v_i_boxed_1815_, v_b_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_as_1803_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___boxed(lean_object* v_className_1817_, lean_object* v_extraDeps_1818_, lean_object* v_plan_1819_, lean_object* v_processing_1820_, lean_object* v_a_1821_, lean_object* v_as_1822_, lean_object* v_sz_1823_, lean_object* v_i_1824_, lean_object* v_b_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
size_t v_sz_boxed_1833_; size_t v_i_boxed_1834_; lean_object* v_res_1835_; 
v_sz_boxed_1833_ = lean_unbox_usize(v_sz_1823_);
lean_dec(v_sz_1823_);
v_i_boxed_1834_ = lean_unbox_usize(v_i_1824_);
lean_dec(v_i_1824_);
v_res_1835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_1817_, v_extraDeps_1818_, v_plan_1819_, v_processing_1820_, v_a_1821_, v_as_1822_, v_sz_boxed_1833_, v_i_boxed_1834_, v_b_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec_ref(v_as_1822_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___boxed(lean_object* v_className_1836_, lean_object* v_extraDeps_1837_, lean_object* v_plan_1838_, lean_object* v_processing_1839_, lean_object* v_depTypes_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1836_, v_extraDeps_1837_, v_plan_1838_, v_processing_1839_, v_depTypes_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___boxed(lean_object* v_className_1849_, lean_object* v_extraDeps_1850_, lean_object* v_plan_1851_, lean_object* v_processing_1852_, lean_object* v_cls_1853_, lean_object* v_inst_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(v_className_1849_, v_extraDeps_1850_, v_plan_1851_, v_processing_1852_, v_cls_1853_, v_inst_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___boxed(lean_object* v_className_1863_, lean_object* v_extraDeps_1864_, lean_object* v_plan_1865_, lean_object* v_processing_1866_, lean_object* v_type_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_1863_, v_extraDeps_1864_, v_plan_1865_, v_processing_1866_, v_type_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(lean_object* v_e_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_e_1876_, v___y_1880_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___boxed(lean_object* v_e_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(v_e_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(lean_object* v_cls_1894_, lean_object* v_msg_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1894_, v_msg_1895_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___boxed(lean_object* v_cls_1904_, lean_object* v_msg_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(v_cls_1904_, v_msg_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8(lean_object* v_00_u03b2_1914_, lean_object* v_m_1915_, lean_object* v_a_1916_, lean_object* v_b_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v_m_1915_, v_a_1916_, v_b_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(lean_object* v_00_u03b2_1919_, lean_object* v_m_1920_, lean_object* v_a_1921_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(v_m_1920_, v_a_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___boxed(lean_object* v_00_u03b2_1923_, lean_object* v_m_1924_, lean_object* v_a_1925_){
_start:
{
uint8_t v_res_1926_; lean_object* v_r_1927_; 
v_res_1926_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(v_00_u03b2_1923_, v_m_1924_, v_a_1925_);
lean_dec_ref(v_a_1925_);
lean_dec_ref(v_m_1924_);
v_r_1927_ = lean_box(v_res_1926_);
return v_r_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(lean_object* v_00_u03b1_1928_, lean_object* v_msg_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v_msg_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___boxed(lean_object* v_00_u03b1_1938_, lean_object* v_msg_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(v_00_u03b1_1938_, v_msg_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(lean_object* v_00_u03b1_1948_, lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v_msg_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___boxed(lean_object* v_00_u03b1_1956_, lean_object* v_msg_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(v_00_u03b1_1956_, v_msg_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(lean_object* v___x_1964_, lean_object* v_fst_1965_, lean_object* v_range_1966_, lean_object* v_b_1967_, lean_object* v_i_1968_, lean_object* v_hs_1969_, lean_object* v_hl_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_1964_, v_fst_1965_, v_range_1966_, v_b_1967_, v_i_1968_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___boxed(lean_object* v___x_1979_, lean_object* v_fst_1980_, lean_object* v_range_1981_, lean_object* v_b_1982_, lean_object* v_i_1983_, lean_object* v_hs_1984_, lean_object* v_hl_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(v___x_1979_, v_fst_1980_, v_range_1981_, v_b_1982_, v_i_1983_, v_hs_1984_, v_hl_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec_ref(v_range_1981_);
lean_dec_ref(v_fst_1980_);
lean_dec_ref(v___x_1979_);
return v_res_1993_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(lean_object* v_00_u03b2_1994_, lean_object* v_a_1995_, lean_object* v_x_1996_){
_start:
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_1995_, v_x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1998_, lean_object* v_a_1999_, lean_object* v_x_2000_){
_start:
{
uint8_t v_res_2001_; lean_object* v_r_2002_; 
v_res_2001_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(v_00_u03b2_1998_, v_a_1999_, v_x_2000_);
lean_dec(v_x_2000_);
lean_dec_ref(v_a_1999_);
v_r_2002_ = lean_box(v_res_2001_);
return v_r_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11(lean_object* v_00_u03b2_2003_, lean_object* v_data_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(v_data_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(lean_object* v_msgData_2006_, lean_object* v_macroStack_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_msgData_2006_, v_macroStack_2007_, v___y_2012_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___boxed(lean_object* v_msgData_2016_, lean_object* v_macroStack_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(v_msgData_2016_, v_macroStack_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14(lean_object* v_00_u03b2_2026_, lean_object* v_i_2027_, lean_object* v_source_2028_, lean_object* v_target_2029_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(v_i_2027_, v_source_2028_, v_target_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26(lean_object* v_00_u03b2_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(v_x_2032_, v_x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_unsigned_to_nat(32u);
v___x_2036_ = lean_mk_empty_array_with_capacity(v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2038_ = ((size_t)5ULL);
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = lean_unsigned_to_nat(32u);
v___x_2041_ = lean_mk_empty_array_with_capacity(v___x_2040_);
v___x_2042_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0);
v___x_2043_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
lean_ctor_set(v___x_2043_, 1, v___x_2041_);
lean_ctor_set(v___x_2043_, 2, v___x_2039_);
lean_ctor_set(v___x_2043_, 3, v___x_2039_);
lean_ctor_set_usize(v___x_2043_, 4, v___x_2038_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v_traceState_2047_; lean_object* v_traces_2048_; lean_object* v___x_2049_; lean_object* v_traceState_2050_; lean_object* v_env_2051_; lean_object* v_nextMacroScope_2052_; lean_object* v_ngen_2053_; lean_object* v_auxDeclNGen_2054_; lean_object* v_cache_2055_; lean_object* v_messages_2056_; lean_object* v_infoState_2057_; lean_object* v_snapshotTasks_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2077_; 
v___x_2046_ = lean_st_ref_get(v___y_2044_);
v_traceState_2047_ = lean_ctor_get(v___x_2046_, 4);
lean_inc_ref(v_traceState_2047_);
lean_dec(v___x_2046_);
v_traces_2048_ = lean_ctor_get(v_traceState_2047_, 0);
lean_inc_ref(v_traces_2048_);
lean_dec_ref(v_traceState_2047_);
v___x_2049_ = lean_st_ref_take(v___y_2044_);
v_traceState_2050_ = lean_ctor_get(v___x_2049_, 4);
v_env_2051_ = lean_ctor_get(v___x_2049_, 0);
v_nextMacroScope_2052_ = lean_ctor_get(v___x_2049_, 1);
v_ngen_2053_ = lean_ctor_get(v___x_2049_, 2);
v_auxDeclNGen_2054_ = lean_ctor_get(v___x_2049_, 3);
v_cache_2055_ = lean_ctor_get(v___x_2049_, 5);
v_messages_2056_ = lean_ctor_get(v___x_2049_, 6);
v_infoState_2057_ = lean_ctor_get(v___x_2049_, 7);
v_snapshotTasks_2058_ = lean_ctor_get(v___x_2049_, 8);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2060_ = v___x_2049_;
v_isShared_2061_ = v_isSharedCheck_2077_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_snapshotTasks_2058_);
lean_inc(v_infoState_2057_);
lean_inc(v_messages_2056_);
lean_inc(v_cache_2055_);
lean_inc(v_traceState_2050_);
lean_inc(v_auxDeclNGen_2054_);
lean_inc(v_ngen_2053_);
lean_inc(v_nextMacroScope_2052_);
lean_inc(v_env_2051_);
lean_dec(v___x_2049_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2077_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
uint64_t v_tid_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2075_; 
v_tid_2062_ = lean_ctor_get_uint64(v_traceState_2050_, sizeof(void*)*1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_traceState_2050_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v_traceState_2050_, 0);
lean_dec(v_unused_2076_);
v___x_2064_ = v_traceState_2050_;
v_isShared_2065_ = v_isSharedCheck_2075_;
goto v_resetjp_2063_;
}
else
{
lean_dec(v_traceState_2050_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2075_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2066_);
lean_ctor_set_uint64(v_reuseFailAlloc_2074_, sizeof(void*)*1, v_tid_2062_);
v___x_2068_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2070_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v___x_2068_);
v___x_2070_ = v___x_2060_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_env_2051_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_nextMacroScope_2052_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_ngen_2053_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_auxDeclNGen_2054_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2073_, 5, v_cache_2055_);
lean_ctor_set(v_reuseFailAlloc_2073_, 6, v_messages_2056_);
lean_ctor_set(v_reuseFailAlloc_2073_, 7, v_infoState_2057_);
lean_ctor_set(v_reuseFailAlloc_2073_, 8, v_snapshotTasks_2058_);
v___x_2070_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_st_ref_set(v___y_2044_, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_traces_2048_);
return v___x_2072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___boxed(lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_2078_);
lean_dec(v___y_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___boxed(lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2096_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0));
v___x_2099_ = l_Lean_stringToMessageData(v___x_2098_);
return v___x_2099_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2));
v___x_2102_ = l_Lean_stringToMessageData(v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(lean_object* v_className_2103_, uint8_t v___x_2104_, lean_object* v_type_2105_, lean_object* v_r_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___y_2124_; 
v___x_2114_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1);
v___x_2115_ = l_Lean_MessageData_ofConstName(v_className_2103_, v___x_2104_);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = l_Lean_MessageData_ofExpr(v_type_2105_);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
if (lean_obj_tag(v_r_2106_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v_r_2106_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v_r_2106_, 1);
v___x_2128_ = l_Lean_Exception_toMessageData(v_a_2127_);
v___y_2124_ = v___x_2128_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2129_ = lean_ctor_get(v_r_2106_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v_r_2106_, 1);
v___x_2130_ = lean_array_to_list(v_a_2129_);
v___x_2131_ = lean_box(0);
v___x_2132_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_2130_, v___x_2131_);
v___x_2133_ = l_Lean_MessageData_ofList(v___x_2132_);
v___y_2124_ = v___x_2133_;
goto v___jp_2123_;
}
v___jp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2122_);
lean_ctor_set(v___x_2125_, 1, v___y_2124_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed(lean_object* v_className_2134_, lean_object* v___x_2135_, lean_object* v_type_2136_, lean_object* v_r_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
uint8_t v___x_9193__boxed_2145_; lean_object* v_res_2146_; 
v___x_9193__boxed_2145_ = lean_unbox(v___x_2135_);
v_res_2146_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(v_className_2134_, v___x_9193__boxed_2145_, v_type_2136_, v_r_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(lean_object* v_opts_2147_, lean_object* v_opt_2148_){
_start:
{
lean_object* v_name_2149_; lean_object* v_defValue_2150_; lean_object* v_map_2151_; lean_object* v___x_2152_; 
v_name_2149_ = lean_ctor_get(v_opt_2148_, 0);
v_defValue_2150_ = lean_ctor_get(v_opt_2148_, 1);
v_map_2151_ = lean_ctor_get(v_opts_2147_, 0);
v___x_2152_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2151_, v_name_2149_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_inc(v_defValue_2150_);
return v_defValue_2150_;
}
else
{
lean_object* v_val_2153_; 
v_val_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_val_2153_);
lean_dec_ref_known(v___x_2152_, 1);
if (lean_obj_tag(v_val_2153_) == 3)
{
lean_object* v_v_2154_; 
v_v_2154_ = lean_ctor_get(v_val_2153_, 0);
lean_inc(v_v_2154_);
lean_dec_ref_known(v_val_2153_, 1);
return v_v_2154_;
}
else
{
lean_dec(v_val_2153_);
lean_inc(v_defValue_2150_);
return v_defValue_2150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4___boxed(lean_object* v_opts_2155_, lean_object* v_opt_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2155_, v_opt_2156_);
lean_dec_ref(v_opt_2156_);
lean_dec_ref(v_opts_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(lean_object* v_x_2158_){
_start:
{
if (lean_obj_tag(v_x_2158_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
v_a_2160_ = lean_ctor_get(v_x_2158_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_x_2158_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v_x_2158_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v_x_2158_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set_tag(v___x_2162_, 1);
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_a_2168_ = lean_ctor_get(v_x_2158_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_x_2158_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v_x_2158_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v_x_2158_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set_tag(v___x_2170_, 0);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg___boxed(lean_object* v_x_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_x_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(lean_object* v_e_2179_){
_start:
{
if (lean_obj_tag(v_e_2179_) == 0)
{
uint8_t v___x_2180_; 
v___x_2180_ = 2;
return v___x_2180_;
}
else
{
uint8_t v___x_2181_; 
v___x_2181_ = 0;
return v___x_2181_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___boxed(lean_object* v_e_2182_){
_start:
{
uint8_t v_res_2183_; lean_object* v_r_2184_; 
v_res_2183_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_e_2182_);
lean_dec_ref(v_e_2182_);
v_r_2184_ = lean_box(v_res_2183_);
return v_r_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(size_t v_sz_2185_, size_t v_i_2186_, lean_object* v_bs_2187_){
_start:
{
uint8_t v___x_2188_; 
v___x_2188_ = lean_usize_dec_lt(v_i_2186_, v_sz_2185_);
if (v___x_2188_ == 0)
{
return v_bs_2187_;
}
else
{
lean_object* v_v_2189_; lean_object* v_msg_2190_; lean_object* v___x_2191_; lean_object* v_bs_x27_2192_; size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v_v_2189_ = lean_array_uget_borrowed(v_bs_2187_, v_i_2186_);
v_msg_2190_ = lean_ctor_get(v_v_2189_, 1);
lean_inc_ref(v_msg_2190_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v_bs_x27_2192_ = lean_array_uset(v_bs_2187_, v_i_2186_, v___x_2191_);
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2186_, v___x_2193_);
v___x_2195_ = lean_array_uset(v_bs_x27_2192_, v_i_2186_, v_msg_2190_);
v_i_2186_ = v___x_2194_;
v_bs_2187_ = v___x_2195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2197_, lean_object* v_i_2198_, lean_object* v_bs_2199_){
_start:
{
size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2197_);
lean_dec(v_sz_2197_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2198_);
lean_dec(v_i_2198_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(v_sz_boxed_2200_, v_i_boxed_2201_, v_bs_2199_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(lean_object* v_oldTraces_2203_, lean_object* v_data_2204_, lean_object* v_ref_2205_, lean_object* v_msg_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_fileName_2212_; lean_object* v_fileMap_2213_; lean_object* v_options_2214_; lean_object* v_currRecDepth_2215_; lean_object* v_maxRecDepth_2216_; lean_object* v_ref_2217_; lean_object* v_currNamespace_2218_; lean_object* v_openDecls_2219_; lean_object* v_initHeartbeats_2220_; lean_object* v_maxHeartbeats_2221_; lean_object* v_quotContext_2222_; lean_object* v_currMacroScope_2223_; uint8_t v_diag_2224_; lean_object* v_cancelTk_x3f_2225_; uint8_t v_suppressElabErrors_2226_; lean_object* v_inheritedTraceOptions_2227_; lean_object* v___x_2228_; lean_object* v_traceState_2229_; lean_object* v_traces_2230_; lean_object* v_ref_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; size_t v_sz_2234_; size_t v___x_2235_; lean_object* v___x_2236_; lean_object* v_msg_2237_; lean_object* v___x_2238_; lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2276_; 
v_fileName_2212_ = lean_ctor_get(v___y_2209_, 0);
v_fileMap_2213_ = lean_ctor_get(v___y_2209_, 1);
v_options_2214_ = lean_ctor_get(v___y_2209_, 2);
v_currRecDepth_2215_ = lean_ctor_get(v___y_2209_, 3);
v_maxRecDepth_2216_ = lean_ctor_get(v___y_2209_, 4);
v_ref_2217_ = lean_ctor_get(v___y_2209_, 5);
v_currNamespace_2218_ = lean_ctor_get(v___y_2209_, 6);
v_openDecls_2219_ = lean_ctor_get(v___y_2209_, 7);
v_initHeartbeats_2220_ = lean_ctor_get(v___y_2209_, 8);
v_maxHeartbeats_2221_ = lean_ctor_get(v___y_2209_, 9);
v_quotContext_2222_ = lean_ctor_get(v___y_2209_, 10);
v_currMacroScope_2223_ = lean_ctor_get(v___y_2209_, 11);
v_diag_2224_ = lean_ctor_get_uint8(v___y_2209_, sizeof(void*)*14);
v_cancelTk_x3f_2225_ = lean_ctor_get(v___y_2209_, 12);
v_suppressElabErrors_2226_ = lean_ctor_get_uint8(v___y_2209_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2227_ = lean_ctor_get(v___y_2209_, 13);
v___x_2228_ = lean_st_ref_get(v___y_2210_);
v_traceState_2229_ = lean_ctor_get(v___x_2228_, 4);
lean_inc_ref(v_traceState_2229_);
lean_dec(v___x_2228_);
v_traces_2230_ = lean_ctor_get(v_traceState_2229_, 0);
lean_inc_ref(v_traces_2230_);
lean_dec_ref(v_traceState_2229_);
v_ref_2231_ = l_Lean_replaceRef(v_ref_2205_, v_ref_2217_);
lean_inc_ref(v_inheritedTraceOptions_2227_);
lean_inc(v_cancelTk_x3f_2225_);
lean_inc(v_currMacroScope_2223_);
lean_inc(v_quotContext_2222_);
lean_inc(v_maxHeartbeats_2221_);
lean_inc(v_initHeartbeats_2220_);
lean_inc(v_openDecls_2219_);
lean_inc(v_currNamespace_2218_);
lean_inc(v_maxRecDepth_2216_);
lean_inc(v_currRecDepth_2215_);
lean_inc_ref(v_options_2214_);
lean_inc_ref(v_fileMap_2213_);
lean_inc_ref(v_fileName_2212_);
v___x_2232_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2232_, 0, v_fileName_2212_);
lean_ctor_set(v___x_2232_, 1, v_fileMap_2213_);
lean_ctor_set(v___x_2232_, 2, v_options_2214_);
lean_ctor_set(v___x_2232_, 3, v_currRecDepth_2215_);
lean_ctor_set(v___x_2232_, 4, v_maxRecDepth_2216_);
lean_ctor_set(v___x_2232_, 5, v_ref_2231_);
lean_ctor_set(v___x_2232_, 6, v_currNamespace_2218_);
lean_ctor_set(v___x_2232_, 7, v_openDecls_2219_);
lean_ctor_set(v___x_2232_, 8, v_initHeartbeats_2220_);
lean_ctor_set(v___x_2232_, 9, v_maxHeartbeats_2221_);
lean_ctor_set(v___x_2232_, 10, v_quotContext_2222_);
lean_ctor_set(v___x_2232_, 11, v_currMacroScope_2223_);
lean_ctor_set(v___x_2232_, 12, v_cancelTk_x3f_2225_);
lean_ctor_set(v___x_2232_, 13, v_inheritedTraceOptions_2227_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*14, v_diag_2224_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*14 + 1, v_suppressElabErrors_2226_);
v___x_2233_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2230_);
lean_dec_ref(v_traces_2230_);
v_sz_2234_ = lean_array_size(v___x_2233_);
v___x_2235_ = ((size_t)0ULL);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(v_sz_2234_, v___x_2235_, v___x_2233_);
v_msg_2237_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2237_, 0, v_data_2204_);
lean_ctor_set(v_msg_2237_, 1, v_msg_2206_);
lean_ctor_set(v_msg_2237_, 2, v___x_2236_);
v___x_2238_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_2237_, v___y_2207_, v___y_2208_, v___x_2232_, v___y_2210_);
lean_dec_ref_known(v___x_2232_, 14);
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2276_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2276_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v_traceState_2244_; lean_object* v_env_2245_; lean_object* v_nextMacroScope_2246_; lean_object* v_ngen_2247_; lean_object* v_auxDeclNGen_2248_; lean_object* v_cache_2249_; lean_object* v_messages_2250_; lean_object* v_infoState_2251_; lean_object* v_snapshotTasks_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2275_; 
v___x_2243_ = lean_st_ref_take(v___y_2210_);
v_traceState_2244_ = lean_ctor_get(v___x_2243_, 4);
v_env_2245_ = lean_ctor_get(v___x_2243_, 0);
v_nextMacroScope_2246_ = lean_ctor_get(v___x_2243_, 1);
v_ngen_2247_ = lean_ctor_get(v___x_2243_, 2);
v_auxDeclNGen_2248_ = lean_ctor_get(v___x_2243_, 3);
v_cache_2249_ = lean_ctor_get(v___x_2243_, 5);
v_messages_2250_ = lean_ctor_get(v___x_2243_, 6);
v_infoState_2251_ = lean_ctor_get(v___x_2243_, 7);
v_snapshotTasks_2252_ = lean_ctor_get(v___x_2243_, 8);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2254_ = v___x_2243_;
v_isShared_2255_ = v_isSharedCheck_2275_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_snapshotTasks_2252_);
lean_inc(v_infoState_2251_);
lean_inc(v_messages_2250_);
lean_inc(v_cache_2249_);
lean_inc(v_traceState_2244_);
lean_inc(v_auxDeclNGen_2248_);
lean_inc(v_ngen_2247_);
lean_inc(v_nextMacroScope_2246_);
lean_inc(v_env_2245_);
lean_dec(v___x_2243_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2275_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
uint64_t v_tid_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2273_; 
v_tid_2256_ = lean_ctor_get_uint64(v_traceState_2244_, sizeof(void*)*1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_traceState_2244_);
if (v_isSharedCheck_2273_ == 0)
{
lean_object* v_unused_2274_; 
v_unused_2274_ = lean_ctor_get(v_traceState_2244_, 0);
lean_dec(v_unused_2274_);
v___x_2258_ = v_traceState_2244_;
v_isShared_2259_ = v_isSharedCheck_2273_;
goto v_resetjp_2257_;
}
else
{
lean_dec(v_traceState_2244_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2273_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v_ref_2205_);
lean_ctor_set(v___x_2260_, 1, v_a_2239_);
v___x_2261_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2203_, v___x_2260_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2261_);
v___x_2263_ = v___x_2258_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2261_);
lean_ctor_set_uint64(v_reuseFailAlloc_2272_, sizeof(void*)*1, v_tid_2256_);
v___x_2263_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2265_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 4, v___x_2263_);
v___x_2265_ = v___x_2254_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_env_2245_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_nextMacroScope_2246_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_ngen_2247_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_auxDeclNGen_2248_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2271_, 5, v_cache_2249_);
lean_ctor_set(v_reuseFailAlloc_2271_, 6, v_messages_2250_);
lean_ctor_set(v_reuseFailAlloc_2271_, 7, v_infoState_2251_);
lean_ctor_set(v_reuseFailAlloc_2271_, 8, v_snapshotTasks_2252_);
v___x_2265_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2266_ = lean_st_ref_set(v___y_2210_, v___x_2265_);
v___x_2267_ = lean_box(0);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2267_);
v___x_2269_ = v___x_2241_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg___boxed(lean_object* v_oldTraces_2277_, lean_object* v_data_2278_, lean_object* v_ref_2279_, lean_object* v_msg_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2277_, v_data_2278_, v_ref_2279_, v_msg_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2286_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2290_; double v___x_2291_; 
v___x_2290_ = lean_unsigned_to_nat(1000u);
v___x_2291_ = lean_float_of_nat(v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(lean_object* v_cls_2292_, uint8_t v_collapsed_2293_, lean_object* v_tag_2294_, lean_object* v_opts_2295_, uint8_t v_clsEnabled_2296_, lean_object* v_oldTraces_2297_, lean_object* v_msg_2298_, lean_object* v_resStartStop_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_fst_2307_; lean_object* v_snd_2308_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v_data_2312_; lean_object* v_fst_2323_; lean_object* v_snd_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; lean_object* v___y_2328_; lean_object* v_a_2329_; uint8_t v___y_2344_; double v___y_2375_; 
v_fst_2307_ = lean_ctor_get(v_resStartStop_2299_, 0);
lean_inc(v_fst_2307_);
v_snd_2308_ = lean_ctor_get(v_resStartStop_2299_, 1);
lean_inc(v_snd_2308_);
lean_dec_ref(v_resStartStop_2299_);
v_fst_2323_ = lean_ctor_get(v_snd_2308_, 0);
lean_inc(v_fst_2323_);
v_snd_2324_ = lean_ctor_get(v_snd_2308_, 1);
lean_inc(v_snd_2324_);
lean_dec(v_snd_2308_);
v___x_2325_ = l_Lean_trace_profiler;
v___x_2326_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_2295_, v___x_2325_);
if (v___x_2326_ == 0)
{
v___y_2344_ = v___x_2326_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2381_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_2295_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; double v___x_2384_; double v___x_2385_; double v___x_2386_; 
v___x_2382_ = l_Lean_trace_profiler_threshold;
v___x_2383_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2295_, v___x_2382_);
v___x_2384_ = lean_float_of_nat(v___x_2383_);
v___x_2385_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2);
v___x_2386_ = lean_float_div(v___x_2384_, v___x_2385_);
v___y_2375_ = v___x_2386_;
goto v___jp_2374_;
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; double v___x_2389_; 
v___x_2387_ = l_Lean_trace_profiler_threshold;
v___x_2388_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2295_, v___x_2387_);
v___x_2389_ = lean_float_of_nat(v___x_2388_);
v___y_2375_ = v___x_2389_;
goto v___jp_2374_;
}
}
v___jp_2309_:
{
lean_object* v___x_2313_; 
lean_inc(v___y_2311_);
v___x_2313_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2297_, v_data_2312_, v___y_2311_, v___y_2310_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v___x_2314_; 
lean_dec_ref_known(v___x_2313_, 1);
v___x_2314_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_fst_2307_);
return v___x_2314_;
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_fst_2307_);
v_a_2315_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2313_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2313_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
v___jp_2327_:
{
uint8_t v_result_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; double v___x_2333_; lean_object* v_data_2334_; 
v_result_2330_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_fst_2307_);
v___x_2331_ = lean_box(v_result_2330_);
v___x_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
v___x_2333_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_2294_);
lean_inc_ref(v___x_2332_);
lean_inc(v_cls_2292_);
v_data_2334_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2334_, 0, v_cls_2292_);
lean_ctor_set(v_data_2334_, 1, v___x_2332_);
lean_ctor_set(v_data_2334_, 2, v_tag_2294_);
lean_ctor_set_float(v_data_2334_, sizeof(void*)*3, v___x_2333_);
lean_ctor_set_float(v_data_2334_, sizeof(void*)*3 + 8, v___x_2333_);
lean_ctor_set_uint8(v_data_2334_, sizeof(void*)*3 + 16, v_collapsed_2293_);
if (v___x_2326_ == 0)
{
lean_dec_ref_known(v___x_2332_, 1);
lean_dec(v_snd_2324_);
lean_dec(v_fst_2323_);
lean_dec_ref(v_tag_2294_);
lean_dec(v_cls_2292_);
v___y_2310_ = v_a_2329_;
v___y_2311_ = v___y_2328_;
v_data_2312_ = v_data_2334_;
goto v___jp_2309_;
}
else
{
lean_object* v_data_2335_; double v___x_2336_; double v___x_2337_; 
lean_dec_ref_known(v_data_2334_, 3);
v_data_2335_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2335_, 0, v_cls_2292_);
lean_ctor_set(v_data_2335_, 1, v___x_2332_);
lean_ctor_set(v_data_2335_, 2, v_tag_2294_);
v___x_2336_ = lean_unbox_float(v_fst_2323_);
lean_dec(v_fst_2323_);
lean_ctor_set_float(v_data_2335_, sizeof(void*)*3, v___x_2336_);
v___x_2337_ = lean_unbox_float(v_snd_2324_);
lean_dec(v_snd_2324_);
lean_ctor_set_float(v_data_2335_, sizeof(void*)*3 + 8, v___x_2337_);
lean_ctor_set_uint8(v_data_2335_, sizeof(void*)*3 + 16, v_collapsed_2293_);
v___y_2310_ = v_a_2329_;
v___y_2311_ = v___y_2328_;
v_data_2312_ = v_data_2335_;
goto v___jp_2309_;
}
}
v___jp_2338_:
{
lean_object* v_ref_2339_; lean_object* v___x_2340_; 
v_ref_2339_ = lean_ctor_get(v___y_2304_, 5);
lean_inc(v___y_2305_);
lean_inc_ref(v___y_2304_);
lean_inc(v___y_2303_);
lean_inc_ref(v___y_2302_);
lean_inc(v___y_2301_);
lean_inc_ref(v___y_2300_);
lean_inc(v_fst_2307_);
v___x_2340_ = lean_apply_8(v_msg_2298_, v_fst_2307_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, lean_box(0));
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___y_2328_ = v_ref_2339_;
v_a_2329_ = v_a_2341_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2342_; 
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1);
v___y_2328_ = v_ref_2339_;
v_a_2329_ = v___x_2342_;
goto v___jp_2327_;
}
}
v___jp_2343_:
{
if (v_clsEnabled_2296_ == 0)
{
if (v___y_2344_ == 0)
{
lean_object* v___x_2345_; lean_object* v_traceState_2346_; lean_object* v_env_2347_; lean_object* v_nextMacroScope_2348_; lean_object* v_ngen_2349_; lean_object* v_auxDeclNGen_2350_; lean_object* v_cache_2351_; lean_object* v_messages_2352_; lean_object* v_infoState_2353_; lean_object* v_snapshotTasks_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_snd_2324_);
lean_dec(v_fst_2323_);
lean_dec_ref(v_msg_2298_);
lean_dec_ref(v_tag_2294_);
lean_dec(v_cls_2292_);
v___x_2345_ = lean_st_ref_take(v___y_2305_);
v_traceState_2346_ = lean_ctor_get(v___x_2345_, 4);
v_env_2347_ = lean_ctor_get(v___x_2345_, 0);
v_nextMacroScope_2348_ = lean_ctor_get(v___x_2345_, 1);
v_ngen_2349_ = lean_ctor_get(v___x_2345_, 2);
v_auxDeclNGen_2350_ = lean_ctor_get(v___x_2345_, 3);
v_cache_2351_ = lean_ctor_get(v___x_2345_, 5);
v_messages_2352_ = lean_ctor_get(v___x_2345_, 6);
v_infoState_2353_ = lean_ctor_get(v___x_2345_, 7);
v_snapshotTasks_2354_ = lean_ctor_get(v___x_2345_, 8);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2356_ = v___x_2345_;
v_isShared_2357_ = v_isSharedCheck_2373_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_snapshotTasks_2354_);
lean_inc(v_infoState_2353_);
lean_inc(v_messages_2352_);
lean_inc(v_cache_2351_);
lean_inc(v_traceState_2346_);
lean_inc(v_auxDeclNGen_2350_);
lean_inc(v_ngen_2349_);
lean_inc(v_nextMacroScope_2348_);
lean_inc(v_env_2347_);
lean_dec(v___x_2345_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2373_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
uint64_t v_tid_2358_; lean_object* v_traces_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2372_; 
v_tid_2358_ = lean_ctor_get_uint64(v_traceState_2346_, sizeof(void*)*1);
v_traces_2359_ = lean_ctor_get(v_traceState_2346_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_traceState_2346_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2361_ = v_traceState_2346_;
v_isShared_2362_ = v_isSharedCheck_2372_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_traces_2359_);
lean_dec(v_traceState_2346_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2372_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2297_, v_traces_2359_);
lean_dec_ref(v_traces_2359_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2363_);
v___x_2365_ = v___x_2361_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2363_);
lean_ctor_set_uint64(v_reuseFailAlloc_2371_, sizeof(void*)*1, v_tid_2358_);
v___x_2365_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 4, v___x_2365_);
v___x_2367_ = v___x_2356_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_env_2347_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_nextMacroScope_2348_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_ngen_2349_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_auxDeclNGen_2350_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2370_, 5, v_cache_2351_);
lean_ctor_set(v_reuseFailAlloc_2370_, 6, v_messages_2352_);
lean_ctor_set(v_reuseFailAlloc_2370_, 7, v_infoState_2353_);
lean_ctor_set(v_reuseFailAlloc_2370_, 8, v_snapshotTasks_2354_);
v___x_2367_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_st_ref_set(v___y_2305_, v___x_2367_);
v___x_2369_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_fst_2307_);
return v___x_2369_;
}
}
}
}
}
else
{
goto v___jp_2338_;
}
}
else
{
goto v___jp_2338_;
}
}
v___jp_2374_:
{
double v___x_2376_; double v___x_2377_; double v___x_2378_; uint8_t v___x_2379_; 
v___x_2376_ = lean_unbox_float(v_snd_2324_);
v___x_2377_ = lean_unbox_float(v_fst_2323_);
v___x_2378_ = lean_float_sub(v___x_2376_, v___x_2377_);
v___x_2379_ = lean_float_decLt(v___y_2375_, v___x_2378_);
v___y_2344_ = v___x_2379_;
goto v___jp_2343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___boxed(lean_object* v_cls_2390_, lean_object* v_collapsed_2391_, lean_object* v_tag_2392_, lean_object* v_opts_2393_, lean_object* v_clsEnabled_2394_, lean_object* v_oldTraces_2395_, lean_object* v_msg_2396_, lean_object* v_resStartStop_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v_collapsed_boxed_2405_; uint8_t v_clsEnabled_boxed_2406_; lean_object* v_res_2407_; 
v_collapsed_boxed_2405_ = lean_unbox(v_collapsed_2391_);
v_clsEnabled_boxed_2406_ = lean_unbox(v_clsEnabled_2394_);
v_res_2407_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v_cls_2390_, v_collapsed_boxed_2405_, v_tag_2392_, v_opts_2393_, v_clsEnabled_boxed_2406_, v_oldTraces_2395_, v_msg_2396_, v_resStartStop_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec_ref(v_opts_2393_);
return v_res_2407_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_unsigned_to_nat(16u);
v___x_2410_ = lean_mk_array(v___x_2409_, v___x_2408_);
return v___x_2410_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0);
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v___x_2411_);
return v___x_2413_;
}
}
static double _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2(void){
_start:
{
lean_object* v___x_2414_; double v___x_2415_; 
v___x_2414_ = lean_unsigned_to_nat(1000000000u);
v___x_2415_ = lean_float_of_nat(v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(lean_object* v_className_2416_, lean_object* v_type_2417_, lean_object* v_extraDeps_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_options_2426_; lean_object* v_inheritedTraceOptions_2427_; uint8_t v_hasTrace_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_options_2426_ = lean_ctor_get(v_a_2423_, 2);
v_inheritedTraceOptions_2427_ = lean_ctor_get(v_a_2423_, 13);
v_hasTrace_2428_ = lean_ctor_get_uint8(v_options_2426_, sizeof(void*)*1);
v___x_2429_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v___x_2430_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1);
v___x_2431_ = lean_box(0);
lean_inc_ref(v_type_2417_);
v___x_2432_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v___x_2430_, v_type_2417_, v___x_2431_);
v___x_2433_ = lean_bool_not(v_hasTrace_2428_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; lean_object* v___x_2438_; lean_object* v___y_2440_; uint8_t v___y_2441_; lean_object* v___y_2442_; lean_object* v_a_2443_; lean_object* v___y_2456_; uint8_t v___y_2457_; lean_object* v___y_2458_; lean_object* v_a_2459_; uint8_t v___y_2469_; uint8_t v_a_2511_; 
v___x_2434_ = lean_box(v___x_2433_);
lean_inc_ref(v_type_2417_);
lean_inc(v_className_2416_);
v___f_2435_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2435_, 0, v_className_2416_);
lean_closure_set(v___f_2435_, 1, v___x_2434_);
lean_closure_set(v___f_2435_, 2, v_type_2417_);
v___x_2436_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2437_ = 1;
v___x_2438_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
if (v_hasTrace_2428_ == 0)
{
v_a_2511_ = v_hasTrace_2428_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2516_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2427_, v_options_2426_, v___x_2515_);
if (v___x_2516_ == 0)
{
v_a_2511_ = v___x_2516_;
goto v___jp_2510_;
}
else
{
v___y_2469_ = v___x_2516_;
goto v___jp_2468_;
}
}
v___jp_2439_:
{
lean_object* v___x_2444_; double v___x_2445_; double v___x_2446_; double v___x_2447_; double v___x_2448_; double v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2444_ = lean_io_mono_nanos_now();
v___x_2445_ = lean_float_of_nat(v___y_2442_);
v___x_2446_ = lean_float_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2);
v___x_2447_ = lean_float_div(v___x_2445_, v___x_2446_);
v___x_2448_ = lean_float_of_nat(v___x_2444_);
v___x_2449_ = lean_float_div(v___x_2448_, v___x_2446_);
v___x_2450_ = lean_box_float(v___x_2447_);
v___x_2451_ = lean_box_float(v___x_2449_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_a_2443_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_2436_, v___x_2437_, v___x_2438_, v_options_2426_, v___y_2441_, v___y_2440_, v___f_2435_, v___x_2453_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2454_;
}
v___jp_2455_:
{
lean_object* v___x_2460_; double v___x_2461_; double v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2460_ = lean_io_get_num_heartbeats();
v___x_2461_ = lean_float_of_nat(v___y_2458_);
v___x_2462_ = lean_float_of_nat(v___x_2460_);
v___x_2463_ = lean_box_float(v___x_2461_);
v___x_2464_ = lean_box_float(v___x_2462_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_a_2459_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_2436_, v___x_2437_, v___x_2438_, v_options_2426_, v___y_2457_, v___y_2456_, v___f_2435_, v___x_2466_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2467_;
}
v___jp_2468_:
{
lean_object* v___x_2470_; lean_object* v_a_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2470_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v_a_2424_);
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2473_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_2426_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_io_mono_nanos_now();
v___x_2475_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2416_, v_extraDeps_2418_, v___x_2429_, v___x_2432_, v_type_2417_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
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
v___y_2440_ = v_a_2471_;
v___y_2441_ = v___y_2469_;
v___y_2442_ = v___x_2474_;
v_a_2443_ = v___x_2481_;
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
v___y_2440_ = v_a_2471_;
v___y_2441_ = v___y_2469_;
v___y_2442_ = v___x_2474_;
v_a_2443_ = v___x_2489_;
goto v___jp_2439_;
}
}
}
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_io_get_num_heartbeats();
v___x_2493_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2416_, v_extraDeps_2418_, v___x_2429_, v___x_2432_, v_type_2417_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set_tag(v___x_2496_, 1);
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
v___y_2456_ = v_a_2471_;
v___y_2457_ = v___y_2469_;
v___y_2458_ = v___x_2492_;
v_a_2459_ = v___x_2499_;
goto v___jp_2455_;
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v_a_2502_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2493_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2493_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 0);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
v___y_2456_ = v_a_2471_;
v___y_2457_ = v___y_2469_;
v___y_2458_ = v___x_2492_;
v_a_2459_ = v___x_2507_;
goto v___jp_2455_;
}
}
}
}
}
v___jp_2510_:
{
lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2512_ = l_Lean_trace_profiler;
v___x_2513_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_2426_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; 
lean_dec_ref(v___f_2435_);
v___x_2514_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2416_, v_extraDeps_2418_, v___x_2429_, v___x_2432_, v_type_2417_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2514_;
}
else
{
v___y_2469_ = v_a_2511_;
goto v___jp_2468_;
}
}
}
else
{
lean_object* v___x_2517_; 
v___x_2517_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2416_, v_extraDeps_2418_, v___x_2429_, v___x_2432_, v_type_2417_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed(lean_object* v_className_2518_, lean_object* v_type_2519_, lean_object* v_extraDeps_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(v_className_2518_, v_type_2519_, v_extraDeps_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(lean_object* v_00_u03b1_2529_, lean_object* v_x_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_x_2530_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2539_, lean_object* v_x_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(v_00_u03b1_2539_, v_x_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(lean_object* v_oldTraces_2549_, lean_object* v_data_2550_, lean_object* v_ref_2551_, lean_object* v_msg_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2549_, v_data_2550_, v_ref_2551_, v_msg_2552_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___boxed(lean_object* v_oldTraces_2561_, lean_object* v_data_2562_, lean_object* v_ref_2563_, lean_object* v_msg_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(v_oldTraces_2561_, v_data_2562_, v_ref_2563_, v_msg_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2572_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2573_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
return v___x_2577_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
v___x_2579_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
lean_ctor_set(v___x_2579_, 2, v___x_2578_);
lean_ctor_set(v___x_2579_, 3, v___x_2578_);
lean_ctor_set(v___x_2579_, 4, v___x_2578_);
lean_ctor_set(v___x_2579_, 5, v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(lean_object* v_env_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; lean_object* v_nextMacroScope_2585_; lean_object* v_ngen_2586_; lean_object* v_auxDeclNGen_2587_; lean_object* v_traceState_2588_; lean_object* v_messages_2589_; lean_object* v_infoState_2590_; lean_object* v_snapshotTasks_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2617_; 
v___x_2584_ = lean_st_ref_take(v___y_2582_);
v_nextMacroScope_2585_ = lean_ctor_get(v___x_2584_, 1);
v_ngen_2586_ = lean_ctor_get(v___x_2584_, 2);
v_auxDeclNGen_2587_ = lean_ctor_get(v___x_2584_, 3);
v_traceState_2588_ = lean_ctor_get(v___x_2584_, 4);
v_messages_2589_ = lean_ctor_get(v___x_2584_, 6);
v_infoState_2590_ = lean_ctor_get(v___x_2584_, 7);
v_snapshotTasks_2591_ = lean_ctor_get(v___x_2584_, 8);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; lean_object* v_unused_2619_; 
v_unused_2618_ = lean_ctor_get(v___x_2584_, 5);
lean_dec(v_unused_2618_);
v_unused_2619_ = lean_ctor_get(v___x_2584_, 0);
lean_dec(v_unused_2619_);
v___x_2593_ = v___x_2584_;
v_isShared_2594_ = v_isSharedCheck_2617_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_snapshotTasks_2591_);
lean_inc(v_infoState_2590_);
lean_inc(v_messages_2589_);
lean_inc(v_traceState_2588_);
lean_inc(v_auxDeclNGen_2587_);
lean_inc(v_ngen_2586_);
lean_inc(v_nextMacroScope_2585_);
lean_dec(v___x_2584_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2617_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 5, v___x_2595_);
lean_ctor_set(v___x_2593_, 0, v_env_2580_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_env_2580_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_nextMacroScope_2585_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_ngen_2586_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_auxDeclNGen_2587_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_traceState_2588_);
lean_ctor_set(v_reuseFailAlloc_2616_, 5, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2616_, 6, v_messages_2589_);
lean_ctor_set(v_reuseFailAlloc_2616_, 7, v_infoState_2590_);
lean_ctor_set(v_reuseFailAlloc_2616_, 8, v_snapshotTasks_2591_);
v___x_2597_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v_mctx_2600_; lean_object* v_zetaDeltaFVarIds_2601_; lean_object* v_postponed_2602_; lean_object* v_diag_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2614_; 
v___x_2598_ = lean_st_ref_set(v___y_2582_, v___x_2597_);
v___x_2599_ = lean_st_ref_take(v___y_2581_);
v_mctx_2600_ = lean_ctor_get(v___x_2599_, 0);
v_zetaDeltaFVarIds_2601_ = lean_ctor_get(v___x_2599_, 2);
v_postponed_2602_ = lean_ctor_get(v___x_2599_, 3);
v_diag_2603_ = lean_ctor_get(v___x_2599_, 4);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2599_, 1);
lean_dec(v_unused_2615_);
v___x_2605_ = v___x_2599_;
v_isShared_2606_ = v_isSharedCheck_2614_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_diag_2603_);
lean_inc(v_postponed_2602_);
lean_inc(v_zetaDeltaFVarIds_2601_);
lean_inc(v_mctx_2600_);
lean_dec(v___x_2599_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2614_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2607_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 1, v___x_2607_);
v___x_2609_ = v___x_2605_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_mctx_2600_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_zetaDeltaFVarIds_2601_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_postponed_2602_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_diag_2603_);
v___x_2609_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_st_ref_set(v___y_2581_, v___x_2609_);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___boxed(lean_object* v_env_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v_env_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec(v___y_2621_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(lean_object* v_env_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v_env_2625_, v___y_2629_, v___y_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___boxed(lean_object* v_env_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(v_env_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2642_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0));
v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(lean_object* v_mkCmd_2646_, lean_object* v_a_2647_, lean_object* v___x_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_inc(v___y_2652_);
lean_inc_ref(v___y_2651_);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc_ref(v_a_2647_);
v___x_2656_ = lean_apply_5(v_mkCmd_2646_, v_a_2647_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
v___x_2657_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_2656_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2648_);
lean_dec_ref(v_a_2647_);
return v___x_2657_;
}
else
{
lean_object* v_a_2658_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; uint8_t v___y_2684_; uint8_t v___x_2707_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
v___x_2707_ = l_Lean_Exception_isInterrupt(v_a_2658_);
if (v___x_2707_ == 0)
{
uint8_t v___x_2708_; 
lean_inc(v_a_2658_);
v___x_2708_ = l_Lean_Exception_isRuntime(v_a_2658_);
v___y_2684_ = v___x_2708_;
goto v___jp_2683_;
}
else
{
v___y_2684_ = v___x_2707_;
goto v___jp_2683_;
}
v___jp_2659_:
{
lean_object* v___x_2666_; 
lean_dec_ref(v___y_2660_);
v___x_2666_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v___x_2648_, v___y_2663_, v___y_2665_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2674_);
v___x_2668_ = v___x_2666_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_dec(v___x_2666_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 1);
lean_ctor_set(v___x_2668_, 0, v_a_2658_);
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2658_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2658_);
v_a_2675_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2666_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2666_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
v___jp_2683_:
{
if (v___y_2684_ == 0)
{
lean_object* v_options_2685_; uint8_t v_hasTrace_2686_; 
lean_dec_ref_known(v___x_2657_, 1);
v_options_2685_ = lean_ctor_get(v___y_2653_, 2);
v_hasTrace_2686_ = lean_ctor_get_uint8(v_options_2685_, sizeof(void*)*1);
if (v_hasTrace_2686_ == 0)
{
lean_dec_ref(v_a_2647_);
v___y_2660_ = v___y_2649_;
v___y_2661_ = v___y_2650_;
v___y_2662_ = v___y_2651_;
v___y_2663_ = v___y_2652_;
v___y_2664_ = v___y_2653_;
v___y_2665_ = v___y_2654_;
goto v___jp_2659_;
}
else
{
lean_object* v_inheritedTraceOptions_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v_inheritedTraceOptions_2687_ = lean_ctor_get(v___y_2653_, 13);
v___x_2688_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2689_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2690_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2687_, v_options_2685_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_dec_ref(v_a_2647_);
v___y_2660_ = v___y_2649_;
v___y_2661_ = v___y_2650_;
v___y_2662_ = v___y_2651_;
v___y_2663_ = v___y_2652_;
v___y_2664_ = v___y_2653_;
v___y_2665_ = v___y_2654_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2691_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1);
v___x_2692_ = l_Lean_MessageData_ofExpr(v_a_2647_);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
lean_inc(v_a_2658_);
v___x_2696_ = l_Lean_Exception_toMessageData(v_a_2658_);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v___x_2688_, v___x_2697_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_dec_ref_known(v___x_2698_, 1);
v___y_2660_ = v___y_2649_;
v___y_2661_ = v___y_2650_;
v___y_2662_ = v___y_2651_;
v___y_2663_ = v___y_2652_;
v___y_2664_ = v___y_2653_;
v___y_2665_ = v___y_2654_;
goto v___jp_2659_;
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_a_2658_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2648_);
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2658_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___x_2648_);
lean_dec_ref(v_a_2647_);
return v___x_2657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed(lean_object* v_mkCmd_2709_, lean_object* v_a_2710_, lean_object* v___x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(v_mkCmd_2709_, v_a_2710_, v___x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
return v_res_2719_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
lean_ctor_set(v___x_2725_, 2, v___x_2724_);
lean_ctor_set(v___x_2725_, 3, v___x_2724_);
lean_ctor_set(v___x_2725_, 4, v___x_2723_);
lean_ctor_set(v___x_2725_, 5, v___x_2723_);
lean_ctor_set(v___x_2725_, 6, v___x_2723_);
lean_ctor_set(v___x_2725_, 7, v___x_2723_);
lean_ctor_set(v___x_2725_, 8, v___x_2723_);
lean_ctor_set(v___x_2725_, 9, v___x_2723_);
return v___x_2725_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_unsigned_to_nat(32u);
v___x_2727_ = lean_mk_empty_array_with_capacity(v___x_2726_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
return v___x_2728_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2729_ = ((size_t)5ULL);
v___x_2730_ = lean_unsigned_to_nat(0u);
v___x_2731_ = lean_unsigned_to_nat(32u);
v___x_2732_ = lean_mk_empty_array_with_capacity(v___x_2731_);
v___x_2733_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3);
v___x_2734_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
lean_ctor_set(v___x_2734_, 1, v___x_2732_);
lean_ctor_set(v___x_2734_, 2, v___x_2730_);
lean_ctor_set(v___x_2734_, 3, v___x_2730_);
lean_ctor_set_usize(v___x_2734_, 4, v___x_2729_);
return v___x_2734_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2735_ = lean_box(1);
v___x_2736_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4);
v___x_2737_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
v___x_2738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v___x_2736_);
lean_ctor_set(v___x_2738_, 2, v___x_2735_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(lean_object* v_msgData_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; lean_object* v_env_2743_; lean_object* v___x_2744_; lean_object* v_scopes_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v_opts_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2742_ = lean_st_ref_get(v___y_2740_);
v_env_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc_ref(v_env_2743_);
lean_dec(v___x_2742_);
v___x_2744_ = lean_st_ref_get(v___y_2740_);
v_scopes_2745_ = lean_ctor_get(v___x_2744_, 2);
lean_inc(v_scopes_2745_);
lean_dec(v___x_2744_);
v___x_2746_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2747_ = l_List_head_x21___redArg(v___x_2746_, v_scopes_2745_);
lean_dec(v_scopes_2745_);
v_opts_2748_ = lean_ctor_get(v___x_2747_, 1);
lean_inc_ref(v_opts_2748_);
lean_dec(v___x_2747_);
v___x_2749_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2);
v___x_2750_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5);
v___x_2751_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2751_, 0, v_env_2743_);
lean_ctor_set(v___x_2751_, 1, v___x_2749_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
lean_ctor_set(v___x_2751_, 3, v_opts_2748_);
v___x_2752_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v_msgData_2739_);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msgData_2754_, v___y_2755_);
lean_dec(v___y_2755_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(lean_object* v_cls_2758_, lean_object* v_msg_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_Elab_Command_getRef___redArg(v___y_2760_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2812_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msg_2759_, v___y_2761_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2812_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2812_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v_traceState_2771_; lean_object* v_env_2772_; lean_object* v_messages_2773_; lean_object* v_scopes_2774_; lean_object* v_usedQuotCtxts_2775_; lean_object* v_nextMacroScope_2776_; lean_object* v_maxRecDepth_2777_; lean_object* v_ngen_2778_; lean_object* v_auxDeclNGen_2779_; lean_object* v_infoState_2780_; lean_object* v_snapshotTasks_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2811_; 
v___x_2770_ = lean_st_ref_take(v___y_2761_);
v_traceState_2771_ = lean_ctor_get(v___x_2770_, 9);
v_env_2772_ = lean_ctor_get(v___x_2770_, 0);
v_messages_2773_ = lean_ctor_get(v___x_2770_, 1);
v_scopes_2774_ = lean_ctor_get(v___x_2770_, 2);
v_usedQuotCtxts_2775_ = lean_ctor_get(v___x_2770_, 3);
v_nextMacroScope_2776_ = lean_ctor_get(v___x_2770_, 4);
v_maxRecDepth_2777_ = lean_ctor_get(v___x_2770_, 5);
v_ngen_2778_ = lean_ctor_get(v___x_2770_, 6);
v_auxDeclNGen_2779_ = lean_ctor_get(v___x_2770_, 7);
v_infoState_2780_ = lean_ctor_get(v___x_2770_, 8);
v_snapshotTasks_2781_ = lean_ctor_get(v___x_2770_, 10);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2783_ = v___x_2770_;
v_isShared_2784_ = v_isSharedCheck_2811_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_snapshotTasks_2781_);
lean_inc(v_traceState_2771_);
lean_inc(v_infoState_2780_);
lean_inc(v_auxDeclNGen_2779_);
lean_inc(v_ngen_2778_);
lean_inc(v_maxRecDepth_2777_);
lean_inc(v_nextMacroScope_2776_);
lean_inc(v_usedQuotCtxts_2775_);
lean_inc(v_scopes_2774_);
lean_inc(v_messages_2773_);
lean_inc(v_env_2772_);
lean_dec(v___x_2770_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2811_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
uint64_t v_tid_2785_; lean_object* v_traces_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2810_; 
v_tid_2785_ = lean_ctor_get_uint64(v_traceState_2771_, sizeof(void*)*1);
v_traces_2786_ = lean_ctor_get(v_traceState_2771_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_traceState_2771_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2788_ = v_traceState_2771_;
v_isShared_2789_ = v_isSharedCheck_2810_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_traces_2786_);
lean_dec(v_traceState_2771_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2810_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; double v___x_2791_; uint8_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2790_ = lean_box(0);
v___x_2791_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
v___x_2792_ = 0;
v___x_2793_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_2794_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2794_, 0, v_cls_2758_);
lean_ctor_set(v___x_2794_, 1, v___x_2790_);
lean_ctor_set(v___x_2794_, 2, v___x_2793_);
lean_ctor_set_float(v___x_2794_, sizeof(void*)*3, v___x_2791_);
lean_ctor_set_float(v___x_2794_, sizeof(void*)*3 + 8, v___x_2791_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*3 + 16, v___x_2792_);
v___x_2795_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1));
v___x_2796_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v_a_2766_);
lean_ctor_set(v___x_2796_, 2, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_a_2764_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = l_Lean_PersistentArray_push___redArg(v_traces_2786_, v___x_2797_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v___x_2798_);
v___x_2800_ = v___x_2788_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2798_);
lean_ctor_set_uint64(v_reuseFailAlloc_2809_, sizeof(void*)*1, v_tid_2785_);
v___x_2800_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2802_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 9, v___x_2800_);
v___x_2802_ = v___x_2783_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_env_2772_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_messages_2773_);
lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_scopes_2774_);
lean_ctor_set(v_reuseFailAlloc_2808_, 3, v_usedQuotCtxts_2775_);
lean_ctor_set(v_reuseFailAlloc_2808_, 4, v_nextMacroScope_2776_);
lean_ctor_set(v_reuseFailAlloc_2808_, 5, v_maxRecDepth_2777_);
lean_ctor_set(v_reuseFailAlloc_2808_, 6, v_ngen_2778_);
lean_ctor_set(v_reuseFailAlloc_2808_, 7, v_auxDeclNGen_2779_);
lean_ctor_set(v_reuseFailAlloc_2808_, 8, v_infoState_2780_);
lean_ctor_set(v_reuseFailAlloc_2808_, 9, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2808_, 10, v_snapshotTasks_2781_);
v___x_2802_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2803_ = lean_st_ref_set(v___y_2761_, v___x_2802_);
v___x_2804_ = lean_box(0);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2804_);
v___x_2806_ = v___x_2768_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v_msg_2759_);
lean_dec(v_cls_2758_);
v_a_2813_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2763_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2763_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1___boxed(lean_object* v_cls_2821_, lean_object* v_msg_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(v_cls_2821_, v_msg_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
return v_res_2826_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0));
v___x_2829_ = l_Lean_stringToMessageData(v___x_2828_);
return v___x_2829_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2));
v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4));
v___x_2835_ = l_Lean_stringToMessageData(v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(lean_object* v_mkCmd_2836_, lean_object* v___x_2837_, lean_object* v_className_2838_, lean_object* v_as_2839_, size_t v_sz_2840_, size_t v_i_2841_, lean_object* v_b_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_a_2847_; uint8_t v___x_2851_; 
v___x_2851_ = lean_usize_dec_lt(v_i_2841_, v_sz_2840_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
lean_dec(v_className_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v_mkCmd_2836_);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_b_2842_);
return v___x_2852_;
}
else
{
lean_object* v_a_2853_; lean_object* v___f_2854_; lean_object* v___x_2855_; 
v_a_2853_ = lean_array_uget_borrowed(v_as_2839_, v_i_2841_);
lean_inc_ref(v___x_2837_);
lean_inc(v_a_2853_);
lean_inc_ref(v_mkCmd_2836_);
v___f_2854_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2854_, 0, v_mkCmd_2836_);
lean_closure_set(v___f_2854_, 1, v_a_2853_);
lean_closure_set(v___f_2854_, 2, v___x_2837_);
v___x_2855_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2854_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = l_Lean_Elab_Command_elabCommand(v_a_2856_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_scopes_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v_opts_2864_; uint8_t v_hasTrace_2865_; lean_object* v___x_2866_; 
lean_dec_ref_known(v___x_2857_, 1);
v___x_2858_ = l_Lean_inheritedTraceOptions;
v___x_2859_ = lean_st_ref_get(v___x_2858_);
v___x_2860_ = lean_st_ref_get(v___y_2844_);
v_scopes_2861_ = lean_ctor_get(v___x_2860_, 2);
lean_inc(v_scopes_2861_);
lean_dec(v___x_2860_);
v___x_2862_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2863_ = l_List_head_x21___redArg(v___x_2862_, v_scopes_2861_);
lean_dec(v_scopes_2861_);
v_opts_2864_ = lean_ctor_get(v___x_2863_, 1);
lean_inc_ref(v_opts_2864_);
lean_dec(v___x_2863_);
v_hasTrace_2865_ = lean_ctor_get_uint8(v_opts_2864_, sizeof(void*)*1);
v___x_2866_ = lean_box(0);
if (v_hasTrace_2865_ == 0)
{
lean_dec_ref(v_opts_2864_);
lean_dec(v___x_2859_);
v_a_2847_ = v___x_2866_;
goto v___jp_2846_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2867_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2868_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2869_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2859_, v_opts_2864_, v___x_2868_);
lean_dec_ref(v_opts_2864_);
lean_dec(v___x_2859_);
if (v___x_2869_ == 0)
{
v_a_2847_ = v___x_2866_;
goto v___jp_2846_;
}
else
{
lean_object* v___x_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2870_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1);
v___x_2871_ = 0;
lean_inc(v_className_2838_);
v___x_2872_ = l_Lean_MessageData_ofConstName(v_className_2838_, v___x_2871_);
v___x_2873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2870_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3);
v___x_2875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
lean_inc(v_a_2853_);
v___x_2876_ = l_Lean_MessageData_ofExpr(v_a_2853_);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(v___x_2867_, v___x_2879_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_dec_ref_known(v___x_2880_, 1);
v_a_2847_ = v___x_2866_;
goto v___jp_2846_;
}
else
{
lean_dec(v_className_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v_mkCmd_2836_);
return v___x_2880_;
}
}
}
}
else
{
lean_dec(v_className_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v_mkCmd_2836_);
return v___x_2857_;
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_className_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v_mkCmd_2836_);
v_a_2881_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2855_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2855_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
v___jp_2846_:
{
size_t v___x_2848_; size_t v___x_2849_; 
v___x_2848_ = ((size_t)1ULL);
v___x_2849_ = lean_usize_add(v_i_2841_, v___x_2848_);
v_i_2841_ = v___x_2849_;
v_b_2842_ = v_a_2847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___boxed(lean_object* v_mkCmd_2889_, lean_object* v___x_2890_, lean_object* v_className_2891_, lean_object* v_as_2892_, lean_object* v_sz_2893_, lean_object* v_i_2894_, lean_object* v_b_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
size_t v_sz_boxed_2899_; size_t v_i_boxed_2900_; lean_object* v_res_2901_; 
v_sz_boxed_2899_ = lean_unbox_usize(v_sz_2893_);
lean_dec(v_sz_2893_);
v_i_boxed_2900_ = lean_unbox_usize(v_i_2894_);
lean_dec(v_i_2894_);
v_res_2901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(v_mkCmd_2889_, v___x_2890_, v_className_2891_, v_as_2892_, v_sz_boxed_2899_, v_i_boxed_2900_, v_b_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec_ref(v_as_2892_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_withClassInstDeps(lean_object* v_className_2902_, lean_object* v_type_2903_, lean_object* v_extraDeps_2904_, lean_object* v_mkCmd_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_inc(v_className_2902_);
v___x_2909_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed), 10, 3);
lean_closure_set(v___x_2909_, 0, v_className_2902_);
lean_closure_set(v___x_2909_, 1, v_type_2903_);
lean_closure_set(v___x_2909_, 2, v_extraDeps_2904_);
v___x_2910_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2909_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v_env_2913_; lean_object* v___x_2914_; size_t v_sz_2915_; size_t v___x_2916_; lean_object* v___x_2917_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2912_ = lean_st_ref_get(v_a_2907_);
v_env_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc_ref(v_env_2913_);
lean_dec(v___x_2912_);
v___x_2914_ = lean_box(0);
v_sz_2915_ = lean_array_size(v_a_2911_);
v___x_2916_ = ((size_t)0ULL);
v___x_2917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(v_mkCmd_2905_, v_env_2913_, v_className_2902_, v_a_2911_, v_sz_2915_, v___x_2916_, v___x_2914_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2911_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2924_ == 0)
{
lean_object* v_unused_2925_; 
v_unused_2925_ = lean_ctor_get(v___x_2917_, 0);
lean_dec(v_unused_2925_);
v___x_2919_ = v___x_2917_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v___x_2917_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2914_);
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2914_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
else
{
return v___x_2917_;
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v_mkCmd_2905_);
lean_dec(v_className_2902_);
v_a_2926_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2910_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2910_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_withClassInstDeps___boxed(lean_object* v_className_2934_, lean_object* v_type_2935_, lean_object* v_extraDeps_2936_, lean_object* v_mkCmd_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_Elab_ConfigEval_withClassInstDeps(v_className_2934_, v_type_2935_, v_extraDeps_2936_, v_mkCmd_2937_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(lean_object* v_msgData_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msgData_2942_, v___y_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___boxed(lean_object* v_msgData_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(v_msgData_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3017_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_3018_ = 0;
v___x_3019_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_));
v___x_3020_ = l_Lean_registerTraceClass(v___x_3017_, v___x_3018_, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2____boxed(lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_();
return v_res_3022_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
