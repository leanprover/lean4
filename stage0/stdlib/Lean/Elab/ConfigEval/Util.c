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
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
v_ref_27_ = lean_ctor_get(v___y_16_, 4);
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
v_ref_97_ = lean_ctor_get(v_a_75_, 4);
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
v_options_382_ = lean_ctor_get(v___y_379_, 1);
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
lean_object* v_toCold_386_; lean_object* v_inheritedTraceOptions_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_toCold_386_ = lean_ctor_get(v___y_379_, 0);
v_inheritedTraceOptions_387_ = lean_ctor_get(v_toCold_386_, 4);
v___x_388_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1));
v___x_389_ = l_Lean_Name_append(v___x_388_, v_cls_374_);
v___x_390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_387_, v_options_382_, v___x_389_);
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
uint8_t v___x_631_; 
v___x_631_ = l_Lean_Expr_hasMVar(v_e_628_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_e_628_);
return v___x_632_;
}
else
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
v___x_648_ = lean_st_ref_put(v___y_629_, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v_fst_636_);
return v___x_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg___boxed(lean_object* v_e_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_e_653_, v___y_654_);
lean_dec(v___y_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(size_t v_sz_657_, size_t v_i_658_, lean_object* v_bs_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = lean_usize_dec_lt(v_i_658_, v_sz_657_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_bs_659_);
return v___x_668_;
}
else
{
lean_object* v_v_669_; lean_object* v___x_670_; 
v_v_669_ = lean_array_uget_borrowed(v_bs_659_, v_i_658_);
lean_inc(v_v_669_);
v___x_670_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_v_669_, v___y_663_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; lean_object* v_bs_x27_673_; size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_unsigned_to_nat(0u);
v_bs_x27_673_ = lean_array_uset(v_bs_659_, v_i_658_, v___x_672_);
v___x_674_ = ((size_t)1ULL);
v___x_675_ = lean_usize_add(v_i_658_, v___x_674_);
v___x_676_ = lean_array_uset(v_bs_x27_673_, v_i_658_, v_a_671_);
v_i_658_ = v___x_675_;
v_bs_659_ = v___x_676_;
goto _start;
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v_bs_659_);
v_a_678_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_670_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_670_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10___boxed(lean_object* v_sz_686_, lean_object* v_i_687_, lean_object* v_bs_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
size_t v_sz_boxed_696_; size_t v_i_boxed_697_; lean_object* v_res_698_; 
v_sz_boxed_696_ = lean_unbox_usize(v_sz_686_);
lean_dec(v_sz_686_);
v_i_boxed_697_ = lean_unbox_usize(v_i_687_);
lean_dec(v_i_687_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(v_sz_boxed_696_, v_i_boxed_697_, v_bs_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_698_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(lean_object* v_opts_699_, lean_object* v_opt_700_){
_start:
{
lean_object* v_name_701_; lean_object* v_defValue_702_; lean_object* v_map_703_; lean_object* v___x_704_; 
v_name_701_ = lean_ctor_get(v_opt_700_, 0);
v_defValue_702_ = lean_ctor_get(v_opt_700_, 1);
v_map_703_ = lean_ctor_get(v_opts_699_, 0);
v___x_704_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_703_, v_name_701_);
if (lean_obj_tag(v___x_704_) == 0)
{
uint8_t v___x_705_; 
v___x_705_ = lean_unbox(v_defValue_702_);
return v___x_705_;
}
else
{
lean_object* v_val_706_; 
v_val_706_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v___x_704_, 1);
if (lean_obj_tag(v_val_706_) == 1)
{
uint8_t v_v_707_; 
v_v_707_ = lean_ctor_get_uint8(v_val_706_, 0);
lean_dec_ref_known(v_val_706_, 0);
return v_v_707_;
}
else
{
uint8_t v___x_708_; 
lean_dec(v_val_706_);
v___x_708_ = lean_unbox(v_defValue_702_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21___boxed(lean_object* v_opts_709_, lean_object* v_opt_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_709_, v_opt_710_);
lean_dec_ref(v_opt_710_);
lean_dec_ref(v_opts_709_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(1);
v___x_714_ = l_Lean_MessageData_ofFormat(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__2));
v___x_719_ = l_Lean_MessageData_ofFormat(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22(lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
return v_x_720_;
}
else
{
lean_object* v_head_722_; lean_object* v_tail_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_745_; 
v_head_722_ = lean_ctor_get(v_x_721_, 0);
v_tail_723_ = lean_ctor_get(v_x_721_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_745_ == 0)
{
v___x_725_ = v_x_721_;
v_isShared_726_ = v_isSharedCheck_745_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_tail_723_);
lean_inc(v_head_722_);
lean_dec(v_x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_745_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_before_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_743_; 
v_before_727_ = lean_ctor_get(v_head_722_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v_head_722_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v_head_722_, 1);
lean_dec(v_unused_744_);
v___x_729_ = v_head_722_;
v_isShared_730_ = v_isSharedCheck_743_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_before_727_);
lean_dec(v_head_722_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_743_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 7);
lean_ctor_set(v___x_729_, 1, v___x_731_);
lean_ctor_set(v___x_729_, 0, v_x_720_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_x_720_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_742_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__3);
if (v_isShared_726_ == 0)
{
lean_ctor_set_tag(v___x_725_, 7);
lean_ctor_set(v___x_725_, 1, v___x_734_);
lean_ctor_set(v___x_725_, 0, v___x_733_);
v___x_736_ = v___x_725_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_734_);
v___x_736_ = v_reuseFailAlloc_741_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = l_Lean_MessageData_ofSyntax(v_before_727_);
v___x_738_ = l_Lean_indentD(v___x_737_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_736_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v_x_720_ = v___x_739_;
v_x_721_ = v_tail_723_;
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
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__1));
v___x_750_ = l_Lean_MessageData_ofFormat(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(lean_object* v_msgData_751_, lean_object* v_macroStack_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_options_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_options_755_ = lean_ctor_get(v___y_753_, 1);
v___x_756_ = l_Lean_Elab_pp_macroStack;
v___x_757_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_macroStack_752_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v_msgData_751_);
return v___x_758_;
}
else
{
if (lean_obj_tag(v_macroStack_752_) == 0)
{
lean_object* v___x_759_; 
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v_msgData_751_);
return v___x_759_;
}
else
{
lean_object* v_head_760_; lean_object* v_after_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_776_; 
v_head_760_ = lean_ctor_get(v_macroStack_752_, 0);
lean_inc(v_head_760_);
v_after_761_ = lean_ctor_get(v_head_760_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_head_760_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_head_760_, 0);
lean_dec(v_unused_777_);
v___x_763_ = v_head_760_;
v_isShared_764_ = v_isSharedCheck_776_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_after_761_);
lean_dec(v_head_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_776_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22___closed__0);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 7);
lean_ctor_set(v___x_763_, 1, v___x_765_);
lean_ctor_set(v___x_763_, 0, v_msgData_751_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_msgData_751_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_775_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_msgData_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_768_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___closed__2);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Lean_MessageData_ofSyntax(v_after_761_);
v___x_771_ = l_Lean_indentD(v___x_770_);
v_msgData_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_772_, 0, v___x_769_);
lean_ctor_set(v_msgData_772_, 1, v___x_771_);
v___x_773_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22(v_msgData_772_, v_macroStack_752_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg___boxed(lean_object* v_msgData_778_, lean_object* v_macroStack_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_msgData_778_, v_macroStack_779_, v___y_780_);
lean_dec_ref(v___y_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(lean_object* v_msgData_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v_env_790_; lean_object* v___x_791_; lean_object* v_mctx_792_; lean_object* v_lctx_793_; lean_object* v_options_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_789_ = lean_st_ref_get(v___y_787_);
v_env_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_ref(v_env_790_);
lean_dec(v___x_789_);
v___x_791_ = lean_st_ref_get(v___y_785_);
v_mctx_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc_ref(v_mctx_792_);
lean_dec(v___x_791_);
v_lctx_793_ = lean_ctor_get(v___y_784_, 2);
v_options_794_ = lean_ctor_get(v___y_786_, 1);
lean_inc_ref(v_options_794_);
lean_inc_ref(v_lctx_793_);
v___x_795_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_795_, 0, v_env_790_);
lean_ctor_set(v___x_795_, 1, v_mctx_792_);
lean_ctor_set(v___x_795_, 2, v_lctx_793_);
lean_ctor_set(v___x_795_, 3, v_options_794_);
v___x_796_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v_msgData_783_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4___boxed(lean_object* v_msgData_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msgData_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_ref_813_; lean_object* v___x_814_; lean_object* v_a_815_; lean_object* v_macroStack_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_ref_813_ = lean_ctor_get(v___y_810_, 4);
v___x_814_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_805_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
v_macroStack_816_ = lean_ctor_get(v___y_806_, 1);
v___x_817_ = l_Lean_Elab_getBetterRef(v_ref_813_, v_macroStack_816_);
lean_inc(v_macroStack_816_);
v___x_818_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_a_815_, v_macroStack_816_, v___y_810_);
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_827_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_817_);
lean_ctor_set(v___x_823_, 1, v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 1);
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg___boxed(lean_object* v_msg_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v_msg_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
lean_inc(v_x_837_);
return v_x_837_;
}
else
{
lean_object* v_key_839_; lean_object* v_tail_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_key_839_ = lean_ctor_get(v_x_838_, 0);
v_tail_840_ = lean_ctor_get(v_x_838_, 2);
v___x_841_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_x_837_, v_tail_840_);
lean_inc(v_key_839_);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v_key_839_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4___boxed(lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_x_843_, v_x_844_);
lean_dec(v_x_844_);
lean_dec(v_x_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(lean_object* v_as_846_, size_t v_i_847_, size_t v_stop_848_, lean_object* v_b_849_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = lean_usize_dec_eq(v_i_847_, v_stop_848_);
if (v___x_850_ == 0)
{
size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_sub(v_i_847_, v___x_851_);
v___x_853_ = lean_array_uget_borrowed(v_as_846_, v___x_852_);
v___x_854_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__4(v_b_849_, v___x_853_);
lean_dec(v_b_849_);
v_i_847_ = v___x_852_;
v_b_849_ = v___x_854_;
goto _start;
}
else
{
return v_b_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5___boxed(lean_object* v_as_856_, lean_object* v_i_857_, lean_object* v_stop_858_, lean_object* v_b_859_){
_start:
{
size_t v_i_boxed_860_; size_t v_stop_boxed_861_; lean_object* v_res_862_; 
v_i_boxed_860_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_stop_boxed_861_ = lean_unbox_usize(v_stop_858_);
lean_dec(v_stop_858_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_as_856_, v_i_boxed_860_, v_stop_boxed_861_, v_b_859_);
lean_dec_ref(v_as_856_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
if (lean_obj_tag(v_a_863_) == 0)
{
lean_object* v___x_865_; 
v___x_865_ = l_List_reverse___redArg(v_a_864_);
return v___x_865_;
}
else
{
lean_object* v_head_866_; lean_object* v_tail_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_876_; 
v_head_866_ = lean_ctor_get(v_a_863_, 0);
v_tail_867_ = lean_ctor_get(v_a_863_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_876_ == 0)
{
v___x_869_ = v_a_863_;
v_isShared_870_ = v_isSharedCheck_876_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_tail_867_);
lean_inc(v_head_866_);
lean_dec(v_a_863_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_876_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_MessageData_ofExpr(v_head_866_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v_a_864_);
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_a_864_);
v___x_873_ = v_reuseFailAlloc_875_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
v_a_863_ = v_tail_867_;
v_a_864_ = v___x_873_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_877_; double v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_float_of_nat(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(lean_object* v_cls_881_, lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_ref_888_; lean_object* v___x_889_; lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_934_; 
v_ref_888_ = lean_ctor_get(v___y_885_, 4);
v___x_889_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_934_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_934_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_934_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v_traceState_895_; lean_object* v_env_896_; lean_object* v_nextMacroScope_897_; lean_object* v_ngen_898_; lean_object* v_auxDeclNGen_899_; lean_object* v_cache_900_; lean_object* v_messages_901_; lean_object* v_infoState_902_; lean_object* v_snapshotTasks_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_933_; 
v___x_894_ = lean_st_ref_take(v___y_886_);
v_traceState_895_ = lean_ctor_get(v___x_894_, 4);
v_env_896_ = lean_ctor_get(v___x_894_, 0);
v_nextMacroScope_897_ = lean_ctor_get(v___x_894_, 1);
v_ngen_898_ = lean_ctor_get(v___x_894_, 2);
v_auxDeclNGen_899_ = lean_ctor_get(v___x_894_, 3);
v_cache_900_ = lean_ctor_get(v___x_894_, 5);
v_messages_901_ = lean_ctor_get(v___x_894_, 6);
v_infoState_902_ = lean_ctor_get(v___x_894_, 7);
v_snapshotTasks_903_ = lean_ctor_get(v___x_894_, 8);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_933_ == 0)
{
v___x_905_ = v___x_894_;
v_isShared_906_ = v_isSharedCheck_933_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_snapshotTasks_903_);
lean_inc(v_infoState_902_);
lean_inc(v_messages_901_);
lean_inc(v_cache_900_);
lean_inc(v_traceState_895_);
lean_inc(v_auxDeclNGen_899_);
lean_inc(v_ngen_898_);
lean_inc(v_nextMacroScope_897_);
lean_inc(v_env_896_);
lean_dec(v___x_894_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_933_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
uint64_t v_tid_907_; lean_object* v_traces_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_932_; 
v_tid_907_ = lean_ctor_get_uint64(v_traceState_895_, sizeof(void*)*1);
v_traces_908_ = lean_ctor_get(v_traceState_895_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_traceState_895_);
if (v_isSharedCheck_932_ == 0)
{
v___x_910_ = v_traceState_895_;
v_isShared_911_ = v_isSharedCheck_932_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_traces_908_);
lean_dec(v_traceState_895_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_932_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; double v___x_913_; uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_912_ = lean_box(0);
v___x_913_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
v___x_914_ = 0;
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_916_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_916_, 0, v_cls_881_);
lean_ctor_set(v___x_916_, 1, v___x_912_);
lean_ctor_set(v___x_916_, 2, v___x_915_);
lean_ctor_set_float(v___x_916_, sizeof(void*)*3, v___x_913_);
lean_ctor_set_float(v___x_916_, sizeof(void*)*3 + 8, v___x_913_);
lean_ctor_set_uint8(v___x_916_, sizeof(void*)*3 + 16, v___x_914_);
v___x_917_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1));
v___x_918_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v_a_890_);
lean_ctor_set(v___x_918_, 2, v___x_917_);
lean_inc(v_ref_888_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_ref_888_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_PersistentArray_push___redArg(v_traces_908_, v___x_919_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_920_);
v___x_922_ = v___x_910_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_920_);
lean_ctor_set_uint64(v_reuseFailAlloc_931_, sizeof(void*)*1, v_tid_907_);
v___x_922_ = v_reuseFailAlloc_931_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 4, v___x_922_);
v___x_924_ = v___x_905_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_env_896_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_nextMacroScope_897_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_ngen_898_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_auxDeclNGen_899_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_930_, 5, v_cache_900_);
lean_ctor_set(v_reuseFailAlloc_930_, 6, v_messages_901_);
lean_ctor_set(v_reuseFailAlloc_930_, 7, v_infoState_902_);
lean_ctor_set(v_reuseFailAlloc_930_, 8, v_snapshotTasks_903_);
v___x_924_ = v_reuseFailAlloc_930_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_925_ = lean_st_ref_put(v___y_886_, v___x_924_);
v___x_926_ = lean_box(0);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_926_);
v___x_928_ = v___x_892_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___boxed(lean_object* v_cls_935_, lean_object* v_msg_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_935_, v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(lean_object* v_msg_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_ref_949_; lean_object* v___x_950_; lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_959_; 
v_ref_949_ = lean_ctor_get(v___y_946_, 4);
v___x_950_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_959_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
lean_inc(v_ref_949_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_ref_949_);
lean_ctor_set(v___x_955_, 1, v_a_951_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 1);
lean_ctor_set(v___x_953_, 0, v___x_955_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg___boxed(lean_object* v_msg_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v_msg_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_966_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(lean_object* v_a_967_, lean_object* v_as_968_, size_t v_i_969_, size_t v_stop_970_){
_start:
{
uint8_t v___x_971_; 
v___x_971_ = lean_usize_dec_eq(v_i_969_, v_stop_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_array_uget_borrowed(v_as_968_, v_i_969_);
v___x_973_ = lean_nat_dec_eq(v_a_967_, v___x_972_);
if (v___x_973_ == 0)
{
size_t v___x_974_; size_t v___x_975_; 
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_add(v_i_969_, v___x_974_);
v_i_969_ = v___x_975_;
goto _start;
}
else
{
return v___x_973_;
}
}
else
{
uint8_t v___x_977_; 
v___x_977_ = 0;
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25___boxed(lean_object* v_a_978_, lean_object* v_as_979_, lean_object* v_i_980_, lean_object* v_stop_981_){
_start:
{
size_t v_i_boxed_982_; size_t v_stop_boxed_983_; uint8_t v_res_984_; lean_object* v_r_985_; 
v_i_boxed_982_ = lean_unbox_usize(v_i_980_);
lean_dec(v_i_980_);
v_stop_boxed_983_ = lean_unbox_usize(v_stop_981_);
lean_dec(v_stop_981_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(v_a_978_, v_as_979_, v_i_boxed_982_, v_stop_boxed_983_);
lean_dec_ref(v_as_979_);
lean_dec(v_a_978_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(lean_object* v_as_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_array_get_size(v_as_986_);
v___x_990_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
if (v___x_990_ == 0)
{
return v___x_990_;
}
else
{
if (v___x_990_ == 0)
{
return v___x_990_;
}
else
{
size_t v___x_991_; size_t v___x_992_; uint8_t v___x_993_; 
v___x_991_ = ((size_t)0ULL);
v___x_992_ = lean_usize_of_nat(v___x_989_);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20_spec__25(v_a_987_, v_as_986_, v___x_991_, v___x_992_);
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20___boxed(lean_object* v_as_994_, lean_object* v_a_995_){
_start:
{
uint8_t v_res_996_; lean_object* v_r_997_; 
v_res_996_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(v_as_994_, v_a_995_);
lean_dec(v_a_995_);
lean_dec_ref(v_as_994_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__0));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(lean_object* v___x_1001_, lean_object* v_fst_1002_, lean_object* v_range_1003_, lean_object* v_b_1004_, lean_object* v_i_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_stop_1013_; lean_object* v_step_1014_; uint8_t v___x_1015_; 
v_stop_1013_ = lean_ctor_get(v_range_1003_, 1);
v_step_1014_ = lean_ctor_get(v_range_1003_, 2);
v___x_1015_ = lean_nat_dec_lt(v_i_1005_, v_stop_1013_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
lean_dec(v_i_1005_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_b_1004_);
return v___x_1016_;
}
else
{
lean_object* v___x_1017_; uint8_t v___x_1021_; 
v___x_1017_ = lean_box(0);
v___x_1021_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__20(v___x_1001_, v_i_1005_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; uint8_t v___x_1025_; 
v___x_1022_ = lean_array_fget_borrowed(v_fst_1002_, v_i_1005_);
lean_inc(v___x_1022_);
v___x_1023_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v___x_1022_, v___y_1009_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = l_Lean_Expr_hasMVar(v_a_1024_);
lean_dec(v_a_1024_);
if (v___x_1025_ == 0)
{
goto v___jp_1018_;
}
else
{
if (v___x_1021_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_dec(v_i_1005_);
v___x_1026_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1027_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1026_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1027_;
}
else
{
goto v___jp_1018_;
}
}
}
else
{
goto v___jp_1018_;
}
v___jp_1018_:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_nat_add(v_i_1005_, v_step_1014_);
lean_dec(v_i_1005_);
v_b_1004_ = v___x_1017_;
v_i_1005_ = v___x_1019_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___boxed(lean_object* v___x_1028_, lean_object* v_fst_1029_, lean_object* v_range_1030_, lean_object* v_b_1031_, lean_object* v_i_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_1028_, v_fst_1029_, v_range_1030_, v_b_1031_, v_i_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec_ref(v_range_1030_);
lean_dec_ref(v_fst_1029_);
lean_dec_ref(v___x_1028_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(lean_object* v_fst_1041_, lean_object* v_className_1042_, lean_object* v_as_1043_, size_t v_sz_1044_, size_t v_i_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_a_1055_; uint8_t v___x_1059_; 
v___x_1059_ = lean_usize_dec_lt(v_i_1045_, v_sz_1044_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_b_1046_);
return v___x_1060_;
}
else
{
lean_object* v___x_1061_; lean_object* v_a_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = l_Lean_instInhabitedExpr;
v_a_1062_ = lean_array_uget_borrowed(v_as_1043_, v_i_1045_);
v___x_1063_ = lean_array_get_borrowed(v___x_1061_, v_fst_1041_, v_a_1062_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___x_1063_);
v___x_1064_ = lean_infer_type(v___x_1063_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
v___x_1066_ = lean_whnf(v_a_1065_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_a_1067_, v___y_1050_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = l_Lean_Expr_isAppOfArity(v_a_1069_, v_className_1042_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec(v_a_1069_);
v___x_1072_ = lean_box(0);
v___x_1073_ = l_Lean_Expr_mvarId_x21(v___x_1063_);
v___x_1074_ = l_Lean_Elab_Term_synthesizeInstMVarCore(v___x_1073_, v___x_1072_, v___x_1072_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; uint8_t v___x_1076_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = lean_unbox(v_a_1075_);
lean_dec(v_a_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1078_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1077_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_dec_ref_known(v___x_1078_, 1);
v_a_1055_ = v_b_1046_;
goto v___jp_1054_;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v_b_1046_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
v_a_1055_ = v_b_1046_;
goto v___jp_1054_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_b_1046_);
v_a_1087_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1074_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1074_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = l_Lean_Expr_appArg_x21(v_a_1069_);
lean_dec(v_a_1069_);
v___x_1096_ = lean_array_push(v_b_1046_, v___x_1095_);
v_a_1055_ = v___x_1096_;
goto v___jp_1054_;
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v_b_1046_);
v_a_1097_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1068_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1068_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v_b_1046_);
v_a_1105_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1066_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1066_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v_b_1046_);
v_a_1113_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1064_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1064_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
v___jp_1054_:
{
size_t v___x_1056_; size_t v___x_1057_; 
v___x_1056_ = ((size_t)1ULL);
v___x_1057_ = lean_usize_add(v_i_1045_, v___x_1056_);
v_i_1045_ = v___x_1057_;
v_b_1046_ = v_a_1055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19___boxed(lean_object* v_fst_1121_, lean_object* v_className_1122_, lean_object* v_as_1123_, lean_object* v_sz_1124_, lean_object* v_i_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
size_t v_sz_boxed_1134_; size_t v_i_boxed_1135_; lean_object* v_res_1136_; 
v_sz_boxed_1134_ = lean_unbox_usize(v_sz_1124_);
lean_dec(v_sz_1124_);
v_i_boxed_1135_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v_fst_1121_, v_className_1122_, v_as_1123_, v_sz_boxed_1134_, v_i_boxed_1135_, v_b_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec_ref(v_as_1123_);
lean_dec(v_className_1122_);
lean_dec_ref(v_fst_1121_);
return v_res_1136_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(lean_object* v_className_1145_, lean_object* v_extraDeps_1146_, lean_object* v_plan_1147_, lean_object* v_processing_1148_, lean_object* v_depTypes_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
size_t v_sz_1157_; size_t v___x_1158_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___x_1202_; 
v_sz_1157_ = lean_array_size(v_depTypes_1149_);
v___x_1158_ = ((size_t)0ULL);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(v_sz_1157_, v___x_1158_, v_depTypes_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___x_1220_; size_t v_sz_1221_; lean_object* v___x_1222_; lean_object* v_fst_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1243_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v_sz_1221_ = lean_array_size(v_a_1203_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(v_a_1203_, v_sz_1221_, v___x_1158_, v___x_1220_);
v_fst_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v___x_1222_, 1);
lean_dec(v_unused_1244_);
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1243_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_fst_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1243_;
goto v_resetjp_1224_;
}
v___jp_1204_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = lean_array_get_size(v_a_1203_);
v___x_1213_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v___x_1214_ = lean_nat_dec_lt(v___x_1211_, v___x_1212_);
if (v___x_1214_ == 0)
{
lean_dec(v_a_1203_);
v___y_1170_ = v___y_1208_;
v___y_1171_ = v___y_1207_;
v___y_1172_ = v___y_1206_;
v___y_1173_ = v___y_1209_;
v___y_1174_ = v___y_1210_;
v___y_1175_ = v___y_1205_;
v___y_1176_ = v___x_1213_;
goto v___jp_1169_;
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_nat_dec_le(v___x_1212_, v___x_1212_);
if (v___x_1215_ == 0)
{
if (v___x_1214_ == 0)
{
lean_dec(v_a_1203_);
v___y_1170_ = v___y_1208_;
v___y_1171_ = v___y_1207_;
v___y_1172_ = v___y_1206_;
v___y_1173_ = v___y_1209_;
v___y_1174_ = v___y_1210_;
v___y_1175_ = v___y_1205_;
v___y_1176_ = v___x_1213_;
goto v___jp_1169_;
}
else
{
size_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_usize_of_nat(v___x_1212_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_1147_, v_a_1203_, v___x_1158_, v___x_1216_, v___x_1213_);
lean_dec(v_a_1203_);
v___y_1170_ = v___y_1208_;
v___y_1171_ = v___y_1207_;
v___y_1172_ = v___y_1206_;
v___y_1173_ = v___y_1209_;
v___y_1174_ = v___y_1210_;
v___y_1175_ = v___y_1205_;
v___y_1176_ = v___x_1217_;
goto v___jp_1169_;
}
}
else
{
size_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_usize_of_nat(v___x_1212_);
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_1147_, v_a_1203_, v___x_1158_, v___x_1218_, v___x_1213_);
lean_dec(v_a_1203_);
v___y_1170_ = v___y_1208_;
v___y_1171_ = v___y_1207_;
v___y_1172_ = v___y_1206_;
v___y_1173_ = v___y_1209_;
v___y_1174_ = v___y_1210_;
v___y_1175_ = v___y_1205_;
v___y_1176_ = v___x_1219_;
goto v___jp_1169_;
}
}
}
v_resetjp_1224_:
{
if (lean_obj_tag(v_fst_1223_) == 0)
{
lean_del_object(v___x_1225_);
v___y_1205_ = v_a_1150_;
v___y_1206_ = v_a_1151_;
v___y_1207_ = v_a_1152_;
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
goto v___jp_1204_;
}
else
{
lean_object* v_val_1227_; 
v_val_1227_ = lean_ctor_get(v_fst_1223_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v_fst_1223_, 1);
if (lean_obj_tag(v_val_1227_) == 1)
{
lean_object* v_val_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v_val_1228_ = lean_ctor_get(v_val_1227_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v_val_1227_, 1);
v___x_1229_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4);
v___x_1230_ = l_Lean_MessageData_ofExpr(v_val_1228_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 7);
lean_ctor_set(v___x_1225_, 1, v___x_1230_);
lean_ctor_set(v___x_1225_, 0, v___x_1229_);
v___x_1232_ = v___x_1225_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_1232_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_dec_ref_known(v___x_1233_, 1);
v___y_1205_ = v_a_1150_;
v___y_1206_ = v_a_1151_;
v___y_1207_ = v_a_1152_;
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
goto v___jp_1204_;
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_a_1203_);
lean_dec_ref(v_processing_1148_);
lean_dec_ref(v_plan_1147_);
lean_dec_ref(v_extraDeps_1146_);
lean_dec(v_className_1145_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
else
{
lean_dec(v_val_1227_);
lean_del_object(v___x_1225_);
v___y_1205_ = v_a_1150_;
v___y_1206_ = v_a_1151_;
v___y_1207_ = v_a_1152_;
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
goto v___jp_1204_;
}
}
}
}
else
{
lean_dec_ref(v_processing_1148_);
lean_dec_ref(v_plan_1147_);
lean_dec_ref(v_extraDeps_1146_);
lean_dec(v_className_1145_);
return v___x_1202_;
}
v___jp_1159_:
{
size_t v_sz_1167_; lean_object* v___x_1168_; 
v_sz_1167_ = lean_array_size(v___y_1160_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_1148_, v_className_1145_, v_extraDeps_1146_, v___y_1160_, v_sz_1167_, v___x_1158_, v_plan_1147_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec_ref(v___y_1160_);
return v___x_1168_;
}
v___jp_1169_:
{
lean_object* v___x_1177_; size_t v_sz_1178_; lean_object* v___x_1179_; lean_object* v_fst_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1200_; 
v___x_1177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v_sz_1178_ = lean_array_size(v___y_1176_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(v_processing_1148_, v___y_1176_, v_sz_1178_, v___x_1158_, v___x_1177_);
v_fst_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v___x_1179_, 1);
lean_dec(v_unused_1201_);
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1200_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_fst_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1200_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
if (lean_obj_tag(v_fst_1180_) == 0)
{
lean_del_object(v___x_1182_);
v___y_1160_ = v___y_1176_;
v___y_1161_ = v___y_1175_;
v___y_1162_ = v___y_1172_;
v___y_1163_ = v___y_1171_;
v___y_1164_ = v___y_1170_;
v___y_1165_ = v___y_1173_;
v___y_1166_ = v___y_1174_;
goto v___jp_1159_;
}
else
{
lean_object* v_val_1184_; 
v_val_1184_ = lean_ctor_get(v_fst_1180_, 0);
lean_inc(v_val_1184_);
lean_dec_ref_known(v_fst_1180_, 1);
if (lean_obj_tag(v_val_1184_) == 1)
{
lean_object* v_val_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v_val_1185_ = lean_ctor_get(v_val_1184_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_val_1184_, 1);
v___x_1186_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1);
v___x_1187_ = l_Lean_MessageData_ofExpr(v_val_1185_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 7);
lean_ctor_set(v___x_1182_, 1, v___x_1187_);
lean_ctor_set(v___x_1182_, 0, v___x_1186_);
v___x_1189_ = v___x_1182_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_1189_, v___y_1175_, v___y_1172_, v___y_1171_, v___y_1170_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_dec_ref_known(v___x_1190_, 1);
v___y_1160_ = v___y_1176_;
v___y_1161_ = v___y_1175_;
v___y_1162_ = v___y_1172_;
v___y_1163_ = v___y_1171_;
v___y_1164_ = v___y_1170_;
v___y_1165_ = v___y_1173_;
v___y_1166_ = v___y_1174_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v___y_1176_);
lean_dec_ref(v_processing_1148_);
lean_dec_ref(v_plan_1147_);
lean_dec_ref(v_extraDeps_1146_);
lean_dec(v_className_1145_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
else
{
lean_dec(v_val_1184_);
lean_del_object(v___x_1182_);
v___y_1160_ = v___y_1176_;
v___y_1161_ = v___y_1175_;
v___y_1162_ = v___y_1172_;
v___y_1163_ = v___y_1171_;
v___y_1164_ = v___y_1170_;
v___y_1165_ = v___y_1173_;
v___y_1166_ = v___y_1174_;
goto v___jp_1159_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3(void){
_start:
{
lean_object* v_cls_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_cls_1253_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1254_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1));
v___x_1255_ = l_Lean_Name_append(v___x_1254_, v_cls_1253_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6));
v___x_1261_ = l_Lean_stringToMessageData(v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8));
v___x_1264_ = l_Lean_stringToMessageData(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(lean_object* v_className_1271_, lean_object* v_extraDeps_1272_, lean_object* v_plan_1273_, lean_object* v_processing_1274_, lean_object* v_cls_1275_, lean_object* v_inst_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_cls_1284_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___x_1455_; 
v_cls_1284_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1455_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1284_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; uint8_t v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = lean_unbox(v_a_1456_);
lean_dec(v_a_1456_);
if (v___x_1457_ == 0)
{
v___y_1373_ = v_a_1277_;
v___y_1374_ = v_a_1278_;
v___y_1375_ = v_a_1279_;
v___y_1376_ = v_a_1280_;
v___y_1377_ = v_a_1281_;
v___y_1378_ = v_a_1282_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13);
lean_inc_ref(v_cls_1275_);
v___x_1459_ = l_Lean_MessageData_ofExpr(v_cls_1275_);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1284_, v___x_1460_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_dec_ref_known(v___x_1461_, 1);
v___y_1373_ = v_a_1277_;
v___y_1374_ = v_a_1278_;
v___y_1375_ = v_a_1279_;
v___y_1376_ = v_a_1280_;
v___y_1377_ = v_a_1281_;
v___y_1378_ = v_a_1282_;
goto v___jp_1372_;
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_inst_1276_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_inst_1276_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1470_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1455_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1455_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
v___jp_1285_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; size_t v_sz_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v_sz_1296_ = lean_array_size(v___y_1293_);
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v___y_1289_, v_className_1271_, v___y_1293_, v_sz_1296_, v___x_1297_, v___x_1295_, v___y_1290_, v___y_1291_, v___y_1286_, v___y_1288_, v___y_1292_, v___y_1287_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1300_ = lean_array_get_size(v___y_1289_);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1294_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
lean_ctor_set(v___x_1302_, 2, v___x_1301_);
v___x_1303_ = lean_box(0);
v___x_1304_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___y_1293_, v___y_1289_, v___x_1302_, v___x_1303_, v___x_1294_, v___y_1290_, v___y_1291_, v___y_1286_, v___y_1288_, v___y_1292_, v___y_1287_);
lean_dec_ref_known(v___x_1302_, 3);
lean_dec_ref(v___y_1289_);
lean_dec_ref(v___y_1293_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_options_1305_; uint8_t v_hasTrace_1306_; 
lean_dec_ref_known(v___x_1304_, 1);
v_options_1305_ = lean_ctor_get(v___y_1292_, 1);
v_hasTrace_1306_ = lean_ctor_get_uint8(v_options_1305_, sizeof(void*)*1);
if (v_hasTrace_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_dec_ref(v_cls_1275_);
v___x_1307_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1271_, v_extraDeps_1272_, v_plan_1273_, v_processing_1274_, v_a_1299_, v___y_1290_, v___y_1291_, v___y_1286_, v___y_1288_, v___y_1292_, v___y_1287_);
return v___x_1307_;
}
else
{
lean_object* v_toCold_1308_; lean_object* v_inheritedTraceOptions_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_toCold_1308_ = lean_ctor_get(v___y_1292_, 0);
v_inheritedTraceOptions_1309_ = lean_ctor_get(v_toCold_1308_, 4);
v___x_1310_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_1311_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1309_, v_options_1305_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref(v_cls_1275_);
v___x_1312_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1271_, v_extraDeps_1272_, v_plan_1273_, v_processing_1274_, v_a_1299_, v___y_1290_, v___y_1291_, v___y_1286_, v___y_1288_, v___y_1292_, v___y_1287_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1313_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5);
v___x_1314_ = l_Lean_MessageData_ofExpr(v_cls_1275_);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
lean_inc(v_a_1299_);
v___x_1318_ = lean_array_to_list(v_a_1299_);
v___x_1319_ = lean_box(0);
v___x_1320_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1318_, v___x_1319_);
v___x_1321_ = l_Lean_MessageData_ofList(v___x_1320_);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1317_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1284_, v___x_1322_, v___y_1286_, v___y_1288_, v___y_1292_, v___y_1287_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref_known(v___x_1323_, 1);
v___x_1324_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1271_, v_extraDeps_1272_, v_plan_1273_, v_processing_1274_, v_a_1299_, v___y_1290_, v___y_1291_, v___y_1286_, v___y_1288_, v___y_1292_, v___y_1287_);
return v___x_1324_;
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1299_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1325_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1323_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1323_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1299_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1333_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1304_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1304_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_dec_ref(v___y_1293_);
lean_dec_ref(v___y_1289_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
return v___x_1298_;
}
}
v___jp_1341_:
{
lean_object* v___x_1351_; 
lean_inc_ref(v_cls_1275_);
v___x_1351_ = l_Lean_Meta_isExprDefEq(v_cls_1275_, v___y_1342_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; uint8_t v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = lean_unbox(v_a_1352_);
lean_dec(v_a_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1355_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1354_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_dec_ref_known(v___x_1355_, 1);
v___y_1286_ = v___y_1347_;
v___y_1287_ = v___y_1350_;
v___y_1288_ = v___y_1348_;
v___y_1289_ = v___y_1343_;
v___y_1290_ = v___y_1345_;
v___y_1291_ = v___y_1346_;
v___y_1292_ = v___y_1349_;
v___y_1293_ = v___y_1344_;
goto v___jp_1285_;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
v___y_1286_ = v___y_1347_;
v___y_1287_ = v___y_1350_;
v___y_1288_ = v___y_1348_;
v___y_1289_ = v___y_1343_;
v___y_1290_ = v___y_1345_;
v___y_1291_ = v___y_1346_;
v___y_1292_ = v___y_1349_;
v___y_1293_ = v___y_1344_;
goto v___jp_1285_;
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1364_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1351_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1351_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
v___jp_1372_:
{
lean_object* v_val_1379_; lean_object* v_synthOrder_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1454_; 
v_val_1379_ = lean_ctor_get(v_inst_1276_, 0);
v_synthOrder_1380_ = lean_ctor_get(v_inst_1276_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_inst_1276_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1382_ = v_inst_1276_;
v_isShared_1383_ = v_isSharedCheck_1454_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_synthOrder_1380_);
lean_inc(v_val_1379_);
lean_dec(v_inst_1276_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1454_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; 
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
v___x_1384_ = lean_infer_type(v_val_1379_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = lean_box(0);
v___x_1387_ = 0;
v___x_1388_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1385_, v___x_1386_, v___x_1387_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v_snd_1390_; lean_object* v_fst_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1437_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v_snd_1390_ = lean_ctor_get(v_a_1389_, 1);
v_fst_1391_ = lean_ctor_get(v_a_1389_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1389_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1393_ = v_a_1389_;
v_isShared_1394_ = v_isSharedCheck_1437_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_snd_1390_);
lean_inc(v_fst_1391_);
lean_dec(v_a_1389_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1437_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1435_; 
v_snd_1395_ = lean_ctor_get(v_snd_1390_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_snd_1390_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_snd_1390_, 0);
lean_dec(v_unused_1436_);
v___x_1397_ = v_snd_1390_;
v_isShared_1398_ = v_isSharedCheck_1435_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_dec(v_snd_1390_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1435_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; 
v___x_1399_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1284_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; uint8_t v___x_1401_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = lean_unbox(v_a_1400_);
lean_dec(v_a_1400_);
if (v___x_1401_ == 0)
{
lean_del_object(v___x_1397_);
lean_del_object(v___x_1393_);
lean_del_object(v___x_1382_);
v___y_1342_ = v_snd_1395_;
v___y_1343_ = v_fst_1391_;
v___y_1344_ = v_synthOrder_1380_;
v___y_1345_ = v___y_1373_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v___y_1375_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___y_1377_;
v___y_1350_ = v___y_1378_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1402_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9);
lean_inc(v_fst_1391_);
v___x_1403_ = lean_array_to_list(v_fst_1391_);
v___x_1404_ = lean_box(0);
v___x_1405_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1403_, v___x_1404_);
v___x_1406_ = l_Lean_MessageData_ofList(v___x_1405_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 7);
lean_ctor_set(v___x_1397_, 1, v___x_1406_);
lean_ctor_set(v___x_1397_, 0, v___x_1402_);
v___x_1408_ = v___x_1397_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11);
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 7);
lean_ctor_set(v___x_1393_, 1, v___x_1409_);
lean_ctor_set(v___x_1393_, 0, v___x_1408_);
v___x_1411_ = v___x_1393_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_inc(v_snd_1395_);
v___x_1412_ = l_Lean_MessageData_ofExpr(v_snd_1395_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 7);
lean_ctor_set(v___x_1382_, 1, v___x_1412_);
lean_ctor_set(v___x_1382_, 0, v___x_1411_);
v___x_1414_ = v___x_1382_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1284_, v___x_1414_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec_ref_known(v___x_1415_, 1);
v___y_1342_ = v_snd_1395_;
v___y_1343_ = v_fst_1391_;
v___y_1344_ = v_synthOrder_1380_;
v___y_1345_ = v___y_1373_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v___y_1375_;
v___y_1348_ = v___y_1376_;
v___y_1349_ = v___y_1377_;
v___y_1350_ = v___y_1378_;
goto v___jp_1341_;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_snd_1395_);
lean_dec(v_fst_1391_);
lean_dec_ref(v_synthOrder_1380_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
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
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_del_object(v___x_1397_);
lean_dec(v_snd_1395_);
lean_del_object(v___x_1393_);
lean_dec(v_fst_1391_);
lean_del_object(v___x_1382_);
lean_dec_ref(v_synthOrder_1380_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1427_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1399_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1399_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_del_object(v___x_1382_);
lean_dec_ref(v_synthOrder_1380_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1438_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1388_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1388_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1382_);
lean_dec_ref(v_synthOrder_1380_);
lean_dec_ref(v_cls_1275_);
lean_dec_ref(v_processing_1274_);
lean_dec_ref(v_plan_1273_);
lean_dec_ref(v_extraDeps_1272_);
lean_dec(v_className_1271_);
v_a_1446_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1384_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1384_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(lean_object* v_className_1478_, lean_object* v_extraDeps_1479_, lean_object* v_plan_1480_, lean_object* v_processing_1481_, lean_object* v_a_1482_, lean_object* v_as_1483_, size_t v_sz_1484_, size_t v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_lt(v_i_1485_, v_sz_1484_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec_ref(v_a_1482_);
lean_dec_ref(v_processing_1481_);
lean_dec_ref(v_plan_1480_);
lean_dec_ref(v_extraDeps_1479_);
lean_dec(v_className_1478_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_b_1486_);
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; lean_object* v_a_1497_; lean_object* v___x_1498_; 
lean_dec_ref(v_b_1486_);
v___x_1496_ = lean_box(0);
v_a_1497_ = lean_array_uget_borrowed(v_as_1483_, v_i_1485_);
lean_inc(v_a_1497_);
lean_inc_ref(v_a_1482_);
lean_inc_ref(v_processing_1481_);
lean_inc_ref(v_plan_1480_);
lean_inc_ref(v_extraDeps_1479_);
lean_inc(v_className_1478_);
v___x_1498_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(v_className_1478_, v_extraDeps_1479_, v_plan_1480_, v_processing_1481_, v_a_1482_, v_a_1497_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v_a_1482_);
lean_dec_ref(v_processing_1481_);
lean_dec_ref(v_plan_1480_);
lean_dec_ref(v_extraDeps_1479_);
lean_dec(v_className_1478_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1508_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1508_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_a_1499_);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1496_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1524_; 
v_a_1509_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1511_ = v___x_1498_;
v_isShared_1512_ = v_isSharedCheck_1524_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1498_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1524_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; uint8_t v___y_1515_; uint8_t v___x_1522_; 
v___x_1513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0));
v___x_1522_ = l_Lean_Exception_isInterrupt(v_a_1509_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; 
lean_inc(v_a_1509_);
v___x_1523_ = l_Lean_Exception_isRuntime(v_a_1509_);
v___y_1515_ = v___x_1523_;
goto v___jp_1514_;
}
else
{
v___y_1515_ = v___x_1522_;
goto v___jp_1514_;
}
v___jp_1514_:
{
if (v___y_1515_ == 0)
{
size_t v___x_1516_; size_t v___x_1517_; 
lean_del_object(v___x_1511_);
lean_dec(v_a_1509_);
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = lean_usize_add(v_i_1485_, v___x_1516_);
v_i_1485_ = v___x_1517_;
v_b_1486_ = v___x_1513_;
goto _start;
}
else
{
lean_object* v___x_1520_; 
lean_dec_ref(v_a_1482_);
lean_dec_ref(v_processing_1481_);
lean_dec_ref(v_plan_1480_);
lean_dec_ref(v_extraDeps_1479_);
lean_dec(v_className_1478_);
if (v_isShared_1512_ == 0)
{
v___x_1520_ = v___x_1511_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1509_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
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
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__0));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__2));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__4));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__6));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__8));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__10));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(lean_object* v_className_1543_, lean_object* v_extraDeps_1544_, lean_object* v_plan_1545_, lean_object* v_processing_1546_, lean_object* v_type_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v_toCold_1573_; lean_object* v_options_1574_; lean_object* v_currRecDepth_1575_; lean_object* v_maxRecDepth_1576_; lean_object* v_ref_1577_; lean_object* v_currNamespace_1578_; lean_object* v_openDecls_1579_; lean_object* v_initHeartbeats_1580_; lean_object* v_maxHeartbeats_1581_; lean_object* v_currMacroScope_1582_; uint8_t v_diag_1583_; uint8_t v_suppressElabErrors_1584_; lean_object* v_cls_1585_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_toCold_1573_ = lean_ctor_get(v_a_1552_, 0);
v_options_1574_ = lean_ctor_get(v_a_1552_, 1);
v_currRecDepth_1575_ = lean_ctor_get(v_a_1552_, 2);
v_maxRecDepth_1576_ = lean_ctor_get(v_a_1552_, 3);
v_ref_1577_ = lean_ctor_get(v_a_1552_, 4);
v_currNamespace_1578_ = lean_ctor_get(v_a_1552_, 5);
v_openDecls_1579_ = lean_ctor_get(v_a_1552_, 6);
v_initHeartbeats_1580_ = lean_ctor_get(v_a_1552_, 7);
v_maxHeartbeats_1581_ = lean_ctor_get(v_a_1552_, 8);
v_currMacroScope_1582_ = lean_ctor_get(v_a_1552_, 9);
v_diag_1583_ = lean_ctor_get_uint8(v_a_1552_, sizeof(void*)*10);
v_suppressElabErrors_1584_ = lean_ctor_get_uint8(v_a_1552_, sizeof(void*)*10 + 1);
v_cls_1585_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_nat_dec_eq(v_maxRecDepth_1576_, v___x_1765_);
if (v___x_1766_ == 0)
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_nat_dec_eq(v_currRecDepth_1575_, v_maxRecDepth_1576_);
if (v___x_1767_ == 0)
{
goto v___jp_1735_;
}
else
{
lean_object* v___x_1768_; 
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
lean_inc(v_ref_1577_);
v___x_1768_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_1577_);
return v___x_1768_;
}
}
else
{
goto v___jp_1735_;
}
v___jp_1555_:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1543_, v_extraDeps_1544_, v_plan_1545_, v_processing_1546_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec_ref(v___y_1561_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1572_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_array_push(v_a_1564_, v_type_1547_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
else
{
lean_dec_ref(v_type_1547_);
return v___x_1563_;
}
}
v___jp_1586_:
{
lean_object* v___x_1595_; size_t v_sz_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v___x_1595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0));
v_sz_1596_ = lean_array_size(v___y_1588_);
v___x_1597_ = ((size_t)0ULL);
lean_inc_ref(v_processing_1546_);
lean_inc_ref(v_plan_1545_);
lean_inc_ref(v_extraDeps_1544_);
lean_inc(v_className_1543_);
v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_1543_, v_extraDeps_1544_, v_plan_1545_, v_processing_1546_, v___y_1587_, v___y_1588_, v_sz_1596_, v___x_1597_, v___x_1595_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
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
lean_inc_ref(v_extraDeps_1544_);
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc_ref(v_type_1547_);
v___x_1607_ = lean_apply_8(v_extraDeps_1544_, v_type_1547_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, lean_box(0));
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_options_1608_; uint8_t v_hasTrace_1609_; 
v_options_1608_ = lean_ctor_get(v___y_1593_, 1);
v_hasTrace_1609_ = lean_ctor_get_uint8(v_options_1608_, sizeof(void*)*1);
if (v_hasTrace_1609_ == 0)
{
lean_object* v_a_1610_; 
lean_del_object(v___x_1605_);
v_a_1610_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1607_, 1);
v___y_1556_ = v_a_1610_;
v___y_1557_ = v___y_1589_;
v___y_1558_ = v___y_1590_;
v___y_1559_ = v___y_1591_;
v___y_1560_ = v___y_1592_;
v___y_1561_ = v___y_1593_;
v___y_1562_ = v___y_1594_;
goto v___jp_1555_;
}
else
{
lean_object* v_toCold_1611_; lean_object* v_a_1612_; lean_object* v_inheritedTraceOptions_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v_toCold_1611_ = lean_ctor_get(v___y_1593_, 0);
v_a_1612_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1607_, 1);
v_inheritedTraceOptions_1613_ = lean_ctor_get(v_toCold_1611_, 4);
v___x_1614_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_1615_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1613_, v_options_1608_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_del_object(v___x_1605_);
v___y_1556_ = v_a_1612_;
v___y_1557_ = v___y_1589_;
v___y_1558_ = v___y_1590_;
v___y_1559_ = v___y_1591_;
v___y_1560_ = v___y_1592_;
v___y_1561_ = v___y_1593_;
v___y_1562_ = v___y_1594_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1);
lean_inc_ref(v_type_1547_);
v___x_1617_ = l_Lean_MessageData_ofExpr(v_type_1547_);
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
v___y_1556_ = v_a_1612_;
v___y_1557_ = v___y_1589_;
v___y_1558_ = v___y_1590_;
v___y_1559_ = v___y_1591_;
v___y_1560_ = v___y_1592_;
v___y_1561_ = v___y_1593_;
v___y_1562_ = v___y_1594_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_a_1612_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
return v___x_1607_;
}
}
else
{
lean_object* v_val_1637_; lean_object* v___x_1639_; 
lean_del_object(v___x_1605_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
v___x_1659_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_plan_1545_, v_type_1547_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_mk_empty_array_with_capacity(v___x_1660_);
lean_inc_ref(v_type_1547_);
v___x_1662_ = lean_array_push(v___x_1661_, v_type_1547_);
lean_inc(v_className_1543_);
v___x_1663_ = l_Lean_Meta_mkAppM(v_className_1543_, v___x_1662_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
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
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v_plan_1545_);
return v___x_1713_;
}
}
v___jp_1714_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1719_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___y_1718_, v___y_1716_);
v___x_1720_ = l_Lean_MessageData_ofList(v___x_1719_);
v___x_1721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___y_1717_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7);
v___x_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
lean_inc_ref(v_type_1547_);
v___x_1724_ = l_Lean_MessageData_ofExpr(v_type_1547_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1585_, v___x_1725_, v_a_1550_, v_a_1551_, v___y_1715_, v_a_1553_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_dec_ref_known(v___x_1726_, 1);
v___y_1653_ = v_a_1548_;
v___y_1654_ = v_a_1549_;
v___y_1655_ = v_a_1550_;
v___y_1656_ = v_a_1551_;
v___y_1657_ = v___y_1715_;
v___y_1658_ = v_a_1553_;
goto v___jp_1652_;
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref(v___y_1715_);
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
v___x_1737_ = lean_nat_add(v_currRecDepth_1575_, v___x_1736_);
lean_inc(v_currMacroScope_1582_);
lean_inc(v_maxHeartbeats_1581_);
lean_inc(v_initHeartbeats_1580_);
lean_inc(v_openDecls_1579_);
lean_inc(v_currNamespace_1578_);
lean_inc(v_ref_1577_);
lean_inc(v_maxRecDepth_1576_);
lean_inc_ref(v_options_1574_);
lean_inc_ref(v_toCold_1573_);
v___x_1738_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1738_, 0, v_toCold_1573_);
lean_ctor_set(v___x_1738_, 1, v_options_1574_);
lean_ctor_set(v___x_1738_, 2, v___x_1737_);
lean_ctor_set(v___x_1738_, 3, v_maxRecDepth_1576_);
lean_ctor_set(v___x_1738_, 4, v_ref_1577_);
lean_ctor_set(v___x_1738_, 5, v_currNamespace_1578_);
lean_ctor_set(v___x_1738_, 6, v_openDecls_1579_);
lean_ctor_set(v___x_1738_, 7, v_initHeartbeats_1580_);
lean_ctor_set(v___x_1738_, 8, v_maxHeartbeats_1581_);
lean_ctor_set(v___x_1738_, 9, v_currMacroScope_1582_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*10, v_diag_1583_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*10 + 1, v_suppressElabErrors_1584_);
v___x_1739_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1585_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v___x_1738_, v_a_1553_);
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
v___y_1653_ = v_a_1548_;
v___y_1654_ = v_a_1549_;
v___y_1655_ = v_a_1550_;
v___y_1656_ = v_a_1551_;
v___y_1657_ = v___x_1738_;
v___y_1658_ = v_a_1553_;
goto v___jp_1652_;
}
else
{
lean_object* v_buckets_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v_buckets_1742_ = lean_ctor_get(v_processing_1546_, 1);
v___x_1743_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9);
lean_inc_ref(v_plan_1545_);
v___x_1744_ = lean_array_to_list(v_plan_1545_);
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
v___y_1715_ = v___x_1738_;
v___y_1716_ = v___x_1745_;
v___y_1717_ = v___x_1750_;
v___y_1718_ = v___x_1745_;
goto v___jp_1714_;
}
else
{
size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_usize_of_nat(v___x_1751_);
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_buckets_1742_, v___x_1754_, v___x_1755_, v___x_1745_);
v___y_1715_ = v___x_1738_;
v___y_1716_ = v___x_1745_;
v___y_1717_ = v___x_1750_;
v___y_1718_ = v___x_1756_;
goto v___jp_1714_;
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref_known(v___x_1738_, 10);
lean_dec_ref(v_type_1547_);
lean_dec_ref(v_processing_1546_);
lean_dec_ref(v_plan_1545_);
lean_dec_ref(v_extraDeps_1544_);
lean_dec(v_className_1543_);
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
lean_object* v___x_2039_; lean_object* v_traceState_2040_; lean_object* v_traces_2041_; lean_object* v___x_2042_; lean_object* v_traceState_2043_; lean_object* v_env_2044_; lean_object* v_nextMacroScope_2045_; lean_object* v_ngen_2046_; lean_object* v_auxDeclNGen_2047_; lean_object* v_cache_2048_; lean_object* v_messages_2049_; lean_object* v_infoState_2050_; lean_object* v_snapshotTasks_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2070_; 
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
v_messages_2049_ = lean_ctor_get(v___x_2042_, 6);
v_infoState_2050_ = lean_ctor_get(v___x_2042_, 7);
v_snapshotTasks_2051_ = lean_ctor_get(v___x_2042_, 8);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2053_ = v___x_2042_;
v_isShared_2054_ = v_isSharedCheck_2070_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_snapshotTasks_2051_);
lean_inc(v_infoState_2050_);
lean_inc(v_messages_2049_);
lean_inc(v_cache_2048_);
lean_inc(v_traceState_2043_);
lean_inc(v_auxDeclNGen_2047_);
lean_inc(v_ngen_2046_);
lean_inc(v_nextMacroScope_2045_);
lean_inc(v_env_2044_);
lean_dec(v___x_2042_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2070_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint64_t v_tid_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2068_; 
v_tid_2055_ = lean_ctor_get_uint64(v_traceState_2043_, sizeof(void*)*1);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_traceState_2043_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v_traceState_2043_, 0);
lean_dec(v_unused_2069_);
v___x_2057_ = v_traceState_2043_;
v_isShared_2058_ = v_isSharedCheck_2068_;
goto v_resetjp_2056_;
}
else
{
lean_dec(v_traceState_2043_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2068_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2059_);
lean_ctor_set_uint64(v_reuseFailAlloc_2067_, sizeof(void*)*1, v_tid_2055_);
v___x_2061_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2063_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 4, v___x_2061_);
v___x_2063_ = v___x_2053_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_env_2044_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_nextMacroScope_2045_);
lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_ngen_2046_);
lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_auxDeclNGen_2047_);
lean_ctor_set(v_reuseFailAlloc_2066_, 4, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2066_, 5, v_cache_2048_);
lean_ctor_set(v_reuseFailAlloc_2066_, 6, v_messages_2049_);
lean_ctor_set(v_reuseFailAlloc_2066_, 7, v_infoState_2050_);
lean_ctor_set(v_reuseFailAlloc_2066_, 8, v_snapshotTasks_2051_);
v___x_2063_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_st_ref_put(v___y_2037_, v___x_2063_);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_traces_2041_);
return v___x_2065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___boxed(lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_2071_);
lean_dec(v___y_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_2079_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___boxed(lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
return v_res_2089_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0));
v___x_2092_ = l_Lean_stringToMessageData(v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2));
v___x_2095_ = l_Lean_stringToMessageData(v___x_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(lean_object* v_className_2096_, lean_object* v_type_2097_, lean_object* v_r_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___y_2117_; 
v___x_2106_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1);
v___x_2107_ = 0;
v___x_2108_ = l_Lean_MessageData_ofConstName(v_className_2096_, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2106_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = l_Lean_MessageData_ofExpr(v_type_2097_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
if (lean_obj_tag(v_r_2098_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v_r_2098_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v_r_2098_, 1);
v___x_2121_ = l_Lean_Exception_toMessageData(v_a_2120_);
v___y_2117_ = v___x_2121_;
goto v___jp_2116_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2122_ = lean_ctor_get(v_r_2098_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v_r_2098_, 1);
v___x_2123_ = lean_array_to_list(v_a_2122_);
v___x_2124_ = lean_box(0);
v___x_2125_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_2123_, v___x_2124_);
v___x_2126_ = l_Lean_MessageData_ofList(v___x_2125_);
v___y_2117_ = v___x_2126_;
goto v___jp_2116_;
}
v___jp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2115_);
lean_ctor_set(v___x_2118_, 1, v___y_2117_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed(lean_object* v_className_2127_, lean_object* v_type_2128_, lean_object* v_r_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(v_className_2127_, v_type_2128_, v_r_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(lean_object* v_opts_2138_, lean_object* v_opt_2139_){
_start:
{
lean_object* v_name_2140_; lean_object* v_defValue_2141_; lean_object* v_map_2142_; lean_object* v___x_2143_; 
v_name_2140_ = lean_ctor_get(v_opt_2139_, 0);
v_defValue_2141_ = lean_ctor_get(v_opt_2139_, 1);
v_map_2142_ = lean_ctor_get(v_opts_2138_, 0);
v___x_2143_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2142_, v_name_2140_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_inc(v_defValue_2141_);
return v_defValue_2141_;
}
else
{
lean_object* v_val_2144_; 
v_val_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v___x_2143_, 1);
if (lean_obj_tag(v_val_2144_) == 3)
{
lean_object* v_v_2145_; 
v_v_2145_ = lean_ctor_get(v_val_2144_, 0);
lean_inc(v_v_2145_);
lean_dec_ref_known(v_val_2144_, 1);
return v_v_2145_;
}
else
{
lean_dec(v_val_2144_);
lean_inc(v_defValue_2141_);
return v_defValue_2141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4___boxed(lean_object* v_opts_2146_, lean_object* v_opt_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2146_, v_opt_2147_);
lean_dec_ref(v_opt_2147_);
lean_dec_ref(v_opts_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(lean_object* v_e_2149_){
_start:
{
if (lean_obj_tag(v_e_2149_) == 0)
{
uint8_t v___x_2150_; 
v___x_2150_ = 2;
return v___x_2150_;
}
else
{
uint8_t v___x_2151_; 
v___x_2151_ = 0;
return v___x_2151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___boxed(lean_object* v_e_2152_){
_start:
{
uint8_t v_res_2153_; lean_object* v_r_2154_; 
v_res_2153_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_e_2152_);
lean_dec_ref(v_e_2152_);
v_r_2154_ = lean_box(v_res_2153_);
return v_r_2154_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(lean_object* v_x_2155_){
_start:
{
if (lean_obj_tag(v_x_2155_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
v_a_2157_ = lean_ctor_get(v_x_2155_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_x_2155_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v_x_2155_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v_x_2155_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
lean_ctor_set_tag(v___x_2159_, 1);
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v_a_2165_ = lean_ctor_get(v_x_2155_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2155_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v_x_2155_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v_x_2155_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 0);
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg___boxed(lean_object* v_x_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_x_2173_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(size_t v_sz_2176_, size_t v_i_2177_, lean_object* v_bs_2178_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = lean_usize_dec_lt(v_i_2177_, v_sz_2176_);
if (v___x_2179_ == 0)
{
return v_bs_2178_;
}
else
{
lean_object* v_v_2180_; lean_object* v_msg_2181_; lean_object* v___x_2182_; lean_object* v_bs_x27_2183_; size_t v___x_2184_; size_t v___x_2185_; lean_object* v___x_2186_; 
v_v_2180_ = lean_array_uget_borrowed(v_bs_2178_, v_i_2177_);
v_msg_2181_ = lean_ctor_get(v_v_2180_, 1);
lean_inc_ref(v_msg_2181_);
v___x_2182_ = lean_unsigned_to_nat(0u);
v_bs_x27_2183_ = lean_array_uset(v_bs_2178_, v_i_2177_, v___x_2182_);
v___x_2184_ = ((size_t)1ULL);
v___x_2185_ = lean_usize_add(v_i_2177_, v___x_2184_);
v___x_2186_ = lean_array_uset(v_bs_x27_2183_, v_i_2177_, v_msg_2181_);
v_i_2177_ = v___x_2185_;
v_bs_2178_ = v___x_2186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2188_, lean_object* v_i_2189_, lean_object* v_bs_2190_){
_start:
{
size_t v_sz_boxed_2191_; size_t v_i_boxed_2192_; lean_object* v_res_2193_; 
v_sz_boxed_2191_ = lean_unbox_usize(v_sz_2188_);
lean_dec(v_sz_2188_);
v_i_boxed_2192_ = lean_unbox_usize(v_i_2189_);
lean_dec(v_i_2189_);
v_res_2193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(v_sz_boxed_2191_, v_i_boxed_2192_, v_bs_2190_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(lean_object* v_oldTraces_2194_, lean_object* v_data_2195_, lean_object* v_ref_2196_, lean_object* v_msg_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_toCold_2203_; lean_object* v_options_2204_; lean_object* v_currRecDepth_2205_; lean_object* v_maxRecDepth_2206_; lean_object* v_ref_2207_; lean_object* v_currNamespace_2208_; lean_object* v_openDecls_2209_; lean_object* v_initHeartbeats_2210_; lean_object* v_maxHeartbeats_2211_; lean_object* v_currMacroScope_2212_; uint8_t v_diag_2213_; uint8_t v_suppressElabErrors_2214_; lean_object* v___x_2215_; lean_object* v_traceState_2216_; lean_object* v_traces_2217_; lean_object* v_ref_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; size_t v_sz_2221_; size_t v___x_2222_; lean_object* v___x_2223_; lean_object* v_msg_2224_; lean_object* v___x_2225_; lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2263_; 
v_toCold_2203_ = lean_ctor_get(v___y_2200_, 0);
v_options_2204_ = lean_ctor_get(v___y_2200_, 1);
v_currRecDepth_2205_ = lean_ctor_get(v___y_2200_, 2);
v_maxRecDepth_2206_ = lean_ctor_get(v___y_2200_, 3);
v_ref_2207_ = lean_ctor_get(v___y_2200_, 4);
v_currNamespace_2208_ = lean_ctor_get(v___y_2200_, 5);
v_openDecls_2209_ = lean_ctor_get(v___y_2200_, 6);
v_initHeartbeats_2210_ = lean_ctor_get(v___y_2200_, 7);
v_maxHeartbeats_2211_ = lean_ctor_get(v___y_2200_, 8);
v_currMacroScope_2212_ = lean_ctor_get(v___y_2200_, 9);
v_diag_2213_ = lean_ctor_get_uint8(v___y_2200_, sizeof(void*)*10);
v_suppressElabErrors_2214_ = lean_ctor_get_uint8(v___y_2200_, sizeof(void*)*10 + 1);
v___x_2215_ = lean_st_ref_get(v___y_2201_);
v_traceState_2216_ = lean_ctor_get(v___x_2215_, 4);
lean_inc_ref(v_traceState_2216_);
lean_dec(v___x_2215_);
v_traces_2217_ = lean_ctor_get(v_traceState_2216_, 0);
lean_inc_ref(v_traces_2217_);
lean_dec_ref(v_traceState_2216_);
v_ref_2218_ = l_Lean_replaceRef(v_ref_2196_, v_ref_2207_);
lean_inc(v_currMacroScope_2212_);
lean_inc(v_maxHeartbeats_2211_);
lean_inc(v_initHeartbeats_2210_);
lean_inc(v_openDecls_2209_);
lean_inc(v_currNamespace_2208_);
lean_inc(v_maxRecDepth_2206_);
lean_inc(v_currRecDepth_2205_);
lean_inc_ref(v_options_2204_);
lean_inc_ref(v_toCold_2203_);
v___x_2219_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2219_, 0, v_toCold_2203_);
lean_ctor_set(v___x_2219_, 1, v_options_2204_);
lean_ctor_set(v___x_2219_, 2, v_currRecDepth_2205_);
lean_ctor_set(v___x_2219_, 3, v_maxRecDepth_2206_);
lean_ctor_set(v___x_2219_, 4, v_ref_2218_);
lean_ctor_set(v___x_2219_, 5, v_currNamespace_2208_);
lean_ctor_set(v___x_2219_, 6, v_openDecls_2209_);
lean_ctor_set(v___x_2219_, 7, v_initHeartbeats_2210_);
lean_ctor_set(v___x_2219_, 8, v_maxHeartbeats_2211_);
lean_ctor_set(v___x_2219_, 9, v_currMacroScope_2212_);
lean_ctor_set_uint8(v___x_2219_, sizeof(void*)*10, v_diag_2213_);
lean_ctor_set_uint8(v___x_2219_, sizeof(void*)*10 + 1, v_suppressElabErrors_2214_);
v___x_2220_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2217_);
lean_dec_ref(v_traces_2217_);
v_sz_2221_ = lean_array_size(v___x_2220_);
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(v_sz_2221_, v___x_2222_, v___x_2220_);
v_msg_2224_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2224_, 0, v_data_2195_);
lean_ctor_set(v_msg_2224_, 1, v_msg_2197_);
lean_ctor_set(v_msg_2224_, 2, v___x_2223_);
v___x_2225_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_2224_, v___y_2198_, v___y_2199_, v___x_2219_, v___y_2201_);
lean_dec_ref_known(v___x_2219_, 10);
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2263_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2263_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v_traceState_2231_; lean_object* v_env_2232_; lean_object* v_nextMacroScope_2233_; lean_object* v_ngen_2234_; lean_object* v_auxDeclNGen_2235_; lean_object* v_cache_2236_; lean_object* v_messages_2237_; lean_object* v_infoState_2238_; lean_object* v_snapshotTasks_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2262_; 
v___x_2230_ = lean_st_ref_take(v___y_2201_);
v_traceState_2231_ = lean_ctor_get(v___x_2230_, 4);
v_env_2232_ = lean_ctor_get(v___x_2230_, 0);
v_nextMacroScope_2233_ = lean_ctor_get(v___x_2230_, 1);
v_ngen_2234_ = lean_ctor_get(v___x_2230_, 2);
v_auxDeclNGen_2235_ = lean_ctor_get(v___x_2230_, 3);
v_cache_2236_ = lean_ctor_get(v___x_2230_, 5);
v_messages_2237_ = lean_ctor_get(v___x_2230_, 6);
v_infoState_2238_ = lean_ctor_get(v___x_2230_, 7);
v_snapshotTasks_2239_ = lean_ctor_get(v___x_2230_, 8);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2241_ = v___x_2230_;
v_isShared_2242_ = v_isSharedCheck_2262_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_snapshotTasks_2239_);
lean_inc(v_infoState_2238_);
lean_inc(v_messages_2237_);
lean_inc(v_cache_2236_);
lean_inc(v_traceState_2231_);
lean_inc(v_auxDeclNGen_2235_);
lean_inc(v_ngen_2234_);
lean_inc(v_nextMacroScope_2233_);
lean_inc(v_env_2232_);
lean_dec(v___x_2230_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2262_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
uint64_t v_tid_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2260_; 
v_tid_2243_ = lean_ctor_get_uint64(v_traceState_2231_, sizeof(void*)*1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_traceState_2231_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; 
v_unused_2261_ = lean_ctor_get(v_traceState_2231_, 0);
lean_dec(v_unused_2261_);
v___x_2245_ = v_traceState_2231_;
v_isShared_2246_ = v_isSharedCheck_2260_;
goto v_resetjp_2244_;
}
else
{
lean_dec(v_traceState_2231_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2260_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_ref_2196_);
lean_ctor_set(v___x_2247_, 1, v_a_2226_);
v___x_2248_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2194_, v___x_2247_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2248_);
v___x_2250_ = v___x_2245_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2248_);
lean_ctor_set_uint64(v_reuseFailAlloc_2259_, sizeof(void*)*1, v_tid_2243_);
v___x_2250_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2252_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 4, v___x_2250_);
v___x_2252_ = v___x_2241_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_env_2232_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_nextMacroScope_2233_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_ngen_2234_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_auxDeclNGen_2235_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2258_, 5, v_cache_2236_);
lean_ctor_set(v_reuseFailAlloc_2258_, 6, v_messages_2237_);
lean_ctor_set(v_reuseFailAlloc_2258_, 7, v_infoState_2238_);
lean_ctor_set(v_reuseFailAlloc_2258_, 8, v_snapshotTasks_2239_);
v___x_2252_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2253_ = lean_st_ref_put(v___y_2201_, v___x_2252_);
v___x_2254_ = lean_box(0);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2254_);
v___x_2256_ = v___x_2228_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg___boxed(lean_object* v_oldTraces_2264_, lean_object* v_data_2265_, lean_object* v_ref_2266_, lean_object* v_msg_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2264_, v_data_2265_, v_ref_2266_, v_msg_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2273_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0));
v___x_2276_ = l_Lean_stringToMessageData(v___x_2275_);
return v___x_2276_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2277_; double v___x_2278_; 
v___x_2277_ = lean_unsigned_to_nat(1000u);
v___x_2278_ = lean_float_of_nat(v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(lean_object* v_cls_2279_, uint8_t v_collapsed_2280_, lean_object* v_tag_2281_, lean_object* v_opts_2282_, uint8_t v_clsEnabled_2283_, lean_object* v_oldTraces_2284_, lean_object* v_msg_2285_, lean_object* v_resStartStop_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_fst_2294_; lean_object* v_snd_2295_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v_data_2299_; lean_object* v_fst_2310_; lean_object* v_snd_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___y_2315_; lean_object* v_a_2316_; uint8_t v___y_2331_; double v___y_2362_; 
v_fst_2294_ = lean_ctor_get(v_resStartStop_2286_, 0);
lean_inc(v_fst_2294_);
v_snd_2295_ = lean_ctor_get(v_resStartStop_2286_, 1);
lean_inc(v_snd_2295_);
lean_dec_ref(v_resStartStop_2286_);
v_fst_2310_ = lean_ctor_get(v_snd_2295_, 0);
lean_inc(v_fst_2310_);
v_snd_2311_ = lean_ctor_get(v_snd_2295_, 1);
lean_inc(v_snd_2311_);
lean_dec(v_snd_2295_);
v___x_2312_ = l_Lean_trace_profiler;
v___x_2313_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_2282_, v___x_2312_);
if (v___x_2313_ == 0)
{
v___y_2331_ = v___x_2313_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2368_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_2282_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; double v___x_2371_; double v___x_2372_; double v___x_2373_; 
v___x_2369_ = l_Lean_trace_profiler_threshold;
v___x_2370_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2282_, v___x_2369_);
v___x_2371_ = lean_float_of_nat(v___x_2370_);
v___x_2372_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2);
v___x_2373_ = lean_float_div(v___x_2371_, v___x_2372_);
v___y_2362_ = v___x_2373_;
goto v___jp_2361_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; double v___x_2376_; 
v___x_2374_ = l_Lean_trace_profiler_threshold;
v___x_2375_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2282_, v___x_2374_);
v___x_2376_ = lean_float_of_nat(v___x_2375_);
v___y_2362_ = v___x_2376_;
goto v___jp_2361_;
}
}
v___jp_2296_:
{
lean_object* v___x_2300_; 
lean_inc(v___y_2297_);
v___x_2300_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2284_, v_data_2299_, v___y_2297_, v___y_2298_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; 
lean_dec_ref_known(v___x_2300_, 1);
v___x_2301_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_fst_2294_);
return v___x_2301_;
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v_fst_2294_);
v_a_2302_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2300_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2300_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
v___jp_2314_:
{
uint8_t v_result_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; double v___x_2320_; lean_object* v_data_2321_; 
v_result_2317_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_fst_2294_);
v___x_2318_ = lean_box(v_result_2317_);
v___x_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
v___x_2320_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_2281_);
lean_inc_ref(v___x_2319_);
lean_inc(v_cls_2279_);
v_data_2321_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2321_, 0, v_cls_2279_);
lean_ctor_set(v_data_2321_, 1, v___x_2319_);
lean_ctor_set(v_data_2321_, 2, v_tag_2281_);
lean_ctor_set_float(v_data_2321_, sizeof(void*)*3, v___x_2320_);
lean_ctor_set_float(v_data_2321_, sizeof(void*)*3 + 8, v___x_2320_);
lean_ctor_set_uint8(v_data_2321_, sizeof(void*)*3 + 16, v_collapsed_2280_);
if (v___x_2313_ == 0)
{
lean_dec_ref_known(v___x_2319_, 1);
lean_dec(v_snd_2311_);
lean_dec(v_fst_2310_);
lean_dec_ref(v_tag_2281_);
lean_dec(v_cls_2279_);
v___y_2297_ = v___y_2315_;
v___y_2298_ = v_a_2316_;
v_data_2299_ = v_data_2321_;
goto v___jp_2296_;
}
else
{
lean_object* v_data_2322_; double v___x_2323_; double v___x_2324_; 
lean_dec_ref_known(v_data_2321_, 3);
v_data_2322_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2322_, 0, v_cls_2279_);
lean_ctor_set(v_data_2322_, 1, v___x_2319_);
lean_ctor_set(v_data_2322_, 2, v_tag_2281_);
v___x_2323_ = lean_unbox_float(v_fst_2310_);
lean_dec(v_fst_2310_);
lean_ctor_set_float(v_data_2322_, sizeof(void*)*3, v___x_2323_);
v___x_2324_ = lean_unbox_float(v_snd_2311_);
lean_dec(v_snd_2311_);
lean_ctor_set_float(v_data_2322_, sizeof(void*)*3 + 8, v___x_2324_);
lean_ctor_set_uint8(v_data_2322_, sizeof(void*)*3 + 16, v_collapsed_2280_);
v___y_2297_ = v___y_2315_;
v___y_2298_ = v_a_2316_;
v_data_2299_ = v_data_2322_;
goto v___jp_2296_;
}
}
v___jp_2325_:
{
lean_object* v_ref_2326_; lean_object* v___x_2327_; 
v_ref_2326_ = lean_ctor_get(v___y_2291_, 4);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2291_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2287_);
lean_inc(v_fst_2294_);
v___x_2327_ = lean_apply_8(v_msg_2285_, v_fst_2294_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, lean_box(0));
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___y_2315_ = v_ref_2326_;
v_a_2316_ = v_a_2328_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2329_; 
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1);
v___y_2315_ = v_ref_2326_;
v_a_2316_ = v___x_2329_;
goto v___jp_2314_;
}
}
v___jp_2330_:
{
if (v_clsEnabled_2283_ == 0)
{
if (v___y_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v_traceState_2333_; lean_object* v_env_2334_; lean_object* v_nextMacroScope_2335_; lean_object* v_ngen_2336_; lean_object* v_auxDeclNGen_2337_; lean_object* v_cache_2338_; lean_object* v_messages_2339_; lean_object* v_infoState_2340_; lean_object* v_snapshotTasks_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v_snd_2311_);
lean_dec(v_fst_2310_);
lean_dec_ref(v_msg_2285_);
lean_dec_ref(v_tag_2281_);
lean_dec(v_cls_2279_);
v___x_2332_ = lean_st_ref_take(v___y_2292_);
v_traceState_2333_ = lean_ctor_get(v___x_2332_, 4);
v_env_2334_ = lean_ctor_get(v___x_2332_, 0);
v_nextMacroScope_2335_ = lean_ctor_get(v___x_2332_, 1);
v_ngen_2336_ = lean_ctor_get(v___x_2332_, 2);
v_auxDeclNGen_2337_ = lean_ctor_get(v___x_2332_, 3);
v_cache_2338_ = lean_ctor_get(v___x_2332_, 5);
v_messages_2339_ = lean_ctor_get(v___x_2332_, 6);
v_infoState_2340_ = lean_ctor_get(v___x_2332_, 7);
v_snapshotTasks_2341_ = lean_ctor_get(v___x_2332_, 8);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2343_ = v___x_2332_;
v_isShared_2344_ = v_isSharedCheck_2360_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_snapshotTasks_2341_);
lean_inc(v_infoState_2340_);
lean_inc(v_messages_2339_);
lean_inc(v_cache_2338_);
lean_inc(v_traceState_2333_);
lean_inc(v_auxDeclNGen_2337_);
lean_inc(v_ngen_2336_);
lean_inc(v_nextMacroScope_2335_);
lean_inc(v_env_2334_);
lean_dec(v___x_2332_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2360_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
uint64_t v_tid_2345_; lean_object* v_traces_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2359_; 
v_tid_2345_ = lean_ctor_get_uint64(v_traceState_2333_, sizeof(void*)*1);
v_traces_2346_ = lean_ctor_get(v_traceState_2333_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_traceState_2333_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2348_ = v_traceState_2333_;
v_isShared_2349_ = v_isSharedCheck_2359_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_traces_2346_);
lean_dec(v_traceState_2333_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2359_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2284_, v_traces_2346_);
lean_dec_ref(v_traces_2346_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2350_);
v___x_2352_ = v___x_2348_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2350_);
lean_ctor_set_uint64(v_reuseFailAlloc_2358_, sizeof(void*)*1, v_tid_2345_);
v___x_2352_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 4, v___x_2352_);
v___x_2354_ = v___x_2343_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_env_2334_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_nextMacroScope_2335_);
lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_ngen_2336_);
lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_auxDeclNGen_2337_);
lean_ctor_set(v_reuseFailAlloc_2357_, 4, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2357_, 5, v_cache_2338_);
lean_ctor_set(v_reuseFailAlloc_2357_, 6, v_messages_2339_);
lean_ctor_set(v_reuseFailAlloc_2357_, 7, v_infoState_2340_);
lean_ctor_set(v_reuseFailAlloc_2357_, 8, v_snapshotTasks_2341_);
v___x_2354_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_st_ref_put(v___y_2292_, v___x_2354_);
v___x_2356_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_fst_2294_);
return v___x_2356_;
}
}
}
}
}
else
{
goto v___jp_2325_;
}
}
else
{
goto v___jp_2325_;
}
}
v___jp_2361_:
{
double v___x_2363_; double v___x_2364_; double v___x_2365_; uint8_t v___x_2366_; 
v___x_2363_ = lean_unbox_float(v_snd_2311_);
v___x_2364_ = lean_unbox_float(v_fst_2310_);
v___x_2365_ = lean_float_sub(v___x_2363_, v___x_2364_);
v___x_2366_ = lean_float_decLt(v___y_2362_, v___x_2365_);
v___y_2331_ = v___x_2366_;
goto v___jp_2330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___boxed(lean_object* v_cls_2377_, lean_object* v_collapsed_2378_, lean_object* v_tag_2379_, lean_object* v_opts_2380_, lean_object* v_clsEnabled_2381_, lean_object* v_oldTraces_2382_, lean_object* v_msg_2383_, lean_object* v_resStartStop_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v_collapsed_boxed_2392_; uint8_t v_clsEnabled_boxed_2393_; lean_object* v_res_2394_; 
v_collapsed_boxed_2392_ = lean_unbox(v_collapsed_2378_);
v_clsEnabled_boxed_2393_ = lean_unbox(v_clsEnabled_2381_);
v_res_2394_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v_cls_2377_, v_collapsed_boxed_2392_, v_tag_2379_, v_opts_2380_, v_clsEnabled_boxed_2393_, v_oldTraces_2382_, v_msg_2383_, v_resStartStop_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec_ref(v_opts_2380_);
return v_res_2394_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_box(0);
v___x_2396_ = lean_unsigned_to_nat(16u);
v___x_2397_ = lean_mk_array(v___x_2396_, v___x_2395_);
return v___x_2397_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0);
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
lean_ctor_set(v___x_2400_, 1, v___x_2398_);
return v___x_2400_;
}
}
static double _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2(void){
_start:
{
lean_object* v___x_2401_; double v___x_2402_; 
v___x_2401_ = lean_unsigned_to_nat(1000000000u);
v___x_2402_ = lean_float_of_nat(v___x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(lean_object* v_className_2403_, lean_object* v_type_2404_, lean_object* v_extraDeps_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_options_2413_; lean_object* v_toCold_2414_; uint8_t v_hasTrace_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_options_2413_ = lean_ctor_get(v_a_2410_, 1);
v_toCold_2414_ = lean_ctor_get(v_a_2410_, 0);
v_hasTrace_2415_ = lean_ctor_get_uint8(v_options_2413_, sizeof(void*)*1);
v___x_2416_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v___x_2417_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1);
v___x_2418_ = lean_box(0);
lean_inc_ref(v_type_2404_);
v___x_2419_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v___x_2417_, v_type_2404_, v___x_2418_);
if (v_hasTrace_2415_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2403_, v_extraDeps_2405_, v___x_2416_, v___x_2419_, v_type_2404_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
return v___x_2420_;
}
else
{
lean_object* v_inheritedTraceOptions_2421_; lean_object* v___f_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v_a_2430_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v_a_2445_; 
v_inheritedTraceOptions_2421_ = lean_ctor_get(v_toCold_2414_, 4);
lean_inc_ref(v_type_2404_);
lean_inc(v_className_2403_);
v___f_2422_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2422_, 0, v_className_2403_);
lean_closure_set(v___f_2422_, 1, v_type_2404_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2424_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_2425_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2426_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2421_, v_options_2413_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2495_ = l_Lean_trace_profiler;
v___x_2496_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_2413_, v___x_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; 
lean_dec_ref(v___f_2422_);
v___x_2497_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2403_, v_extraDeps_2405_, v___x_2416_, v___x_2419_, v_type_2404_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
return v___x_2497_;
}
else
{
goto v___jp_2454_;
}
}
else
{
goto v___jp_2454_;
}
v___jp_2427_:
{
lean_object* v___x_2431_; double v___x_2432_; double v___x_2433_; double v___x_2434_; double v___x_2435_; double v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2431_ = lean_io_mono_nanos_now();
v___x_2432_ = lean_float_of_nat(v___y_2428_);
v___x_2433_ = lean_float_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2);
v___x_2434_ = lean_float_div(v___x_2432_, v___x_2433_);
v___x_2435_ = lean_float_of_nat(v___x_2431_);
v___x_2436_ = lean_float_div(v___x_2435_, v___x_2433_);
v___x_2437_ = lean_box_float(v___x_2434_);
v___x_2438_ = lean_box_float(v___x_2436_);
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_a_2430_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_2423_, v_hasTrace_2415_, v___x_2424_, v_options_2413_, v___x_2426_, v___y_2429_, v___f_2422_, v___x_2440_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
return v___x_2441_;
}
v___jp_2442_:
{
lean_object* v___x_2446_; double v___x_2447_; double v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2446_ = lean_io_get_num_heartbeats();
v___x_2447_ = lean_float_of_nat(v___y_2444_);
v___x_2448_ = lean_float_of_nat(v___x_2446_);
v___x_2449_ = lean_box_float(v___x_2447_);
v___x_2450_ = lean_box_float(v___x_2448_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_a_2445_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_2423_, v_hasTrace_2415_, v___x_2424_, v_options_2413_, v___x_2426_, v___y_2443_, v___f_2422_, v___x_2452_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
return v___x_2453_;
}
v___jp_2454_:
{
lean_object* v___x_2455_; lean_object* v_a_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2455_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v_a_2411_);
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
v___x_2457_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2458_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_2413_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_io_mono_nanos_now();
v___x_2460_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2403_, v_extraDeps_2405_, v___x_2416_, v___x_2419_, v_type_2404_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set_tag(v___x_2463_, 1);
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
v___y_2428_ = v___x_2459_;
v___y_2429_ = v_a_2456_;
v_a_2430_ = v___x_2466_;
goto v___jp_2427_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
v_a_2469_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2460_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2460_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set_tag(v___x_2471_, 0);
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
v___y_2428_ = v___x_2459_;
v___y_2429_ = v_a_2456_;
v_a_2430_ = v___x_2474_;
goto v___jp_2427_;
}
}
}
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = lean_io_get_num_heartbeats();
v___x_2478_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2403_, v_extraDeps_2405_, v___x_2416_, v___x_2419_, v_type_2404_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set_tag(v___x_2481_, 1);
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
v___y_2443_ = v_a_2456_;
v___y_2444_ = v___x_2477_;
v_a_2445_ = v___x_2484_;
goto v___jp_2442_;
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
v_a_2487_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2478_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2478_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set_tag(v___x_2489_, 0);
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
v___y_2443_ = v_a_2456_;
v___y_2444_ = v___x_2477_;
v_a_2445_ = v___x_2492_;
goto v___jp_2442_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed(lean_object* v_className_2498_, lean_object* v_type_2499_, lean_object* v_extraDeps_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(v_className_2498_, v_type_2499_, v_extraDeps_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(lean_object* v_00_u03b1_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_x_2510_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2519_, lean_object* v_x_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(v_00_u03b1_2519_, v_x_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(lean_object* v_oldTraces_2529_, lean_object* v_data_2530_, lean_object* v_ref_2531_, lean_object* v_msg_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2529_, v_data_2530_, v_ref_2531_, v_msg_2532_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___boxed(lean_object* v_oldTraces_2541_, lean_object* v_data_2542_, lean_object* v_ref_2543_, lean_object* v_msg_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(v_oldTraces_2541_, v_data_2542_, v_ref_2543_, v_msg_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2552_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
return v___x_2557_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
v___x_2559_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
lean_ctor_set(v___x_2559_, 2, v___x_2558_);
lean_ctor_set(v___x_2559_, 3, v___x_2558_);
lean_ctor_set(v___x_2559_, 4, v___x_2558_);
lean_ctor_set(v___x_2559_, 5, v___x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(lean_object* v_env_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; lean_object* v_nextMacroScope_2565_; lean_object* v_ngen_2566_; lean_object* v_auxDeclNGen_2567_; lean_object* v_traceState_2568_; lean_object* v_messages_2569_; lean_object* v_infoState_2570_; lean_object* v_snapshotTasks_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2597_; 
v___x_2564_ = lean_st_ref_take(v___y_2562_);
v_nextMacroScope_2565_ = lean_ctor_get(v___x_2564_, 1);
v_ngen_2566_ = lean_ctor_get(v___x_2564_, 2);
v_auxDeclNGen_2567_ = lean_ctor_get(v___x_2564_, 3);
v_traceState_2568_ = lean_ctor_get(v___x_2564_, 4);
v_messages_2569_ = lean_ctor_get(v___x_2564_, 6);
v_infoState_2570_ = lean_ctor_get(v___x_2564_, 7);
v_snapshotTasks_2571_ = lean_ctor_get(v___x_2564_, 8);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; lean_object* v_unused_2599_; 
v_unused_2598_ = lean_ctor_get(v___x_2564_, 5);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v___x_2564_, 0);
lean_dec(v_unused_2599_);
v___x_2573_ = v___x_2564_;
v_isShared_2574_ = v_isSharedCheck_2597_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snapshotTasks_2571_);
lean_inc(v_infoState_2570_);
lean_inc(v_messages_2569_);
lean_inc(v_traceState_2568_);
lean_inc(v_auxDeclNGen_2567_);
lean_inc(v_ngen_2566_);
lean_inc(v_nextMacroScope_2565_);
lean_dec(v___x_2564_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2597_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 5, v___x_2575_);
lean_ctor_set(v___x_2573_, 0, v_env_2560_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_env_2560_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_nextMacroScope_2565_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_ngen_2566_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_auxDeclNGen_2567_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_traceState_2568_);
lean_ctor_set(v_reuseFailAlloc_2596_, 5, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2596_, 6, v_messages_2569_);
lean_ctor_set(v_reuseFailAlloc_2596_, 7, v_infoState_2570_);
lean_ctor_set(v_reuseFailAlloc_2596_, 8, v_snapshotTasks_2571_);
v___x_2577_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_mctx_2580_; lean_object* v_zetaDeltaFVarIds_2581_; lean_object* v_postponed_2582_; lean_object* v_diag_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2594_; 
v___x_2578_ = lean_st_ref_put(v___y_2562_, v___x_2577_);
v___x_2579_ = lean_st_ref_take(v___y_2561_);
v_mctx_2580_ = lean_ctor_get(v___x_2579_, 0);
v_zetaDeltaFVarIds_2581_ = lean_ctor_get(v___x_2579_, 2);
v_postponed_2582_ = lean_ctor_get(v___x_2579_, 3);
v_diag_2583_ = lean_ctor_get(v___x_2579_, 4);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v___x_2579_, 1);
lean_dec(v_unused_2595_);
v___x_2585_ = v___x_2579_;
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_diag_2583_);
lean_inc(v_postponed_2582_);
lean_inc(v_zetaDeltaFVarIds_2581_);
lean_inc(v_mctx_2580_);
lean_dec(v___x_2579_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2594_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 1, v___x_2587_);
v___x_2589_ = v___x_2585_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_mctx_2580_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v_zetaDeltaFVarIds_2581_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v_postponed_2582_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v_diag_2583_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_st_ref_put(v___y_2561_, v___x_2589_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___boxed(lean_object* v_env_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v_env_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec(v___y_2601_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(lean_object* v_env_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v_env_2605_, v___y_2609_, v___y_2611_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___boxed(lean_object* v_env_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(v_env_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
return v_res_2622_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(lean_object* v_mkCmd_2626_, lean_object* v_a_2627_, lean_object* v___x_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2631_);
lean_inc(v___y_2630_);
lean_inc_ref(v___y_2629_);
lean_inc_ref(v_a_2627_);
v___x_2636_ = lean_apply_5(v_mkCmd_2626_, v_a_2627_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
v___x_2637_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_2636_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v_a_2627_);
return v___x_2637_;
}
else
{
lean_object* v_a_2638_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; uint8_t v___y_2664_; uint8_t v___x_2688_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
v___x_2688_ = l_Lean_Exception_isInterrupt(v_a_2638_);
if (v___x_2688_ == 0)
{
uint8_t v___x_2689_; 
lean_inc(v_a_2638_);
v___x_2689_ = l_Lean_Exception_isRuntime(v_a_2638_);
v___y_2664_ = v___x_2689_;
goto v___jp_2663_;
}
else
{
v___y_2664_ = v___x_2688_;
goto v___jp_2663_;
}
v___jp_2639_:
{
lean_object* v___x_2646_; 
lean_dec_ref(v___y_2640_);
v___x_2646_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v___x_2628_, v___y_2643_, v___y_2645_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v___x_2646_, 0);
lean_dec(v_unused_2654_);
v___x_2648_ = v___x_2646_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_dec(v___x_2646_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set_tag(v___x_2648_, 1);
lean_ctor_set(v___x_2648_, 0, v_a_2638_);
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2638_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_a_2638_);
v_a_2655_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2646_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2646_);
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
v___jp_2663_:
{
if (v___y_2664_ == 0)
{
lean_object* v_options_2665_; uint8_t v_hasTrace_2666_; 
lean_dec_ref_known(v___x_2637_, 1);
v_options_2665_ = lean_ctor_get(v___y_2633_, 1);
v_hasTrace_2666_ = lean_ctor_get_uint8(v_options_2665_, sizeof(void*)*1);
if (v_hasTrace_2666_ == 0)
{
lean_dec_ref(v_a_2627_);
v___y_2640_ = v___y_2629_;
v___y_2641_ = v___y_2630_;
v___y_2642_ = v___y_2631_;
v___y_2643_ = v___y_2632_;
v___y_2644_ = v___y_2633_;
v___y_2645_ = v___y_2634_;
goto v___jp_2639_;
}
else
{
lean_object* v_toCold_2667_; lean_object* v_inheritedTraceOptions_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_toCold_2667_ = lean_ctor_get(v___y_2633_, 0);
v_inheritedTraceOptions_2668_ = lean_ctor_get(v_toCold_2667_, 4);
v___x_2669_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2670_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2671_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2668_, v_options_2665_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_dec_ref(v_a_2627_);
v___y_2640_ = v___y_2629_;
v___y_2641_ = v___y_2630_;
v___y_2642_ = v___y_2631_;
v___y_2643_ = v___y_2632_;
v___y_2644_ = v___y_2633_;
v___y_2645_ = v___y_2634_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2672_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1);
v___x_2673_ = l_Lean_MessageData_ofExpr(v_a_2627_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
lean_inc(v_a_2638_);
v___x_2677_ = l_Lean_Exception_toMessageData(v_a_2638_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v___x_2669_, v___x_2678_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_dec_ref_known(v___x_2679_, 1);
v___y_2640_ = v___y_2629_;
v___y_2641_ = v___y_2630_;
v___y_2642_ = v___y_2631_;
v___y_2643_ = v___y_2632_;
v___y_2644_ = v___y_2633_;
v___y_2645_ = v___y_2634_;
goto v___jp_2639_;
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v_a_2638_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___x_2628_);
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
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
}
else
{
lean_dec(v_a_2638_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v_a_2627_);
return v___x_2637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed(lean_object* v_mkCmd_2690_, lean_object* v_a_2691_, lean_object* v___x_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(v_mkCmd_2690_, v_a_2691_, v___x_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
return v_res_2700_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_ctor_set(v___x_2706_, 2, v___x_2705_);
lean_ctor_set(v___x_2706_, 3, v___x_2705_);
lean_ctor_set(v___x_2706_, 4, v___x_2704_);
lean_ctor_set(v___x_2706_, 5, v___x_2704_);
lean_ctor_set(v___x_2706_, 6, v___x_2704_);
lean_ctor_set(v___x_2706_, 7, v___x_2704_);
lean_ctor_set(v___x_2706_, 8, v___x_2704_);
lean_ctor_set(v___x_2706_, 9, v___x_2704_);
lean_ctor_set(v___x_2706_, 10, v___x_2704_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_unsigned_to_nat(32u);
v___x_2708_ = lean_mk_empty_array_with_capacity(v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2710_ = ((size_t)5ULL);
v___x_2711_ = lean_unsigned_to_nat(0u);
v___x_2712_ = lean_unsigned_to_nat(32u);
v___x_2713_ = lean_mk_empty_array_with_capacity(v___x_2712_);
v___x_2714_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3);
v___x_2715_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v___x_2713_);
lean_ctor_set(v___x_2715_, 2, v___x_2711_);
lean_ctor_set(v___x_2715_, 3, v___x_2711_);
lean_ctor_set_usize(v___x_2715_, 4, v___x_2710_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2716_ = lean_box(1);
v___x_2717_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4);
v___x_2718_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
v___x_2719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v___x_2717_);
lean_ctor_set(v___x_2719_, 2, v___x_2716_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(lean_object* v_msgData_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; lean_object* v_env_2724_; lean_object* v___x_2725_; lean_object* v_scopes_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v_opts_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2723_ = lean_st_ref_get(v___y_2721_);
v_env_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc_ref(v_env_2724_);
lean_dec(v___x_2723_);
v___x_2725_ = lean_st_ref_get(v___y_2721_);
v_scopes_2726_ = lean_ctor_get(v___x_2725_, 2);
lean_inc(v_scopes_2726_);
lean_dec(v___x_2725_);
v___x_2727_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2728_ = l_List_head_x21___redArg(v___x_2727_, v_scopes_2726_);
lean_dec(v_scopes_2726_);
v_opts_2729_ = lean_ctor_get(v___x_2728_, 1);
lean_inc_ref(v_opts_2729_);
lean_dec(v___x_2728_);
v___x_2730_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2);
v___x_2731_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5);
v___x_2732_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2732_, 0, v_env_2724_);
lean_ctor_set(v___x_2732_, 1, v___x_2730_);
lean_ctor_set(v___x_2732_, 2, v___x_2731_);
lean_ctor_set(v___x_2732_, 3, v_opts_2729_);
v___x_2733_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_msgData_2720_);
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
lean_object* v___x_2773_; double v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
v___x_2775_ = 0;
v___x_2776_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_2777_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2777_, 0, v_cls_2739_);
lean_ctor_set(v___x_2777_, 1, v___x_2773_);
lean_ctor_set(v___x_2777_, 2, v___x_2776_);
lean_ctor_set_float(v___x_2777_, sizeof(void*)*3, v___x_2774_);
lean_ctor_set_float(v___x_2777_, sizeof(void*)*3 + 8, v___x_2774_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*3 + 16, v___x_2775_);
v___x_2778_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1));
v___x_2779_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v_a_2747_);
lean_ctor_set(v___x_2779_, 2, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_a_2745_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = l_Lean_PersistentArray_push___redArg(v_traces_2769_, v___x_2780_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2781_);
v___x_2783_ = v___x_2771_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2781_);
lean_ctor_set_uint64(v_reuseFailAlloc_2792_, sizeof(void*)*1, v_tid_2768_);
v___x_2783_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2785_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 9, v___x_2783_);
v___x_2785_ = v___x_2766_;
goto v_reusejp_2784_;
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
lean_ctor_set(v_reuseFailAlloc_2791_, 9, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2791_, 10, v_snapshotTasks_2762_);
lean_ctor_set(v_reuseFailAlloc_2791_, 11, v_prevLinterStates_2763_);
lean_ctor_set(v_reuseFailAlloc_2791_, 12, v_codeQualityEntryTasks_2764_);
v___x_2785_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2786_ = lean_st_ref_put(v___y_2742_, v___x_2785_);
v___x_2787_ = lean_box(0);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2787_);
v___x_2789_ = v___x_2749_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
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
lean_object* v_a_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; 
v_a_2836_ = lean_array_uget_borrowed(v_as_2822_, v_i_2824_);
lean_inc_ref(v___x_2820_);
lean_inc(v_a_2836_);
lean_inc_ref(v_mkCmd_2819_);
v___f_2837_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2837_, 0, v_mkCmd_2819_);
lean_closure_set(v___f_2837_, 1, v_a_2836_);
lean_closure_set(v___f_2837_, 2, v___x_2820_);
v___x_2838_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2837_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = l_Lean_Elab_Command_elabCommand(v_a_2839_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_scopes_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v_opts_2847_; uint8_t v_hasTrace_2848_; lean_object* v___x_2849_; 
lean_dec_ref_known(v___x_2840_, 1);
v___x_2841_ = l_Lean_inheritedTraceOptions;
v___x_2842_ = lean_st_ref_get(v___x_2841_);
v___x_2843_ = lean_st_ref_get(v___y_2827_);
v_scopes_2844_ = lean_ctor_get(v___x_2843_, 2);
lean_inc(v_scopes_2844_);
lean_dec(v___x_2843_);
v___x_2845_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2846_ = l_List_head_x21___redArg(v___x_2845_, v_scopes_2844_);
lean_dec(v_scopes_2844_);
v_opts_2847_ = lean_ctor_get(v___x_2846_, 1);
lean_inc_ref(v_opts_2847_);
lean_dec(v___x_2846_);
v_hasTrace_2848_ = lean_ctor_get_uint8(v_opts_2847_, sizeof(void*)*1);
v___x_2849_ = lean_box(0);
if (v_hasTrace_2848_ == 0)
{
lean_dec_ref(v_opts_2847_);
lean_dec(v___x_2842_);
v_a_2830_ = v___x_2849_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2851_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2852_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2842_, v_opts_2847_, v___x_2851_);
lean_dec_ref(v_opts_2847_);
lean_dec(v___x_2842_);
if (v___x_2852_ == 0)
{
v_a_2830_ = v___x_2849_;
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
lean_inc(v_a_2836_);
v___x_2859_ = l_Lean_MessageData_ofExpr(v_a_2836_);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(v___x_2850_, v___x_2862_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_dec_ref_known(v___x_2863_, 1);
v_a_2830_ = v___x_2849_;
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
return v___x_2840_;
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_className_2821_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v_mkCmd_2819_);
v_a_2864_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2838_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2838_);
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
