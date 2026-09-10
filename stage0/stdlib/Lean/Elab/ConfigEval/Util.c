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
lean_object* v_toCold_755_; lean_object* v_options_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_toCold_755_ = lean_ctor_get(v___y_753_, 0);
v_options_756_ = lean_ctor_get(v_toCold_755_, 2);
v___x_757_ = l_Lean_Elab_pp_macroStack;
v___x_758_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec(v_macroStack_752_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v_msgData_751_);
return v___x_759_;
}
else
{
if (lean_obj_tag(v_macroStack_752_) == 0)
{
lean_object* v___x_760_; 
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v_msgData_751_);
return v___x_760_;
}
else
{
lean_object* v_head_761_; lean_object* v_after_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_777_; 
v_head_761_ = lean_ctor_get(v_macroStack_752_, 0);
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
lean_ctor_set(v___x_764_, 0, v_msgData_751_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_msgData_751_);
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
v___x_774_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__22(v_msgData_773_, v_macroStack_752_);
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
lean_object* v___x_790_; lean_object* v_env_791_; lean_object* v___x_792_; lean_object* v_toCold_793_; lean_object* v_mctx_794_; lean_object* v_lctx_795_; lean_object* v_options_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_790_ = lean_st_ref_get(v___y_788_);
v_env_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc_ref(v_env_791_);
lean_dec(v___x_790_);
v___x_792_ = lean_st_ref_get(v___y_786_);
v_toCold_793_ = lean_ctor_get(v___y_787_, 0);
v_mctx_794_ = lean_ctor_get(v___x_792_, 0);
lean_inc_ref(v_mctx_794_);
lean_dec(v___x_792_);
v_lctx_795_ = lean_ctor_get(v___y_785_, 2);
v_options_796_ = lean_ctor_get(v_toCold_793_, 2);
lean_inc_ref(v_options_796_);
lean_inc_ref(v_lctx_795_);
v___x_797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_797_, 0, v_env_791_);
lean_ctor_set(v___x_797_, 1, v_mctx_794_);
lean_ctor_set(v___x_797_, 2, v_lctx_795_);
lean_ctor_set(v___x_797_, 3, v_options_796_);
v___x_798_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_msgData_784_);
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
v_ref_815_ = lean_ctor_get(v___y_812_, 2);
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
v_ref_890_ = lean_ctor_get(v___y_887_, 2);
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
v___x_927_ = lean_st_ref_put(v___y_888_, v___x_926_);
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
v_ref_951_ = lean_ctor_get(v___y_948_, 2);
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
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; uint8_t v___x_1027_; 
v___x_1024_ = lean_array_fget_borrowed(v_fst_1004_, v_i_1007_);
lean_inc(v___x_1024_);
v___x_1025_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v___x_1024_, v___y_1011_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = l_Lean_Expr_hasMVar(v_a_1026_);
lean_dec(v_a_1026_);
if (v___x_1027_ == 0)
{
goto v___jp_1020_;
}
else
{
if (v___x_1023_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec(v_i_1007_);
v___x_1028_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1029_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1028_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1029_;
}
else
{
goto v___jp_1020_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___boxed(lean_object* v___x_1030_, lean_object* v_fst_1031_, lean_object* v_range_1032_, lean_object* v_b_1033_, lean_object* v_i_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_1030_, v_fst_1031_, v_range_1032_, v_b_1033_, v_i_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v_range_1032_);
lean_dec_ref(v_fst_1031_);
lean_dec_ref(v___x_1030_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(lean_object* v_fst_1043_, lean_object* v_className_1044_, lean_object* v_as_1045_, size_t v_sz_1046_, size_t v_i_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_a_1057_; uint8_t v___x_1061_; 
v___x_1061_ = lean_usize_dec_lt(v_i_1047_, v_sz_1046_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_b_1048_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1063_ = l_Lean_instInhabitedExpr;
v_a_1064_ = lean_array_uget_borrowed(v_as_1045_, v_i_1047_);
v___x_1065_ = lean_array_get_borrowed(v___x_1063_, v_fst_1043_, v_a_1064_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___x_1065_);
v___x_1066_ = lean_infer_type(v___x_1065_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
v___x_1068_ = lean_whnf(v_a_1067_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_a_1069_, v___y_1052_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = l_Lean_Expr_isAppOfArity(v_a_1071_, v_className_1044_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec(v_a_1071_);
v___x_1074_ = lean_box(0);
v___x_1075_ = l_Lean_Expr_mvarId_x21(v___x_1065_);
v___x_1076_ = l_Lean_Elab_Term_synthesizeInstMVarCore(v___x_1075_, v___x_1074_, v___x_1074_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; uint8_t v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = lean_unbox(v_a_1077_);
lean_dec(v_a_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg___closed__1);
v___x_1080_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v___x_1079_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_dec_ref_known(v___x_1080_, 1);
v_a_1057_ = v_b_1048_;
goto v___jp_1056_;
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v_b_1048_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
v_a_1057_ = v_b_1048_;
goto v___jp_1056_;
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v_b_1048_);
v_a_1089_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1076_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1076_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = l_Lean_Expr_appArg_x21(v_a_1071_);
lean_dec(v_a_1071_);
v___x_1098_ = lean_array_push(v_b_1048_, v___x_1097_);
v_a_1057_ = v___x_1098_;
goto v___jp_1056_;
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_b_1048_);
v_a_1099_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1070_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1070_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v_b_1048_);
v_a_1107_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1068_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1068_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_b_1048_);
v_a_1115_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1066_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1066_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
v___jp_1056_:
{
size_t v___x_1058_; size_t v___x_1059_; 
v___x_1058_ = ((size_t)1ULL);
v___x_1059_ = lean_usize_add(v_i_1047_, v___x_1058_);
v_i_1047_ = v___x_1059_;
v_b_1048_ = v_a_1057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19___boxed(lean_object* v_fst_1123_, lean_object* v_className_1124_, lean_object* v_as_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
size_t v_sz_boxed_1136_; size_t v_i_boxed_1137_; lean_object* v_res_1138_; 
v_sz_boxed_1136_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1137_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v_fst_1123_, v_className_1124_, v_as_1125_, v_sz_boxed_1136_, v_i_boxed_1137_, v_b_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v_as_1125_);
lean_dec(v_className_1124_);
lean_dec_ref(v_fst_1123_);
return v_res_1138_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__0));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__3));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(lean_object* v_className_1147_, lean_object* v_extraDeps_1148_, lean_object* v_plan_1149_, lean_object* v_processing_1150_, lean_object* v_depTypes_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
size_t v_sz_1159_; size_t v___x_1160_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___x_1204_; 
v_sz_1159_ = lean_array_size(v_depTypes_1151_);
v___x_1160_ = ((size_t)0ULL);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__10(v_sz_1159_, v___x_1160_, v_depTypes_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___x_1222_; size_t v_sz_1223_; lean_object* v___x_1224_; lean_object* v_fst_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1245_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v___x_1222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v_sz_1223_ = lean_array_size(v_a_1205_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16(v_a_1205_, v_sz_1223_, v___x_1160_, v___x_1222_);
v_fst_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1224_, 1);
lean_dec(v_unused_1246_);
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1245_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_fst_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1245_;
goto v_resetjp_1226_;
}
v___jp_1206_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_array_get_size(v_a_1205_);
v___x_1215_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v___x_1216_ = lean_nat_dec_lt(v___x_1213_, v___x_1214_);
if (v___x_1216_ == 0)
{
lean_dec(v_a_1205_);
v___y_1172_ = v___y_1207_;
v___y_1173_ = v___y_1210_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1209_;
v___y_1176_ = v___y_1211_;
v___y_1177_ = v___y_1208_;
v___y_1178_ = v___x_1215_;
goto v___jp_1171_;
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_nat_dec_le(v___x_1214_, v___x_1214_);
if (v___x_1217_ == 0)
{
if (v___x_1216_ == 0)
{
lean_dec(v_a_1205_);
v___y_1172_ = v___y_1207_;
v___y_1173_ = v___y_1210_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1209_;
v___y_1176_ = v___y_1211_;
v___y_1177_ = v___y_1208_;
v___y_1178_ = v___x_1215_;
goto v___jp_1171_;
}
else
{
size_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_usize_of_nat(v___x_1214_);
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_1149_, v_a_1205_, v___x_1160_, v___x_1218_, v___x_1215_);
lean_dec(v_a_1205_);
v___y_1172_ = v___y_1207_;
v___y_1173_ = v___y_1210_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1209_;
v___y_1176_ = v___y_1211_;
v___y_1177_ = v___y_1208_;
v___y_1178_ = v___x_1219_;
goto v___jp_1171_;
}
}
else
{
size_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_usize_of_nat(v___x_1214_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__15(v_plan_1149_, v_a_1205_, v___x_1160_, v___x_1220_, v___x_1215_);
lean_dec(v_a_1205_);
v___y_1172_ = v___y_1207_;
v___y_1173_ = v___y_1210_;
v___y_1174_ = v___y_1212_;
v___y_1175_ = v___y_1209_;
v___y_1176_ = v___y_1211_;
v___y_1177_ = v___y_1208_;
v___y_1178_ = v___x_1221_;
goto v___jp_1171_;
}
}
}
v_resetjp_1226_:
{
if (lean_obj_tag(v_fst_1225_) == 0)
{
lean_del_object(v___x_1227_);
v___y_1207_ = v_a_1152_;
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
goto v___jp_1206_;
}
else
{
lean_object* v_val_1229_; 
v_val_1229_ = lean_ctor_get(v_fst_1225_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v_fst_1225_, 1);
if (lean_obj_tag(v_val_1229_) == 1)
{
lean_object* v_val_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v_val_1230_ = lean_ctor_get(v_val_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v_val_1229_, 1);
v___x_1231_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__4);
v___x_1232_ = l_Lean_MessageData_ofExpr(v_val_1230_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 7);
lean_ctor_set(v___x_1227_, 1, v___x_1232_);
lean_ctor_set(v___x_1227_, 0, v___x_1231_);
v___x_1234_ = v___x_1227_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_1234_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_dec_ref_known(v___x_1235_, 1);
v___y_1207_ = v_a_1152_;
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
goto v___jp_1206_;
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec(v_a_1205_);
lean_dec_ref(v_processing_1150_);
lean_dec_ref(v_plan_1149_);
lean_dec_ref(v_extraDeps_1148_);
lean_dec(v_className_1147_);
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
else
{
lean_dec(v_val_1229_);
lean_del_object(v___x_1227_);
v___y_1207_ = v_a_1152_;
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v_a_1155_;
v___y_1211_ = v_a_1156_;
v___y_1212_ = v_a_1157_;
goto v___jp_1206_;
}
}
}
}
else
{
lean_dec_ref(v_processing_1150_);
lean_dec_ref(v_plan_1149_);
lean_dec_ref(v_extraDeps_1148_);
lean_dec(v_className_1147_);
return v___x_1204_;
}
v___jp_1161_:
{
size_t v_sz_1169_; lean_object* v___x_1170_; 
v_sz_1169_ = lean_array_size(v___y_1162_);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_1150_, v_className_1147_, v_extraDeps_1148_, v___y_1162_, v_sz_1169_, v___x_1160_, v_plan_1149_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec_ref(v___y_1162_);
return v___x_1170_;
}
v___jp_1171_:
{
lean_object* v___x_1179_; size_t v_sz_1180_; lean_object* v___x_1181_; lean_object* v_fst_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1202_; 
v___x_1179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__16___closed__0));
v_sz_1180_ = lean_array_size(v___y_1178_);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__13(v_processing_1150_, v___y_1178_, v_sz_1180_, v___x_1160_, v___x_1179_);
v_fst_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v___x_1181_, 1);
lean_dec(v_unused_1203_);
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1202_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_fst_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1202_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
if (lean_obj_tag(v_fst_1182_) == 0)
{
lean_del_object(v___x_1184_);
v___y_1162_ = v___y_1178_;
v___y_1163_ = v___y_1172_;
v___y_1164_ = v___y_1177_;
v___y_1165_ = v___y_1175_;
v___y_1166_ = v___y_1173_;
v___y_1167_ = v___y_1176_;
v___y_1168_ = v___y_1174_;
goto v___jp_1161_;
}
else
{
lean_object* v_val_1186_; 
v_val_1186_ = lean_ctor_get(v_fst_1182_, 0);
lean_inc(v_val_1186_);
lean_dec_ref_known(v_fst_1182_, 1);
if (lean_obj_tag(v_val_1186_) == 1)
{
lean_object* v_val_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v_val_1187_ = lean_ctor_get(v_val_1186_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v_val_1186_, 1);
v___x_1188_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__1);
v___x_1189_ = l_Lean_MessageData_ofExpr(v_val_1187_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 7);
lean_ctor_set(v___x_1184_, 1, v___x_1189_);
lean_ctor_set(v___x_1184_, 0, v___x_1188_);
v___x_1191_ = v___x_1184_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v___x_1191_, v___y_1172_, v___y_1177_, v___y_1175_, v___y_1173_, v___y_1176_, v___y_1174_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_dec_ref_known(v___x_1192_, 1);
v___y_1162_ = v___y_1178_;
v___y_1163_ = v___y_1172_;
v___y_1164_ = v___y_1177_;
v___y_1165_ = v___y_1175_;
v___y_1166_ = v___y_1173_;
v___y_1167_ = v___y_1176_;
v___y_1168_ = v___y_1174_;
goto v___jp_1161_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v___y_1178_);
lean_dec_ref(v_processing_1150_);
lean_dec_ref(v_plan_1149_);
lean_dec_ref(v_extraDeps_1148_);
lean_dec(v_className_1147_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
else
{
lean_dec(v_val_1186_);
lean_del_object(v___x_1184_);
v___y_1162_ = v___y_1178_;
v___y_1163_ = v___y_1172_;
v___y_1164_ = v___y_1177_;
v___y_1165_ = v___y_1175_;
v___y_1166_ = v___y_1173_;
v___y_1167_ = v___y_1176_;
v___y_1168_ = v___y_1174_;
goto v___jp_1161_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3(void){
_start:
{
lean_object* v_cls_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_cls_1255_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0___closed__1));
v___x_1257_ = l_Lean_Name_append(v___x_1256_, v_cls_1255_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__4));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__6));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__9(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__8));
v___x_1266_ = l_Lean_stringToMessageData(v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__11(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__10));
v___x_1269_ = l_Lean_stringToMessageData(v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__12));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(lean_object* v_className_1273_, lean_object* v_extraDeps_1274_, lean_object* v_plan_1275_, lean_object* v_processing_1276_, lean_object* v_cls_1277_, lean_object* v_inst_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_cls_1286_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___x_1457_; 
v_cls_1286_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1457_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1286_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
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
v___y_1375_ = v_a_1279_;
v___y_1376_ = v_a_1280_;
v___y_1377_ = v_a_1281_;
v___y_1378_ = v_a_1282_;
v___y_1379_ = v_a_1283_;
v___y_1380_ = v_a_1284_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__13);
lean_inc_ref(v_cls_1277_);
v___x_1461_ = l_Lean_MessageData_ofExpr(v_cls_1277_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1286_, v___x_1462_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec_ref_known(v___x_1463_, 1);
v___y_1375_ = v_a_1279_;
v___y_1376_ = v_a_1280_;
v___y_1377_ = v_a_1281_;
v___y_1378_ = v_a_1282_;
v___y_1379_ = v_a_1283_;
v___y_1380_ = v_a_1284_;
goto v___jp_1374_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
v___jp_1287_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; size_t v_sz_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v_sz_1298_ = lean_array_size(v___y_1292_);
v___x_1299_ = ((size_t)0ULL);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__19(v___y_1288_, v_className_1273_, v___y_1292_, v_sz_1298_, v___x_1299_, v___x_1297_, v___y_1289_, v___y_1293_, v___y_1291_, v___y_1290_, v___y_1295_, v___y_1294_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = lean_array_get_size(v___y_1288_);
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1296_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
lean_ctor_set(v___x_1304_, 2, v___x_1303_);
v___x_1305_ = lean_box(0);
v___x_1306_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___y_1292_, v___y_1288_, v___x_1304_, v___x_1305_, v___x_1296_, v___y_1289_, v___y_1293_, v___y_1291_, v___y_1290_, v___y_1295_, v___y_1294_);
lean_dec_ref_known(v___x_1304_, 3);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v___y_1292_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_toCold_1307_; lean_object* v_options_1308_; uint8_t v_hasTrace_1309_; 
lean_dec_ref_known(v___x_1306_, 1);
v_toCold_1307_ = lean_ctor_get(v___y_1295_, 0);
v_options_1308_ = lean_ctor_get(v_toCold_1307_, 2);
v_hasTrace_1309_ = lean_ctor_get_uint8(v_options_1308_, sizeof(void*)*1);
if (v_hasTrace_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_dec_ref(v_cls_1277_);
v___x_1310_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1273_, v_extraDeps_1274_, v_plan_1275_, v_processing_1276_, v_a_1301_, v___y_1289_, v___y_1293_, v___y_1291_, v___y_1290_, v___y_1295_, v___y_1294_);
return v___x_1310_;
}
else
{
lean_object* v_inheritedTraceOptions_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_inheritedTraceOptions_1311_ = lean_ctor_get(v_toCold_1307_, 11);
v___x_1312_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_1313_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1311_, v_options_1308_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref(v_cls_1277_);
v___x_1314_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1273_, v_extraDeps_1274_, v_plan_1275_, v_processing_1276_, v_a_1301_, v___y_1289_, v___y_1293_, v___y_1291_, v___y_1290_, v___y_1295_, v___y_1294_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1315_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__5);
v___x_1316_ = l_Lean_MessageData_ofExpr(v_cls_1277_);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__7);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
lean_inc(v_a_1301_);
v___x_1320_ = lean_array_to_list(v_a_1301_);
v___x_1321_ = lean_box(0);
v___x_1322_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1320_, v___x_1321_);
v___x_1323_ = l_Lean_MessageData_ofList(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1319_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1286_, v___x_1324_, v___y_1291_, v___y_1290_, v___y_1295_, v___y_1294_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1326_; 
lean_dec_ref_known(v___x_1325_, 1);
v___x_1326_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1273_, v_extraDeps_1274_, v_plan_1275_, v_processing_1276_, v_a_1301_, v___y_1289_, v___y_1293_, v___y_1291_, v___y_1290_, v___y_1295_, v___y_1294_);
return v___x_1326_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_a_1301_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
lean_dec(v_a_1301_);
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
v_a_1335_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1306_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1306_);
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
lean_dec_ref(v___y_1292_);
lean_dec_ref(v___y_1288_);
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
return v___x_1300_;
}
}
v___jp_1343_:
{
lean_object* v___x_1353_; 
lean_inc_ref(v_cls_1277_);
v___x_1353_ = l_Lean_Meta_isExprDefEq(v_cls_1277_, v___y_1346_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
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
v___y_1288_ = v___y_1344_;
v___y_1289_ = v___y_1347_;
v___y_1290_ = v___y_1350_;
v___y_1291_ = v___y_1349_;
v___y_1292_ = v___y_1345_;
v___y_1293_ = v___y_1348_;
v___y_1294_ = v___y_1352_;
v___y_1295_ = v___y_1351_;
goto v___jp_1287_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
v___y_1288_ = v___y_1344_;
v___y_1289_ = v___y_1347_;
v___y_1290_ = v___y_1350_;
v___y_1291_ = v___y_1349_;
v___y_1292_ = v___y_1345_;
v___y_1293_ = v___y_1348_;
v___y_1294_ = v___y_1352_;
v___y_1295_ = v___y_1351_;
goto v___jp_1287_;
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
v_val_1381_ = lean_ctor_get(v_inst_1278_, 0);
v_synthOrder_1382_ = lean_ctor_get(v_inst_1278_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_inst_1278_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1384_ = v_inst_1278_;
v_isShared_1385_ = v_isSharedCheck_1456_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_synthOrder_1382_);
lean_inc(v_val_1381_);
lean_dec(v_inst_1278_);
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
v___x_1401_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1286_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
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
v___y_1345_ = v_synthOrder_1382_;
v___y_1346_ = v_snd_1397_;
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
v___x_1417_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1286_, v___x_1416_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref_known(v___x_1417_, 1);
v___y_1344_ = v_fst_1393_;
v___y_1345_ = v_synthOrder_1382_;
v___y_1346_ = v_snd_1397_;
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
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
lean_dec_ref(v_cls_1277_);
lean_dec_ref(v_processing_1276_);
lean_dec_ref(v_plan_1275_);
lean_dec_ref(v_extraDeps_1274_);
lean_dec(v_className_1273_);
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
lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v_toCold_1575_; lean_object* v_currRecDepth_1576_; lean_object* v_ref_1577_; uint8_t v_diag_1578_; uint8_t v_suppressElabErrors_1579_; lean_object* v_maxRecDepth_1580_; lean_object* v_cls_1581_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_toCold_1575_ = lean_ctor_get(v_a_1554_, 0);
v_currRecDepth_1576_ = lean_ctor_get(v_a_1554_, 1);
v_ref_1577_ = lean_ctor_get(v_a_1554_, 2);
v_diag_1578_ = lean_ctor_get_uint8(v_a_1554_, sizeof(void*)*3);
v_suppressElabErrors_1579_ = lean_ctor_get_uint8(v_a_1554_, sizeof(void*)*3 + 1);
v_maxRecDepth_1580_ = lean_ctor_get(v_toCold_1575_, 3);
v_cls_1581_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_nat_dec_eq(v_maxRecDepth_1580_, v___x_1761_);
if (v___x_1762_ == 0)
{
uint8_t v___x_1763_; 
v___x_1763_ = lean_nat_dec_eq(v_currRecDepth_1576_, v_maxRecDepth_1580_);
if (v___x_1763_ == 0)
{
goto v___jp_1731_;
}
else
{
lean_object* v___x_1764_; 
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
lean_inc(v_ref_1577_);
v___x_1764_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__6___redArg(v_ref_1577_);
return v___x_1764_;
}
}
else
{
goto v___jp_1731_;
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
v___jp_1582_:
{
lean_object* v___x_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___closed__0));
v_sz_1592_ = lean_array_size(v___y_1583_);
v___x_1593_ = ((size_t)0ULL);
lean_inc_ref(v_processing_1548_);
lean_inc_ref(v_plan_1547_);
lean_inc_ref(v_extraDeps_1546_);
lean_inc(v_className_1545_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_1545_, v_extraDeps_1546_, v_plan_1547_, v_processing_1548_, v___y_1584_, v___y_1583_, v_sz_1592_, v___x_1593_, v___x_1591_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
lean_dec_ref(v___y_1583_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1639_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1639_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1639_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_fst_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1637_; 
v_fst_1599_ = lean_ctor_get(v_a_1595_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_a_1595_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v_a_1595_, 1);
lean_dec(v_unused_1638_);
v___x_1601_ = v_a_1595_;
v_isShared_1602_ = v_isSharedCheck_1637_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_fst_1599_);
lean_dec(v_a_1595_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1637_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
if (lean_obj_tag(v_fst_1599_) == 0)
{
lean_object* v___x_1603_; 
lean_del_object(v___x_1597_);
lean_inc_ref(v_extraDeps_1546_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc_ref(v_type_1549_);
v___x_1603_ = lean_apply_8(v_extraDeps_1546_, v_type_1549_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, lean_box(0));
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_toCold_1604_; lean_object* v_options_1605_; uint8_t v_hasTrace_1606_; 
v_toCold_1604_ = lean_ctor_get(v___y_1589_, 0);
v_options_1605_ = lean_ctor_get(v_toCold_1604_, 2);
v_hasTrace_1606_ = lean_ctor_get_uint8(v_options_1605_, sizeof(void*)*1);
if (v_hasTrace_1606_ == 0)
{
lean_object* v_a_1607_; 
lean_del_object(v___x_1601_);
v_a_1607_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1603_, 1);
v___y_1558_ = v_a_1607_;
v___y_1559_ = v___y_1585_;
v___y_1560_ = v___y_1586_;
v___y_1561_ = v___y_1587_;
v___y_1562_ = v___y_1588_;
v___y_1563_ = v___y_1589_;
v___y_1564_ = v___y_1590_;
goto v___jp_1557_;
}
else
{
lean_object* v_a_1608_; lean_object* v_inheritedTraceOptions_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v_a_1608_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1603_, 1);
v_inheritedTraceOptions_1609_ = lean_ctor_get(v_toCold_1604_, 11);
v___x_1610_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_1611_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1609_, v_options_1605_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_del_object(v___x_1601_);
v___y_1558_ = v_a_1608_;
v___y_1559_ = v___y_1585_;
v___y_1560_ = v___y_1586_;
v___y_1561_ = v___y_1587_;
v___y_1562_ = v___y_1588_;
v___y_1563_ = v___y_1589_;
v___y_1564_ = v___y_1590_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1612_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__1);
lean_inc_ref(v_type_1549_);
v___x_1613_ = l_Lean_MessageData_ofExpr(v_type_1549_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set_tag(v___x_1601_, 7);
lean_ctor_set(v___x_1601_, 1, v___x_1613_);
lean_ctor_set(v___x_1601_, 0, v___x_1612_);
v___x_1615_ = v___x_1601_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
lean_inc(v_a_1608_);
v___x_1618_ = lean_array_to_list(v_a_1608_);
v___x_1619_ = lean_box(0);
v___x_1620_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1618_, v___x_1619_);
v___x_1621_ = l_Lean_MessageData_ofList(v___x_1620_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1617_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1581_, v___x_1622_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_dec_ref_known(v___x_1623_, 1);
v___y_1558_ = v_a_1608_;
v___y_1559_ = v___y_1585_;
v___y_1560_ = v___y_1586_;
v___y_1561_ = v___y_1587_;
v___y_1562_ = v___y_1588_;
v___y_1563_ = v___y_1589_;
v___y_1564_ = v___y_1590_;
goto v___jp_1557_;
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1608_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1601_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
return v___x_1603_;
}
}
else
{
lean_object* v_val_1633_; lean_object* v___x_1635_; 
lean_del_object(v___x_1601_);
lean_dec_ref(v___y_1589_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_val_1633_ = lean_ctor_get(v_fst_1599_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v_fst_1599_, 1);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_val_1633_);
v___x_1635_ = v___x_1597_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_val_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___y_1589_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1640_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1594_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1594_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
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
v___jp_1648_:
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Array_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__0(v_plan_1547_, v_type_1549_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1656_ = lean_unsigned_to_nat(1u);
v___x_1657_ = lean_mk_empty_array_with_capacity(v___x_1656_);
lean_inc_ref(v_type_1549_);
v___x_1658_ = lean_array_push(v___x_1657_, v_type_1549_);
lean_inc(v_className_1545_);
v___x_1659_ = l_Lean_Meta_mkAppM(v_className_1545_, v___x_1658_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc_n(v_a_1660_, 2);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = l_Lean_Meta_SynthInstance_getInstances(v_a_1660_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1581_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; uint8_t v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = lean_unbox(v_a_1664_);
lean_dec(v_a_1664_);
if (v___x_1665_ == 0)
{
v___y_1583_ = v_a_1662_;
v___y_1584_ = v_a_1660_;
v___y_1585_ = v___y_1649_;
v___y_1586_ = v___y_1650_;
v___y_1587_ = v___y_1651_;
v___y_1588_ = v___y_1652_;
v___y_1589_ = v___y_1653_;
v___y_1590_ = v___y_1654_;
goto v___jp_1582_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1666_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__5);
lean_inc(v_a_1660_);
v___x_1667_ = l_Lean_MessageData_ofExpr(v_a_1660_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_array_get_size(v_a_1662_);
v___x_1672_ = l_Nat_reprFast(v___x_1671_);
v___x_1673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
v___x_1674_ = l_Lean_MessageData_ofFormat(v___x_1673_);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1670_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1581_, v___x_1675_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_dec_ref_known(v___x_1676_, 1);
v___y_1583_ = v_a_1662_;
v___y_1584_ = v_a_1660_;
v___y_1585_ = v___y_1649_;
v___y_1586_ = v___y_1650_;
v___y_1587_ = v___y_1651_;
v___y_1588_ = v___y_1652_;
v___y_1589_ = v___y_1653_;
v___y_1590_ = v___y_1654_;
goto v___jp_1582_;
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_a_1662_);
lean_dec(v_a_1660_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_a_1662_);
lean_dec(v_a_1660_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1685_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1663_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1663_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_a_1660_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1693_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1661_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1661_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1701_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1659_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1659_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v___x_1709_; 
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_plan_1547_);
return v___x_1709_;
}
}
v___jp_1710_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1715_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___y_1714_, v___y_1712_);
v___x_1716_ = l_Lean_MessageData_ofList(v___x_1715_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___y_1713_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__7);
v___x_1719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
lean_inc_ref(v_type_1549_);
v___x_1720_ = l_Lean_MessageData_ofExpr(v_type_1549_);
v___x_1721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1719_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1581_, v___x_1721_, v_a_1552_, v_a_1553_, v___y_1711_, v_a_1555_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_dec_ref_known(v___x_1722_, 1);
v___y_1649_ = v_a_1550_;
v___y_1650_ = v_a_1551_;
v___y_1651_ = v_a_1552_;
v___y_1652_ = v_a_1553_;
v___y_1653_ = v___y_1711_;
v___y_1654_ = v_a_1555_;
goto v___jp_1648_;
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v___y_1711_);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
v___jp_1731_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1732_ = lean_unsigned_to_nat(1u);
v___x_1733_ = lean_nat_add(v_currRecDepth_1576_, v___x_1732_);
lean_inc(v_ref_1577_);
lean_inc_ref(v_toCold_1575_);
v___x_1734_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1734_, 0, v_toCold_1575_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
lean_ctor_set(v___x_1734_, 2, v_ref_1577_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*3, v_diag_1578_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*3 + 1, v_suppressElabErrors_1579_);
v___x_1735_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___lam__0(v_cls_1581_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v___x_1734_, v_a_1555_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; uint8_t v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = lean_unbox(v_a_1736_);
lean_dec(v_a_1736_);
if (v___x_1737_ == 0)
{
v___y_1649_ = v_a_1550_;
v___y_1650_ = v_a_1551_;
v___y_1651_ = v_a_1552_;
v___y_1652_ = v_a_1553_;
v___y_1653_ = v___x_1734_;
v___y_1654_ = v_a_1555_;
goto v___jp_1648_;
}
else
{
lean_object* v_buckets_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_buckets_1738_ = lean_ctor_get(v_processing_1548_, 1);
v___x_1739_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__9);
lean_inc_ref(v_plan_1547_);
v___x_1740_ = lean_array_to_list(v_plan_1547_);
v___x_1741_ = lean_box(0);
v___x_1742_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_1740_, v___x_1741_);
v___x_1743_ = l_Lean_MessageData_ofList(v___x_1742_);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1739_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__11);
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = lean_array_get_size(v_buckets_1738_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = lean_nat_dec_lt(v___x_1748_, v___x_1747_);
if (v___x_1749_ == 0)
{
v___y_1711_ = v___x_1734_;
v___y_1712_ = v___x_1741_;
v___y_1713_ = v___x_1746_;
v___y_1714_ = v___x_1741_;
goto v___jp_1710_;
}
else
{
size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = lean_usize_of_nat(v___x_1747_);
v___x_1751_ = ((size_t)0ULL);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__5(v_buckets_1738_, v___x_1750_, v___x_1751_, v___x_1741_);
v___y_1711_ = v___x_1734_;
v___y_1712_ = v___x_1741_;
v___y_1713_ = v___x_1746_;
v___y_1714_ = v___x_1752_;
goto v___jp_1710_;
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref_known(v___x_1734_, 3);
lean_dec_ref(v_type_1549_);
lean_dec_ref(v_processing_1548_);
lean_dec_ref(v_plan_1547_);
lean_dec_ref(v_extraDeps_1546_);
lean_dec(v_className_1545_);
v_a_1753_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1735_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1735_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(lean_object* v_processing_1765_, lean_object* v_className_1766_, lean_object* v_extraDeps_1767_, lean_object* v_as_1768_, size_t v_sz_1769_, size_t v_i_1770_, lean_object* v_b_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_usize_dec_lt(v_i_1770_, v_sz_1769_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; 
lean_dec_ref(v_extraDeps_1767_);
lean_dec(v_className_1766_);
lean_dec_ref(v_processing_1765_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_b_1771_);
return v___x_1780_;
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_a_1781_ = lean_array_uget_borrowed(v_as_1768_, v_i_1770_);
v___x_1782_ = lean_box(0);
lean_inc_n(v_a_1781_, 2);
lean_inc_ref(v_processing_1765_);
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v_processing_1765_, v_a_1781_, v___x_1782_);
lean_inc_ref(v_extraDeps_1767_);
lean_inc(v_className_1766_);
v___x_1784_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_1766_, v_extraDeps_1767_, v_b_1771_, v___x_1783_, v_a_1781_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; size_t v___x_1786_; size_t v___x_1787_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = ((size_t)1ULL);
v___x_1787_ = lean_usize_add(v_i_1770_, v___x_1786_);
v_i_1770_ = v___x_1787_;
v_b_1771_ = v_a_1785_;
goto _start;
}
else
{
lean_dec_ref(v_extraDeps_1767_);
lean_dec(v_className_1766_);
lean_dec_ref(v_processing_1765_);
return v___x_1784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11___boxed(lean_object* v_processing_1789_, lean_object* v_className_1790_, lean_object* v_extraDeps_1791_, lean_object* v_as_1792_, lean_object* v_sz_1793_, lean_object* v_i_1794_, lean_object* v_b_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
size_t v_sz_boxed_1803_; size_t v_i_boxed_1804_; lean_object* v_res_1805_; 
v_sz_boxed_1803_ = lean_unbox_usize(v_sz_1793_);
lean_dec(v_sz_1793_);
v_i_boxed_1804_ = lean_unbox_usize(v_i_1794_);
lean_dec(v_i_1794_);
v_res_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__11(v_processing_1789_, v_className_1790_, v_extraDeps_1791_, v_as_1792_, v_sz_boxed_1803_, v_i_boxed_1804_, v_b_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec_ref(v_as_1792_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1___boxed(lean_object* v_className_1806_, lean_object* v_extraDeps_1807_, lean_object* v_plan_1808_, lean_object* v_processing_1809_, lean_object* v_a_1810_, lean_object* v_as_1811_, lean_object* v_sz_1812_, lean_object* v_i_1813_, lean_object* v_b_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
size_t v_sz_boxed_1822_; size_t v_i_boxed_1823_; lean_object* v_res_1824_; 
v_sz_boxed_1822_ = lean_unbox_usize(v_sz_1812_);
lean_dec(v_sz_1812_);
v_i_boxed_1823_ = lean_unbox_usize(v_i_1813_);
lean_dec(v_i_1813_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__1(v_className_1806_, v_extraDeps_1807_, v_plan_1808_, v_processing_1809_, v_a_1810_, v_as_1811_, v_sz_boxed_1822_, v_i_boxed_1823_, v_b_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_as_1811_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___boxed(lean_object* v_className_1825_, lean_object* v_extraDeps_1826_, lean_object* v_plan_1827_, lean_object* v_processing_1828_, lean_object* v_depTypes_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes(v_className_1825_, v_extraDeps_1826_, v_plan_1827_, v_processing_1828_, v_depTypes_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___boxed(lean_object* v_className_1838_, lean_object* v_extraDeps_1839_, lean_object* v_plan_1840_, lean_object* v_processing_1841_, lean_object* v_cls_1842_, lean_object* v_inst_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst(v_className_1838_, v_extraDeps_1839_, v_plan_1840_, v_processing_1841_, v_cls_1842_, v_inst_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___boxed(lean_object* v_className_1852_, lean_object* v_extraDeps_1853_, lean_object* v_plan_1854_, lean_object* v_processing_1855_, lean_object* v_type_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_1852_, v_extraDeps_1853_, v_plan_1854_, v_processing_1855_, v_type_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(lean_object* v_e_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___redArg(v_e_1865_, v___y_1869_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9___boxed(lean_object* v_e_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__9(v_e_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(lean_object* v_cls_1883_, lean_object* v_msg_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v_cls_1883_, v_msg_1884_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___boxed(lean_object* v_cls_1893_, lean_object* v_msg_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3(v_cls_1893_, v_msg_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8(lean_object* v_00_u03b2_1903_, lean_object* v_m_1904_, lean_object* v_a_1905_, lean_object* v_b_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v_m_1904_, v_a_1905_, v_b_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(lean_object* v_00_u03b2_1908_, lean_object* v_m_1909_, lean_object* v_a_1910_){
_start:
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___redArg(v_m_1909_, v_a_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12___boxed(lean_object* v_00_u03b2_1912_, lean_object* v_m_1913_, lean_object* v_a_1914_){
_start:
{
uint8_t v_res_1915_; lean_object* v_r_1916_; 
v_res_1915_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__12(v_00_u03b2_1912_, v_m_1913_, v_a_1914_);
lean_dec_ref(v_a_1914_);
lean_dec_ref(v_m_1913_);
v_r_1916_ = lean_box(v_res_1915_);
return v_r_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(lean_object* v_00_u03b1_1917_, lean_object* v_msg_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___redArg(v_msg_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_msg_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14(v_00_u03b1_1927_, v_msg_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(lean_object* v_00_u03b1_1937_, lean_object* v_msg_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___redArg(v_msg_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18___boxed(lean_object* v_00_u03b1_1945_, lean_object* v_msg_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__18(v_00_u03b1_1945_, v_msg_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(lean_object* v___x_1953_, lean_object* v_fst_1954_, lean_object* v_range_1955_, lean_object* v_b_1956_, lean_object* v_i_1957_, lean_object* v_hs_1958_, lean_object* v_hl_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___redArg(v___x_1953_, v_fst_1954_, v_range_1955_, v_b_1956_, v_i_1957_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21___boxed(lean_object* v___x_1968_, lean_object* v_fst_1969_, lean_object* v_range_1970_, lean_object* v_b_1971_, lean_object* v_i_1972_, lean_object* v_hs_1973_, lean_object* v_hl_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst_spec__21(v___x_1968_, v_fst_1969_, v_range_1970_, v_b_1971_, v_i_1972_, v_hs_1973_, v_hl_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec_ref(v_range_1970_);
lean_dec_ref(v_fst_1969_);
lean_dec_ref(v___x_1968_);
return v_res_1982_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(lean_object* v_00_u03b2_1983_, lean_object* v_a_1984_, lean_object* v_x_1985_){
_start:
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___redArg(v_a_1984_, v_x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1987_, lean_object* v_a_1988_, lean_object* v_x_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__10(v_00_u03b2_1987_, v_a_1988_, v_x_1989_);
lean_dec(v_x_1989_);
lean_dec_ref(v_a_1988_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11(lean_object* v_00_u03b2_1992_, lean_object* v_data_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11___redArg(v_data_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(lean_object* v_msgData_1995_, lean_object* v_macroStack_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___redArg(v_msgData_1995_, v_macroStack_1996_, v___y_2001_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18___boxed(lean_object* v_msgData_2005_, lean_object* v_macroStack_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18(v_msgData_2005_, v_macroStack_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14(lean_object* v_00_u03b2_2015_, lean_object* v_i_2016_, lean_object* v_source_2017_, lean_object* v_target_2018_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14___redArg(v_i_2016_, v_source_2017_, v_target_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26(lean_object* v_00_u03b2_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8_spec__11_spec__14_spec__26___redArg(v_x_2021_, v_x_2022_);
return v___x_2023_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_unsigned_to_nat(32u);
v___x_2025_ = lean_mk_empty_array_with_capacity(v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2027_ = ((size_t)5ULL);
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = lean_unsigned_to_nat(32u);
v___x_2030_ = lean_mk_empty_array_with_capacity(v___x_2029_);
v___x_2031_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__0);
v___x_2032_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___x_2030_);
lean_ctor_set(v___x_2032_, 2, v___x_2028_);
lean_ctor_set(v___x_2032_, 3, v___x_2028_);
lean_ctor_set_usize(v___x_2032_, 4, v___x_2027_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(lean_object* v___y_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v_traceState_2036_; lean_object* v_traces_2037_; lean_object* v___x_2038_; lean_object* v_traceState_2039_; lean_object* v_env_2040_; lean_object* v_nextMacroScope_2041_; lean_object* v_ngen_2042_; lean_object* v_auxDeclNGen_2043_; lean_object* v_cache_2044_; lean_object* v_messages_2045_; lean_object* v_infoState_2046_; lean_object* v_snapshotTasks_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2066_; 
v___x_2035_ = lean_st_ref_get(v___y_2033_);
v_traceState_2036_ = lean_ctor_get(v___x_2035_, 4);
lean_inc_ref(v_traceState_2036_);
lean_dec(v___x_2035_);
v_traces_2037_ = lean_ctor_get(v_traceState_2036_, 0);
lean_inc_ref(v_traces_2037_);
lean_dec_ref(v_traceState_2036_);
v___x_2038_ = lean_st_ref_take(v___y_2033_);
v_traceState_2039_ = lean_ctor_get(v___x_2038_, 4);
v_env_2040_ = lean_ctor_get(v___x_2038_, 0);
v_nextMacroScope_2041_ = lean_ctor_get(v___x_2038_, 1);
v_ngen_2042_ = lean_ctor_get(v___x_2038_, 2);
v_auxDeclNGen_2043_ = lean_ctor_get(v___x_2038_, 3);
v_cache_2044_ = lean_ctor_get(v___x_2038_, 5);
v_messages_2045_ = lean_ctor_get(v___x_2038_, 6);
v_infoState_2046_ = lean_ctor_get(v___x_2038_, 7);
v_snapshotTasks_2047_ = lean_ctor_get(v___x_2038_, 8);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2049_ = v___x_2038_;
v_isShared_2050_ = v_isSharedCheck_2066_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_snapshotTasks_2047_);
lean_inc(v_infoState_2046_);
lean_inc(v_messages_2045_);
lean_inc(v_cache_2044_);
lean_inc(v_traceState_2039_);
lean_inc(v_auxDeclNGen_2043_);
lean_inc(v_ngen_2042_);
lean_inc(v_nextMacroScope_2041_);
lean_inc(v_env_2040_);
lean_dec(v___x_2038_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2066_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
uint64_t v_tid_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2064_; 
v_tid_2051_ = lean_ctor_get_uint64(v_traceState_2039_, sizeof(void*)*1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_traceState_2039_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_traceState_2039_, 0);
lean_dec(v_unused_2065_);
v___x_2053_ = v_traceState_2039_;
v_isShared_2054_ = v_isSharedCheck_2064_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v_traceState_2039_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2064_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___closed__1);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2055_);
v___x_2057_ = v___x_2053_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2055_);
lean_ctor_set_uint64(v_reuseFailAlloc_2063_, sizeof(void*)*1, v_tid_2051_);
v___x_2057_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2059_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 4, v___x_2057_);
v___x_2059_ = v___x_2049_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_env_2040_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_nextMacroScope_2041_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_ngen_2042_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v_auxDeclNGen_2043_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2062_, 5, v_cache_2044_);
lean_ctor_set(v_reuseFailAlloc_2062_, 6, v_messages_2045_);
lean_ctor_set(v_reuseFailAlloc_2062_, 7, v_infoState_2046_);
lean_ctor_set(v_reuseFailAlloc_2062_, 8, v_snapshotTasks_2047_);
v___x_2059_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_st_ref_put(v___y_2033_, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_traces_2037_);
return v___x_2061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg___boxed(lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_2067_);
lean_dec(v___y_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v___y_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___boxed(lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0(v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
return v_res_2085_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__0));
v___x_2088_ = l_Lean_stringToMessageData(v___x_2087_);
return v___x_2088_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__2));
v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(lean_object* v_className_2092_, lean_object* v_type_2093_, lean_object* v_r_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___y_2113_; 
v___x_2102_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__1);
v___x_2103_ = 0;
v___x_2104_ = l_Lean_MessageData_ofConstName(v_className_2092_, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2102_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___closed__3);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = l_Lean_MessageData_ofExpr(v_type_2093_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
if (lean_obj_tag(v_r_2094_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2117_; 
v_a_2116_ = lean_ctor_get(v_r_2094_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v_r_2094_, 1);
v___x_2117_ = l_Lean_Exception_toMessageData(v_a_2116_);
v___y_2113_ = v___x_2117_;
goto v___jp_2112_;
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_a_2118_ = lean_ctor_get(v_r_2094_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v_r_2094_, 1);
v___x_2119_ = lean_array_to_list(v_a_2118_);
v___x_2120_ = lean_box(0);
v___x_2121_ = l_List_mapTR_loop___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__2(v___x_2119_, v___x_2120_);
v___x_2122_ = l_Lean_MessageData_ofList(v___x_2121_);
v___y_2113_ = v___x_2122_;
goto v___jp_2112_;
}
v___jp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2111_);
lean_ctor_set(v___x_2114_, 1, v___y_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed(lean_object* v_className_2123_, lean_object* v_type_2124_, lean_object* v_r_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0(v_className_2123_, v_type_2124_, v_r_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(lean_object* v_opts_2134_, lean_object* v_opt_2135_){
_start:
{
lean_object* v_name_2136_; lean_object* v_defValue_2137_; lean_object* v_map_2138_; lean_object* v___x_2139_; 
v_name_2136_ = lean_ctor_get(v_opt_2135_, 0);
v_defValue_2137_ = lean_ctor_get(v_opt_2135_, 1);
v_map_2138_ = lean_ctor_get(v_opts_2134_, 0);
v___x_2139_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2138_, v_name_2136_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_inc(v_defValue_2137_);
return v_defValue_2137_;
}
else
{
lean_object* v_val_2140_; 
v_val_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_val_2140_);
lean_dec_ref_known(v___x_2139_, 1);
if (lean_obj_tag(v_val_2140_) == 3)
{
lean_object* v_v_2141_; 
v_v_2141_ = lean_ctor_get(v_val_2140_, 0);
lean_inc(v_v_2141_);
lean_dec_ref_known(v_val_2140_, 1);
return v_v_2141_;
}
else
{
lean_dec(v_val_2140_);
lean_inc(v_defValue_2137_);
return v_defValue_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4___boxed(lean_object* v_opts_2142_, lean_object* v_opt_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2142_, v_opt_2143_);
lean_dec_ref(v_opt_2143_);
lean_dec_ref(v_opts_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(lean_object* v_e_2145_){
_start:
{
if (lean_obj_tag(v_e_2145_) == 0)
{
uint8_t v___x_2146_; 
v___x_2146_ = 2;
return v___x_2146_;
}
else
{
uint8_t v___x_2147_; 
v___x_2147_ = 0;
return v___x_2147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3___boxed(lean_object* v_e_2148_){
_start:
{
uint8_t v_res_2149_; lean_object* v_r_2150_; 
v_res_2149_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_e_2148_);
lean_dec_ref(v_e_2148_);
v_r_2150_ = lean_box(v_res_2149_);
return v_r_2150_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_a_2153_ = lean_ctor_get(v_x_2151_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_x_2151_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v_x_2151_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v_x_2151_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 1);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
v_a_2161_ = lean_ctor_get(v_x_2151_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_x_2151_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v_x_2151_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v_x_2151_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 0);
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg___boxed(lean_object* v_x_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_x_2169_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(size_t v_sz_2172_, size_t v_i_2173_, lean_object* v_bs_2174_){
_start:
{
uint8_t v___x_2175_; 
v___x_2175_ = lean_usize_dec_lt(v_i_2173_, v_sz_2172_);
if (v___x_2175_ == 0)
{
return v_bs_2174_;
}
else
{
lean_object* v_v_2176_; lean_object* v_msg_2177_; lean_object* v___x_2178_; lean_object* v_bs_x27_2179_; size_t v___x_2180_; size_t v___x_2181_; lean_object* v___x_2182_; 
v_v_2176_ = lean_array_uget_borrowed(v_bs_2174_, v_i_2173_);
v_msg_2177_ = lean_ctor_get(v_v_2176_, 1);
lean_inc_ref(v_msg_2177_);
v___x_2178_ = lean_unsigned_to_nat(0u);
v_bs_x27_2179_ = lean_array_uset(v_bs_2174_, v_i_2173_, v___x_2178_);
v___x_2180_ = ((size_t)1ULL);
v___x_2181_ = lean_usize_add(v_i_2173_, v___x_2180_);
v___x_2182_ = lean_array_uset(v_bs_x27_2179_, v_i_2173_, v_msg_2177_);
v_i_2173_ = v___x_2181_;
v_bs_2174_ = v___x_2182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2184_, lean_object* v_i_2185_, lean_object* v_bs_2186_){
_start:
{
size_t v_sz_boxed_2187_; size_t v_i_boxed_2188_; lean_object* v_res_2189_; 
v_sz_boxed_2187_ = lean_unbox_usize(v_sz_2184_);
lean_dec(v_sz_2184_);
v_i_boxed_2188_ = lean_unbox_usize(v_i_2185_);
lean_dec(v_i_2185_);
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(v_sz_boxed_2187_, v_i_boxed_2188_, v_bs_2186_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(lean_object* v_oldTraces_2190_, lean_object* v_data_2191_, lean_object* v_ref_2192_, lean_object* v_msg_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_toCold_2199_; lean_object* v_currRecDepth_2200_; lean_object* v_ref_2201_; uint8_t v_diag_2202_; uint8_t v_suppressElabErrors_2203_; lean_object* v___x_2204_; lean_object* v_traceState_2205_; lean_object* v_traces_2206_; lean_object* v_ref_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; size_t v_sz_2210_; size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v_msg_2213_; lean_object* v___x_2214_; lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2252_; 
v_toCold_2199_ = lean_ctor_get(v___y_2196_, 0);
v_currRecDepth_2200_ = lean_ctor_get(v___y_2196_, 1);
v_ref_2201_ = lean_ctor_get(v___y_2196_, 2);
v_diag_2202_ = lean_ctor_get_uint8(v___y_2196_, sizeof(void*)*3);
v_suppressElabErrors_2203_ = lean_ctor_get_uint8(v___y_2196_, sizeof(void*)*3 + 1);
v___x_2204_ = lean_st_ref_get(v___y_2197_);
v_traceState_2205_ = lean_ctor_get(v___x_2204_, 4);
lean_inc_ref(v_traceState_2205_);
lean_dec(v___x_2204_);
v_traces_2206_ = lean_ctor_get(v_traceState_2205_, 0);
lean_inc_ref(v_traces_2206_);
lean_dec_ref(v_traceState_2205_);
v_ref_2207_ = l_Lean_replaceRef(v_ref_2192_, v_ref_2201_);
lean_inc(v_currRecDepth_2200_);
lean_inc_ref(v_toCold_2199_);
v___x_2208_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2208_, 0, v_toCold_2199_);
lean_ctor_set(v___x_2208_, 1, v_currRecDepth_2200_);
lean_ctor_set(v___x_2208_, 2, v_ref_2207_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*3, v_diag_2202_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*3 + 1, v_suppressElabErrors_2203_);
v___x_2209_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2206_);
lean_dec_ref(v_traces_2206_);
v_sz_2210_ = lean_array_size(v___x_2209_);
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1_spec__2(v_sz_2210_, v___x_2211_, v___x_2209_);
v_msg_2213_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2213_, 0, v_data_2191_);
lean_ctor_set(v_msg_2213_, 1, v_msg_2193_);
lean_ctor_set(v_msg_2213_, 2, v___x_2212_);
v___x_2214_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3_spec__4(v_msg_2213_, v___y_2194_, v___y_2195_, v___x_2208_, v___y_2197_);
lean_dec_ref_known(v___x_2208_, 3);
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2252_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2252_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v_traceState_2220_; lean_object* v_env_2221_; lean_object* v_nextMacroScope_2222_; lean_object* v_ngen_2223_; lean_object* v_auxDeclNGen_2224_; lean_object* v_cache_2225_; lean_object* v_messages_2226_; lean_object* v_infoState_2227_; lean_object* v_snapshotTasks_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2251_; 
v___x_2219_ = lean_st_ref_take(v___y_2197_);
v_traceState_2220_ = lean_ctor_get(v___x_2219_, 4);
v_env_2221_ = lean_ctor_get(v___x_2219_, 0);
v_nextMacroScope_2222_ = lean_ctor_get(v___x_2219_, 1);
v_ngen_2223_ = lean_ctor_get(v___x_2219_, 2);
v_auxDeclNGen_2224_ = lean_ctor_get(v___x_2219_, 3);
v_cache_2225_ = lean_ctor_get(v___x_2219_, 5);
v_messages_2226_ = lean_ctor_get(v___x_2219_, 6);
v_infoState_2227_ = lean_ctor_get(v___x_2219_, 7);
v_snapshotTasks_2228_ = lean_ctor_get(v___x_2219_, 8);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2230_ = v___x_2219_;
v_isShared_2231_ = v_isSharedCheck_2251_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_snapshotTasks_2228_);
lean_inc(v_infoState_2227_);
lean_inc(v_messages_2226_);
lean_inc(v_cache_2225_);
lean_inc(v_traceState_2220_);
lean_inc(v_auxDeclNGen_2224_);
lean_inc(v_ngen_2223_);
lean_inc(v_nextMacroScope_2222_);
lean_inc(v_env_2221_);
lean_dec(v___x_2219_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2251_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
uint64_t v_tid_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2249_; 
v_tid_2232_ = lean_ctor_get_uint64(v_traceState_2220_, sizeof(void*)*1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_traceState_2220_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v_traceState_2220_, 0);
lean_dec(v_unused_2250_);
v___x_2234_ = v_traceState_2220_;
v_isShared_2235_ = v_isSharedCheck_2249_;
goto v_resetjp_2233_;
}
else
{
lean_dec(v_traceState_2220_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2249_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v_ref_2192_);
lean_ctor_set(v___x_2236_, 1, v_a_2215_);
v___x_2237_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2190_, v___x_2236_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2237_);
v___x_2239_ = v___x_2234_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2237_);
lean_ctor_set_uint64(v_reuseFailAlloc_2248_, sizeof(void*)*1, v_tid_2232_);
v___x_2239_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2241_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 4, v___x_2239_);
v___x_2241_ = v___x_2230_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_env_2221_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_nextMacroScope_2222_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_ngen_2223_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v_auxDeclNGen_2224_);
lean_ctor_set(v_reuseFailAlloc_2247_, 4, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2247_, 5, v_cache_2225_);
lean_ctor_set(v_reuseFailAlloc_2247_, 6, v_messages_2226_);
lean_ctor_set(v_reuseFailAlloc_2247_, 7, v_infoState_2227_);
lean_ctor_set(v_reuseFailAlloc_2247_, 8, v_snapshotTasks_2228_);
v___x_2241_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2242_ = lean_st_ref_put(v___y_2197_, v___x_2241_);
v___x_2243_ = lean_box(0);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v___x_2243_);
v___x_2245_ = v___x_2217_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg___boxed(lean_object* v_oldTraces_2253_, lean_object* v_data_2254_, lean_object* v_ref_2255_, lean_object* v_msg_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2253_, v_data_2254_, v_ref_2255_, v_msg_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v_res_2262_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__0));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2266_; double v___x_2267_; 
v___x_2266_ = lean_unsigned_to_nat(1000u);
v___x_2267_ = lean_float_of_nat(v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(lean_object* v_cls_2268_, uint8_t v_collapsed_2269_, lean_object* v_tag_2270_, lean_object* v_opts_2271_, uint8_t v_clsEnabled_2272_, lean_object* v_oldTraces_2273_, lean_object* v_msg_2274_, lean_object* v_resStartStop_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_fst_2283_; lean_object* v_snd_2284_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v_data_2288_; lean_object* v_fst_2299_; lean_object* v_snd_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___y_2304_; lean_object* v_a_2305_; uint8_t v___y_2320_; double v___y_2351_; 
v_fst_2283_ = lean_ctor_get(v_resStartStop_2275_, 0);
lean_inc(v_fst_2283_);
v_snd_2284_ = lean_ctor_get(v_resStartStop_2275_, 1);
lean_inc(v_snd_2284_);
lean_dec_ref(v_resStartStop_2275_);
v_fst_2299_ = lean_ctor_get(v_snd_2284_, 0);
lean_inc(v_fst_2299_);
v_snd_2300_ = lean_ctor_get(v_snd_2284_, 1);
lean_inc(v_snd_2300_);
lean_dec(v_snd_2284_);
v___x_2301_ = l_Lean_trace_profiler;
v___x_2302_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_2271_, v___x_2301_);
if (v___x_2302_ == 0)
{
v___y_2320_ = v___x_2302_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2357_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_opts_2271_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2359_; double v___x_2360_; double v___x_2361_; double v___x_2362_; 
v___x_2358_ = l_Lean_trace_profiler_threshold;
v___x_2359_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2271_, v___x_2358_);
v___x_2360_ = lean_float_of_nat(v___x_2359_);
v___x_2361_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__2);
v___x_2362_ = lean_float_div(v___x_2360_, v___x_2361_);
v___y_2351_ = v___x_2362_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; double v___x_2365_; 
v___x_2363_ = l_Lean_trace_profiler_threshold;
v___x_2364_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__4(v_opts_2271_, v___x_2363_);
v___x_2365_ = lean_float_of_nat(v___x_2364_);
v___y_2351_ = v___x_2365_;
goto v___jp_2350_;
}
}
v___jp_2285_:
{
lean_object* v___x_2289_; 
lean_inc(v___y_2286_);
v___x_2289_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2273_, v_data_2288_, v___y_2286_, v___y_2287_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; 
lean_dec_ref_known(v___x_2289_, 1);
v___x_2290_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_fst_2283_);
return v___x_2290_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_fst_2283_);
v_a_2291_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2289_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
v___jp_2303_:
{
uint8_t v_result_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; double v___x_2309_; lean_object* v_data_2310_; 
v_result_2306_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__3(v_fst_2283_);
v___x_2307_ = lean_box(v_result_2306_);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
v___x_2309_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_2270_);
lean_inc_ref(v___x_2308_);
lean_inc(v_cls_2268_);
v_data_2310_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2310_, 0, v_cls_2268_);
lean_ctor_set(v_data_2310_, 1, v___x_2308_);
lean_ctor_set(v_data_2310_, 2, v_tag_2270_);
lean_ctor_set_float(v_data_2310_, sizeof(void*)*3, v___x_2309_);
lean_ctor_set_float(v_data_2310_, sizeof(void*)*3 + 8, v___x_2309_);
lean_ctor_set_uint8(v_data_2310_, sizeof(void*)*3 + 16, v_collapsed_2269_);
if (v___x_2302_ == 0)
{
lean_dec_ref_known(v___x_2308_, 1);
lean_dec(v_snd_2300_);
lean_dec(v_fst_2299_);
lean_dec_ref(v_tag_2270_);
lean_dec(v_cls_2268_);
v___y_2286_ = v___y_2304_;
v___y_2287_ = v_a_2305_;
v_data_2288_ = v_data_2310_;
goto v___jp_2285_;
}
else
{
lean_object* v_data_2311_; double v___x_2312_; double v___x_2313_; 
lean_dec_ref_known(v_data_2310_, 3);
v_data_2311_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2311_, 0, v_cls_2268_);
lean_ctor_set(v_data_2311_, 1, v___x_2308_);
lean_ctor_set(v_data_2311_, 2, v_tag_2270_);
v___x_2312_ = lean_unbox_float(v_fst_2299_);
lean_dec(v_fst_2299_);
lean_ctor_set_float(v_data_2311_, sizeof(void*)*3, v___x_2312_);
v___x_2313_ = lean_unbox_float(v_snd_2300_);
lean_dec(v_snd_2300_);
lean_ctor_set_float(v_data_2311_, sizeof(void*)*3 + 8, v___x_2313_);
lean_ctor_set_uint8(v_data_2311_, sizeof(void*)*3 + 16, v_collapsed_2269_);
v___y_2286_ = v___y_2304_;
v___y_2287_ = v_a_2305_;
v_data_2288_ = v_data_2311_;
goto v___jp_2285_;
}
}
v___jp_2314_:
{
lean_object* v_ref_2315_; lean_object* v___x_2316_; 
v_ref_2315_ = lean_ctor_get(v___y_2280_, 2);
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v_fst_2283_);
v___x_2316_ = lean_apply_8(v_msg_2274_, v_fst_2283_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, lean_box(0));
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___y_2304_ = v_ref_2315_;
v_a_2305_ = v_a_2317_;
goto v___jp_2303_;
}
else
{
lean_object* v___x_2318_; 
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___closed__1);
v___y_2304_ = v_ref_2315_;
v_a_2305_ = v___x_2318_;
goto v___jp_2303_;
}
}
v___jp_2319_:
{
if (v_clsEnabled_2272_ == 0)
{
if (v___y_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v_traceState_2322_; lean_object* v_env_2323_; lean_object* v_nextMacroScope_2324_; lean_object* v_ngen_2325_; lean_object* v_auxDeclNGen_2326_; lean_object* v_cache_2327_; lean_object* v_messages_2328_; lean_object* v_infoState_2329_; lean_object* v_snapshotTasks_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_snd_2300_);
lean_dec(v_fst_2299_);
lean_dec_ref(v_msg_2274_);
lean_dec_ref(v_tag_2270_);
lean_dec(v_cls_2268_);
v___x_2321_ = lean_st_ref_take(v___y_2281_);
v_traceState_2322_ = lean_ctor_get(v___x_2321_, 4);
v_env_2323_ = lean_ctor_get(v___x_2321_, 0);
v_nextMacroScope_2324_ = lean_ctor_get(v___x_2321_, 1);
v_ngen_2325_ = lean_ctor_get(v___x_2321_, 2);
v_auxDeclNGen_2326_ = lean_ctor_get(v___x_2321_, 3);
v_cache_2327_ = lean_ctor_get(v___x_2321_, 5);
v_messages_2328_ = lean_ctor_get(v___x_2321_, 6);
v_infoState_2329_ = lean_ctor_get(v___x_2321_, 7);
v_snapshotTasks_2330_ = lean_ctor_get(v___x_2321_, 8);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2332_ = v___x_2321_;
v_isShared_2333_ = v_isSharedCheck_2349_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_snapshotTasks_2330_);
lean_inc(v_infoState_2329_);
lean_inc(v_messages_2328_);
lean_inc(v_cache_2327_);
lean_inc(v_traceState_2322_);
lean_inc(v_auxDeclNGen_2326_);
lean_inc(v_ngen_2325_);
lean_inc(v_nextMacroScope_2324_);
lean_inc(v_env_2323_);
lean_dec(v___x_2321_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2349_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
uint64_t v_tid_2334_; lean_object* v_traces_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2348_; 
v_tid_2334_ = lean_ctor_get_uint64(v_traceState_2322_, sizeof(void*)*1);
v_traces_2335_ = lean_ctor_get(v_traceState_2322_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_traceState_2322_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2337_ = v_traceState_2322_;
v_isShared_2338_ = v_isSharedCheck_2348_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_traces_2335_);
lean_dec(v_traceState_2322_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2348_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2339_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2273_, v_traces_2335_);
lean_dec_ref(v_traces_2335_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2339_);
v___x_2341_ = v___x_2337_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2339_);
lean_ctor_set_uint64(v_reuseFailAlloc_2347_, sizeof(void*)*1, v_tid_2334_);
v___x_2341_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 4, v___x_2341_);
v___x_2343_ = v___x_2332_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_env_2323_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_nextMacroScope_2324_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_ngen_2325_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_auxDeclNGen_2326_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2346_, 5, v_cache_2327_);
lean_ctor_set(v_reuseFailAlloc_2346_, 6, v_messages_2328_);
lean_ctor_set(v_reuseFailAlloc_2346_, 7, v_infoState_2329_);
lean_ctor_set(v_reuseFailAlloc_2346_, 8, v_snapshotTasks_2330_);
v___x_2343_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_st_ref_put(v___y_2281_, v___x_2343_);
v___x_2345_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_fst_2283_);
return v___x_2345_;
}
}
}
}
}
else
{
goto v___jp_2314_;
}
}
else
{
goto v___jp_2314_;
}
}
v___jp_2350_:
{
double v___x_2352_; double v___x_2353_; double v___x_2354_; uint8_t v___x_2355_; 
v___x_2352_ = lean_unbox_float(v_snd_2300_);
v___x_2353_ = lean_unbox_float(v_fst_2299_);
v___x_2354_ = lean_float_sub(v___x_2352_, v___x_2353_);
v___x_2355_ = lean_float_decLt(v___y_2351_, v___x_2354_);
v___y_2320_ = v___x_2355_;
goto v___jp_2319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1___boxed(lean_object* v_cls_2366_, lean_object* v_collapsed_2367_, lean_object* v_tag_2368_, lean_object* v_opts_2369_, lean_object* v_clsEnabled_2370_, lean_object* v_oldTraces_2371_, lean_object* v_msg_2372_, lean_object* v_resStartStop_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
uint8_t v_collapsed_boxed_2381_; uint8_t v_clsEnabled_boxed_2382_; lean_object* v_res_2383_; 
v_collapsed_boxed_2381_ = lean_unbox(v_collapsed_2367_);
v_clsEnabled_boxed_2382_ = lean_unbox(v_clsEnabled_2370_);
v_res_2383_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v_cls_2366_, v_collapsed_boxed_2381_, v_tag_2368_, v_opts_2369_, v_clsEnabled_boxed_2382_, v_oldTraces_2371_, v_msg_2372_, v_resStartStop_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v_opts_2369_);
return v_res_2383_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = lean_unsigned_to_nat(16u);
v___x_2386_ = lean_mk_array(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__0);
v___x_2388_ = lean_unsigned_to_nat(0u);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v___x_2387_);
return v___x_2389_;
}
}
static double _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2(void){
_start:
{
lean_object* v___x_2390_; double v___x_2391_; 
v___x_2390_ = lean_unsigned_to_nat(1000000000u);
v___x_2391_ = lean_float_of_nat(v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(lean_object* v_className_2392_, lean_object* v_type_2393_, lean_object* v_extraDeps_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_toCold_2402_; lean_object* v_options_2403_; lean_object* v_inheritedTraceOptions_2404_; uint8_t v_hasTrace_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_toCold_2402_ = lean_ctor_get(v_a_2399_, 0);
v_options_2403_ = lean_ctor_get(v_toCold_2402_, 2);
v_inheritedTraceOptions_2404_ = lean_ctor_get(v_toCold_2402_, 11);
v_hasTrace_2405_ = lean_ctor_get_uint8(v_options_2403_, sizeof(void*)*1);
v___x_2406_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes___closed__2));
v___x_2407_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__1);
v___x_2408_ = lean_box(0);
lean_inc_ref(v_type_2393_);
v___x_2409_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__8___redArg(v___x_2407_, v_type_2393_, v___x_2408_);
if (v_hasTrace_2405_ == 0)
{
lean_object* v___x_2410_; 
v___x_2410_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2392_, v_extraDeps_2394_, v___x_2406_, v___x_2409_, v_type_2393_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2410_;
}
else
{
lean_object* v___f_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v_a_2419_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v_a_2434_; 
lean_inc_ref(v_type_2393_);
lean_inc(v_className_2392_);
v___f_2411_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2411_, 0, v_className_2392_);
lean_closure_set(v___f_2411_, 1, v_type_2393_);
v___x_2412_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_2414_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2404_, v_options_2403_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = l_Lean_trace_profiler;
v___x_2485_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_2403_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
lean_dec_ref(v___f_2411_);
v___x_2486_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2392_, v_extraDeps_2394_, v___x_2406_, v___x_2409_, v_type_2393_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2486_;
}
else
{
goto v___jp_2443_;
}
}
else
{
goto v___jp_2443_;
}
v___jp_2416_:
{
lean_object* v___x_2420_; double v___x_2421_; double v___x_2422_; double v___x_2423_; double v___x_2424_; double v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2420_ = lean_io_mono_nanos_now();
v___x_2421_ = lean_float_of_nat(v___y_2417_);
v___x_2422_ = lean_float_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___closed__2);
v___x_2423_ = lean_float_div(v___x_2421_, v___x_2422_);
v___x_2424_ = lean_float_of_nat(v___x_2420_);
v___x_2425_ = lean_float_div(v___x_2424_, v___x_2422_);
v___x_2426_ = lean_box_float(v___x_2423_);
v___x_2427_ = lean_box_float(v___x_2425_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_a_2419_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_2412_, v_hasTrace_2405_, v___x_2413_, v_options_2403_, v___x_2415_, v___y_2418_, v___f_2411_, v___x_2429_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2430_;
}
v___jp_2431_:
{
lean_object* v___x_2435_; double v___x_2436_; double v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2435_ = lean_io_get_num_heartbeats();
v___x_2436_ = lean_float_of_nat(v___y_2433_);
v___x_2437_ = lean_float_of_nat(v___x_2435_);
v___x_2438_ = lean_box_float(v___x_2436_);
v___x_2439_ = lean_box_float(v___x_2437_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_a_2434_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1(v___x_2412_, v_hasTrace_2405_, v___x_2413_, v_options_2403_, v___x_2415_, v___y_2432_, v___f_2411_, v___x_2441_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
return v___x_2442_;
}
v___jp_2443_:
{
lean_object* v___x_2444_; lean_object* v_a_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2444_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__0___redArg(v_a_2400_);
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_a_2445_);
lean_dec_ref(v___x_2444_);
v___x_2446_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2447_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_useDepTypes_spec__14_spec__18_spec__21(v_options_2403_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_io_mono_nanos_now();
v___x_2449_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2392_, v_extraDeps_2394_, v___x_2406_, v___x_2409_, v_type_2393_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set_tag(v___x_2452_, 1);
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
v___y_2417_ = v___x_2448_;
v___y_2418_ = v_a_2445_;
v_a_2419_ = v___x_2455_;
goto v___jp_2416_;
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v_a_2458_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2449_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2449_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 0);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
v___y_2417_ = v___x_2448_;
v___y_2418_ = v_a_2445_;
v_a_2419_ = v___x_2463_;
goto v___jp_2416_;
}
}
}
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_io_get_num_heartbeats();
v___x_2467_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go(v_className_2392_, v_extraDeps_2394_, v___x_2406_, v___x_2409_, v_type_2393_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set_tag(v___x_2470_, 1);
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
v___y_2432_ = v_a_2445_;
v___y_2433_ = v___x_2466_;
v_a_2434_ = v___x_2473_;
goto v___jp_2431_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2467_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2467_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 0);
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
v___y_2432_ = v_a_2445_;
v___y_2433_ = v___x_2466_;
v_a_2434_ = v___x_2481_;
goto v___jp_2431_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed(lean_object* v_className_2487_, lean_object* v_type_2488_, lean_object* v_extraDeps_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation(v_className_2487_, v_type_2488_, v_extraDeps_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(lean_object* v_00_u03b1_2498_, lean_object* v_x_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___redArg(v_x_2499_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2508_, lean_object* v_x_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__2(v_00_u03b1_2508_, v_x_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(lean_object* v_oldTraces_2518_, lean_object* v_data_2519_, lean_object* v_ref_2520_, lean_object* v_msg_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___redArg(v_oldTraces_2518_, v_data_2519_, v_ref_2520_, v_msg_2521_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1___boxed(lean_object* v_oldTraces_2530_, lean_object* v_data_2531_, lean_object* v_ref_2532_, lean_object* v_msg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_spec__1_spec__1(v_oldTraces_2530_, v_data_2531_, v_ref_2532_, v_msg_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2541_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2542_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__0);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__1);
v___x_2548_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
lean_ctor_set(v___x_2548_, 2, v___x_2547_);
lean_ctor_set(v___x_2548_, 3, v___x_2547_);
lean_ctor_set(v___x_2548_, 4, v___x_2547_);
lean_ctor_set(v___x_2548_, 5, v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(lean_object* v_env_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; lean_object* v_nextMacroScope_2554_; lean_object* v_ngen_2555_; lean_object* v_auxDeclNGen_2556_; lean_object* v_traceState_2557_; lean_object* v_messages_2558_; lean_object* v_infoState_2559_; lean_object* v_snapshotTasks_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2586_; 
v___x_2553_ = lean_st_ref_take(v___y_2551_);
v_nextMacroScope_2554_ = lean_ctor_get(v___x_2553_, 1);
v_ngen_2555_ = lean_ctor_get(v___x_2553_, 2);
v_auxDeclNGen_2556_ = lean_ctor_get(v___x_2553_, 3);
v_traceState_2557_ = lean_ctor_get(v___x_2553_, 4);
v_messages_2558_ = lean_ctor_get(v___x_2553_, 6);
v_infoState_2559_ = lean_ctor_get(v___x_2553_, 7);
v_snapshotTasks_2560_ = lean_ctor_get(v___x_2553_, 8);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; lean_object* v_unused_2588_; 
v_unused_2587_ = lean_ctor_get(v___x_2553_, 5);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v___x_2553_, 0);
lean_dec(v_unused_2588_);
v___x_2562_ = v___x_2553_;
v_isShared_2563_ = v_isSharedCheck_2586_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snapshotTasks_2560_);
lean_inc(v_infoState_2559_);
lean_inc(v_messages_2558_);
lean_inc(v_traceState_2557_);
lean_inc(v_auxDeclNGen_2556_);
lean_inc(v_ngen_2555_);
lean_inc(v_nextMacroScope_2554_);
lean_dec(v___x_2553_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2586_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__2);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 5, v___x_2564_);
lean_ctor_set(v___x_2562_, 0, v_env_2549_);
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_env_2549_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_nextMacroScope_2554_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_ngen_2555_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_auxDeclNGen_2556_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_traceState_2557_);
lean_ctor_set(v_reuseFailAlloc_2585_, 5, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2585_, 6, v_messages_2558_);
lean_ctor_set(v_reuseFailAlloc_2585_, 7, v_infoState_2559_);
lean_ctor_set(v_reuseFailAlloc_2585_, 8, v_snapshotTasks_2560_);
v___x_2566_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v_mctx_2569_; lean_object* v_zetaDeltaFVarIds_2570_; lean_object* v_postponed_2571_; lean_object* v_diag_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2583_; 
v___x_2567_ = lean_st_ref_put(v___y_2551_, v___x_2566_);
v___x_2568_ = lean_st_ref_take(v___y_2550_);
v_mctx_2569_ = lean_ctor_get(v___x_2568_, 0);
v_zetaDeltaFVarIds_2570_ = lean_ctor_get(v___x_2568_, 2);
v_postponed_2571_ = lean_ctor_get(v___x_2568_, 3);
v_diag_2572_ = lean_ctor_get(v___x_2568_, 4);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; 
v_unused_2584_ = lean_ctor_get(v___x_2568_, 1);
lean_dec(v_unused_2584_);
v___x_2574_ = v___x_2568_;
v_isShared_2575_ = v_isSharedCheck_2583_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_diag_2572_);
lean_inc(v_postponed_2571_);
lean_inc(v_zetaDeltaFVarIds_2570_);
lean_inc(v_mctx_2569_);
lean_dec(v___x_2568_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2583_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___closed__3);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v___x_2576_);
v___x_2578_ = v___x_2574_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_mctx_2569_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_zetaDeltaFVarIds_2570_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_postponed_2571_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_diag_2572_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = lean_st_ref_put(v___y_2550_, v___x_2578_);
v___x_2580_ = lean_box(0);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
return v___x_2581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg___boxed(lean_object* v_env_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v_env_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec(v___y_2590_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(lean_object* v_env_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v_env_2594_, v___y_2598_, v___y_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___boxed(lean_object* v_env_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0(v_env_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2611_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__0));
v___x_2614_ = l_Lean_stringToMessageData(v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(lean_object* v_mkCmd_2615_, lean_object* v_a_2616_, lean_object* v___x_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_inc(v___y_2621_);
lean_inc_ref(v___y_2620_);
lean_inc(v___y_2619_);
lean_inc_ref(v___y_2618_);
lean_inc_ref(v_a_2616_);
v___x_2625_ = lean_apply_5(v_mkCmd_2615_, v_a_2616_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
v___x_2626_ = l_Lean_Core_withFreshMacroScope___redArg(v___x_2625_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_a_2616_);
return v___x_2626_;
}
else
{
lean_object* v_a_2627_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; uint8_t v___y_2653_; uint8_t v___x_2677_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
v___x_2677_ = l_Lean_Exception_isInterrupt(v_a_2627_);
if (v___x_2677_ == 0)
{
uint8_t v___x_2678_; 
lean_inc(v_a_2627_);
v___x_2678_ = l_Lean_Exception_isRuntime(v_a_2627_);
v___y_2653_ = v___x_2678_;
goto v___jp_2652_;
}
else
{
v___y_2653_ = v___x_2677_;
goto v___jp_2652_;
}
v___jp_2628_:
{
lean_object* v___x_2635_; 
lean_dec_ref(v___y_2629_);
v___x_2635_ = l_Lean_setEnv___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__0___redArg(v___x_2617_, v___y_2632_, v___y_2634_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v___x_2635_, 0);
lean_dec(v_unused_2643_);
v___x_2637_ = v___x_2635_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_dec(v___x_2635_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 1);
lean_ctor_set(v___x_2637_, 0, v_a_2627_);
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2627_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_a_2627_);
v_a_2644_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2635_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2635_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
v___jp_2652_:
{
if (v___y_2653_ == 0)
{
lean_object* v_toCold_2654_; lean_object* v_options_2655_; uint8_t v_hasTrace_2656_; 
lean_dec_ref_known(v___x_2626_, 1);
v_toCold_2654_ = lean_ctor_get(v___y_2622_, 0);
v_options_2655_ = lean_ctor_get(v_toCold_2654_, 2);
v_hasTrace_2656_ = lean_ctor_get_uint8(v_options_2655_, sizeof(void*)*1);
if (v_hasTrace_2656_ == 0)
{
lean_dec_ref(v_a_2616_);
v___y_2629_ = v___y_2618_;
v___y_2630_ = v___y_2619_;
v___y_2631_ = v___y_2620_;
v___y_2632_ = v___y_2621_;
v___y_2633_ = v___y_2622_;
v___y_2634_ = v___y_2623_;
goto v___jp_2628_;
}
else
{
lean_object* v_inheritedTraceOptions_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v_inheritedTraceOptions_2657_ = lean_ctor_get(v_toCold_2654_, 11);
v___x_2658_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2659_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2657_, v_options_2655_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_dec_ref(v_a_2616_);
v___y_2629_ = v___y_2618_;
v___y_2630_ = v___y_2619_;
v___y_2631_ = v___y_2620_;
v___y_2632_ = v___y_2621_;
v___y_2633_ = v___y_2622_;
v___y_2634_ = v___y_2623_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2661_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___closed__1);
v___x_2662_ = l_Lean_MessageData_ofExpr(v_a_2616_);
v___x_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go___closed__3);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
lean_inc(v_a_2627_);
v___x_2666_ = l_Lean_Exception_toMessageData(v_a_2627_);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg(v___x_2658_, v___x_2667_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec_ref_known(v___x_2668_, 1);
v___y_2629_ = v___y_2618_;
v___y_2630_ = v___y_2619_;
v___y_2631_ = v___y_2620_;
v___y_2632_ = v___y_2621_;
v___y_2633_ = v___y_2622_;
v___y_2634_ = v___y_2623_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v_a_2627_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___x_2617_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2627_);
lean_dec_ref(v___y_2618_);
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_a_2616_);
return v___x_2626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed(lean_object* v_mkCmd_2679_, lean_object* v_a_2680_, lean_object* v___x_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0(v_mkCmd_2679_, v_a_2680_, v___x_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
return v_res_2689_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2690_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__0);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
return v___x_2692_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
lean_ctor_set(v___x_2695_, 2, v___x_2694_);
lean_ctor_set(v___x_2695_, 3, v___x_2694_);
lean_ctor_set(v___x_2695_, 4, v___x_2693_);
lean_ctor_set(v___x_2695_, 5, v___x_2693_);
lean_ctor_set(v___x_2695_, 6, v___x_2693_);
lean_ctor_set(v___x_2695_, 7, v___x_2693_);
lean_ctor_set(v___x_2695_, 8, v___x_2693_);
lean_ctor_set(v___x_2695_, 9, v___x_2693_);
lean_ctor_set(v___x_2695_, 10, v___x_2693_);
return v___x_2695_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_unsigned_to_nat(32u);
v___x_2697_ = lean_mk_empty_array_with_capacity(v___x_2696_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2699_ = ((size_t)5ULL);
v___x_2700_ = lean_unsigned_to_nat(0u);
v___x_2701_ = lean_unsigned_to_nat(32u);
v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2701_);
v___x_2703_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__3);
v___x_2704_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___x_2702_);
lean_ctor_set(v___x_2704_, 2, v___x_2700_);
lean_ctor_set(v___x_2704_, 3, v___x_2700_);
lean_ctor_set_usize(v___x_2704_, 4, v___x_2699_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2705_ = lean_box(1);
v___x_2706_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__4);
v___x_2707_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__1);
v___x_2708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
lean_ctor_set(v___x_2708_, 1, v___x_2706_);
lean_ctor_set(v___x_2708_, 2, v___x_2705_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(lean_object* v_msgData_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; lean_object* v_env_2713_; lean_object* v___x_2714_; lean_object* v_scopes_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v_opts_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2712_ = lean_st_ref_get(v___y_2710_);
v_env_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc_ref(v_env_2713_);
lean_dec(v___x_2712_);
v___x_2714_ = lean_st_ref_get(v___y_2710_);
v_scopes_2715_ = lean_ctor_get(v___x_2714_, 2);
lean_inc(v_scopes_2715_);
lean_dec(v___x_2714_);
v___x_2716_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2717_ = l_List_head_x21___redArg(v___x_2716_, v_scopes_2715_);
lean_dec(v_scopes_2715_);
v_opts_2718_ = lean_ctor_get(v___x_2717_, 1);
lean_inc_ref(v_opts_2718_);
lean_dec(v___x_2717_);
v___x_2719_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__2);
v___x_2720_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___closed__5);
v___x_2721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2721_, 0, v_env_2713_);
lean_ctor_set(v___x_2721_, 1, v___x_2719_);
lean_ctor_set(v___x_2721_, 2, v___x_2720_);
lean_ctor_set(v___x_2721_, 3, v_opts_2718_);
v___x_2722_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_msgData_2709_);
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msgData_2724_, v___y_2725_);
lean_dec(v___y_2725_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(lean_object* v_cls_2728_, lean_object* v_msg_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Elab_Command_getRef___redArg(v___y_2730_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2735_; lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2784_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msg_2729_, v___y_2731_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2784_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2784_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v_traceState_2741_; lean_object* v_env_2742_; lean_object* v_messages_2743_; lean_object* v_scopes_2744_; lean_object* v_usedQuotCtxts_2745_; lean_object* v_nextMacroScope_2746_; lean_object* v_maxRecDepth_2747_; lean_object* v_ngen_2748_; lean_object* v_auxDeclNGen_2749_; lean_object* v_infoState_2750_; lean_object* v_snapshotTasks_2751_; lean_object* v_prevLinterStates_2752_; lean_object* v_codeQualityEntryTasks_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2783_; 
v___x_2740_ = lean_st_ref_take(v___y_2731_);
v_traceState_2741_ = lean_ctor_get(v___x_2740_, 9);
v_env_2742_ = lean_ctor_get(v___x_2740_, 0);
v_messages_2743_ = lean_ctor_get(v___x_2740_, 1);
v_scopes_2744_ = lean_ctor_get(v___x_2740_, 2);
v_usedQuotCtxts_2745_ = lean_ctor_get(v___x_2740_, 3);
v_nextMacroScope_2746_ = lean_ctor_get(v___x_2740_, 4);
v_maxRecDepth_2747_ = lean_ctor_get(v___x_2740_, 5);
v_ngen_2748_ = lean_ctor_get(v___x_2740_, 6);
v_auxDeclNGen_2749_ = lean_ctor_get(v___x_2740_, 7);
v_infoState_2750_ = lean_ctor_get(v___x_2740_, 8);
v_snapshotTasks_2751_ = lean_ctor_get(v___x_2740_, 10);
v_prevLinterStates_2752_ = lean_ctor_get(v___x_2740_, 11);
v_codeQualityEntryTasks_2753_ = lean_ctor_get(v___x_2740_, 12);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2755_ = v___x_2740_;
v_isShared_2756_ = v_isSharedCheck_2783_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_codeQualityEntryTasks_2753_);
lean_inc(v_prevLinterStates_2752_);
lean_inc(v_snapshotTasks_2751_);
lean_inc(v_traceState_2741_);
lean_inc(v_infoState_2750_);
lean_inc(v_auxDeclNGen_2749_);
lean_inc(v_ngen_2748_);
lean_inc(v_maxRecDepth_2747_);
lean_inc(v_nextMacroScope_2746_);
lean_inc(v_usedQuotCtxts_2745_);
lean_inc(v_scopes_2744_);
lean_inc(v_messages_2743_);
lean_inc(v_env_2742_);
lean_dec(v___x_2740_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2783_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
uint64_t v_tid_2757_; lean_object* v_traces_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2782_; 
v_tid_2757_ = lean_ctor_get_uint64(v_traceState_2741_, sizeof(void*)*1);
v_traces_2758_ = lean_ctor_get(v_traceState_2741_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_traceState_2741_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2760_ = v_traceState_2741_;
v_isShared_2761_ = v_isSharedCheck_2782_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_traces_2758_);
lean_dec(v_traceState_2741_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2782_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; double v___x_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__0);
v___x_2764_ = 0;
v___x_2765_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_makeStringMatcher_build___closed__0));
v___x_2766_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2766_, 0, v_cls_2728_);
lean_ctor_set(v___x_2766_, 1, v___x_2762_);
lean_ctor_set(v___x_2766_, 2, v___x_2765_);
lean_ctor_set_float(v___x_2766_, sizeof(void*)*3, v___x_2763_);
lean_ctor_set_float(v___x_2766_, sizeof(void*)*3 + 8, v___x_2763_);
lean_ctor_set_uint8(v___x_2766_, sizeof(void*)*3 + 16, v___x_2764_);
v___x_2767_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_go_spec__3___redArg___closed__1));
v___x_2768_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v_a_2736_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v_a_2734_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = l_Lean_PersistentArray_push___redArg(v_traces_2758_, v___x_2769_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2770_);
v___x_2772_ = v___x_2760_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2770_);
lean_ctor_set_uint64(v_reuseFailAlloc_2781_, sizeof(void*)*1, v_tid_2757_);
v___x_2772_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2774_; 
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 9, v___x_2772_);
v___x_2774_ = v___x_2755_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_env_2742_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_messages_2743_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_scopes_2744_);
lean_ctor_set(v_reuseFailAlloc_2780_, 3, v_usedQuotCtxts_2745_);
lean_ctor_set(v_reuseFailAlloc_2780_, 4, v_nextMacroScope_2746_);
lean_ctor_set(v_reuseFailAlloc_2780_, 5, v_maxRecDepth_2747_);
lean_ctor_set(v_reuseFailAlloc_2780_, 6, v_ngen_2748_);
lean_ctor_set(v_reuseFailAlloc_2780_, 7, v_auxDeclNGen_2749_);
lean_ctor_set(v_reuseFailAlloc_2780_, 8, v_infoState_2750_);
lean_ctor_set(v_reuseFailAlloc_2780_, 9, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2780_, 10, v_snapshotTasks_2751_);
lean_ctor_set(v_reuseFailAlloc_2780_, 11, v_prevLinterStates_2752_);
lean_ctor_set(v_reuseFailAlloc_2780_, 12, v_codeQualityEntryTasks_2753_);
v___x_2774_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2775_ = lean_st_ref_put(v___y_2731_, v___x_2774_);
v___x_2776_ = lean_box(0);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2776_);
v___x_2778_ = v___x_2738_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref(v_msg_2729_);
lean_dec(v_cls_2728_);
v_a_2785_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2733_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2733_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1___boxed(lean_object* v_cls_2793_, lean_object* v_msg_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(v_cls_2793_, v_msg_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2798_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__0));
v___x_2801_ = l_Lean_stringToMessageData(v___x_2800_);
return v___x_2801_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__2));
v___x_2804_ = l_Lean_stringToMessageData(v___x_2803_);
return v___x_2804_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__4));
v___x_2807_ = l_Lean_stringToMessageData(v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(lean_object* v_mkCmd_2808_, lean_object* v___x_2809_, lean_object* v_className_2810_, lean_object* v_as_2811_, size_t v_sz_2812_, size_t v_i_2813_, lean_object* v_b_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_a_2819_; uint8_t v___x_2823_; 
v___x_2823_ = lean_usize_dec_lt(v_i_2813_, v_sz_2812_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; 
lean_dec(v_className_2810_);
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_mkCmd_2808_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v_b_2814_);
return v___x_2824_;
}
else
{
lean_object* v_a_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; 
v_a_2825_ = lean_array_uget_borrowed(v_as_2811_, v_i_2813_);
lean_inc_ref(v___x_2809_);
lean_inc(v_a_2825_);
lean_inc_ref(v_mkCmd_2808_);
v___f_2826_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2826_, 0, v_mkCmd_2808_);
lean_closure_set(v___f_2826_, 1, v_a_2825_);
lean_closure_set(v___f_2826_, 2, v___x_2809_);
v___x_2827_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2826_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = l_Lean_Elab_Command_elabCommand(v_a_2828_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v_scopes_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_opts_2836_; uint8_t v_hasTrace_2837_; lean_object* v___x_2838_; 
lean_dec_ref_known(v___x_2829_, 1);
v___x_2830_ = l_Lean_inheritedTraceOptions;
v___x_2831_ = lean_st_ref_get(v___x_2830_);
v___x_2832_ = lean_st_ref_get(v___y_2816_);
v_scopes_2833_ = lean_ctor_get(v___x_2832_, 2);
lean_inc(v_scopes_2833_);
lean_dec(v___x_2832_);
v___x_2834_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2835_ = l_List_head_x21___redArg(v___x_2834_, v_scopes_2833_);
lean_dec(v_scopes_2833_);
v_opts_2836_ = lean_ctor_get(v___x_2835_, 1);
lean_inc_ref(v_opts_2836_);
lean_dec(v___x_2835_);
v_hasTrace_2837_ = lean_ctor_get_uint8(v_opts_2836_, sizeof(void*)*1);
v___x_2838_ = lean_box(0);
if (v_hasTrace_2837_ == 0)
{
lean_dec_ref(v_opts_2836_);
lean_dec(v___x_2831_);
v_a_2819_ = v___x_2838_;
goto v___jp_2818_;
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2839_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2840_ = lean_obj_once(&l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3, &l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3_once, _init_l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__3);
v___x_2841_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2831_, v_opts_2836_, v___x_2840_);
lean_dec_ref(v_opts_2836_);
lean_dec(v___x_2831_);
if (v___x_2841_ == 0)
{
v_a_2819_ = v___x_2838_;
goto v___jp_2818_;
}
else
{
lean_object* v___x_2842_; uint8_t v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__1);
v___x_2843_ = 0;
lean_inc(v_className_2810_);
v___x_2844_ = l_Lean_MessageData_ofConstName(v_className_2810_, v___x_2843_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2842_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__3);
v___x_2847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2845_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
lean_inc(v_a_2825_);
v___x_2848_ = l_Lean_MessageData_ofExpr(v_a_2825_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___closed__5);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1(v___x_2839_, v___x_2851_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_dec_ref_known(v___x_2852_, 1);
v_a_2819_ = v___x_2838_;
goto v___jp_2818_;
}
else
{
lean_dec(v_className_2810_);
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_mkCmd_2808_);
return v___x_2852_;
}
}
}
}
else
{
lean_dec(v_className_2810_);
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_mkCmd_2808_);
return v___x_2829_;
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_className_2810_);
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_mkCmd_2808_);
v_a_2853_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2827_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2827_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
v___jp_2818_:
{
size_t v___x_2820_; size_t v___x_2821_; 
v___x_2820_ = ((size_t)1ULL);
v___x_2821_ = lean_usize_add(v_i_2813_, v___x_2820_);
v_i_2813_ = v___x_2821_;
v_b_2814_ = v_a_2819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2___boxed(lean_object* v_mkCmd_2861_, lean_object* v___x_2862_, lean_object* v_className_2863_, lean_object* v_as_2864_, lean_object* v_sz_2865_, lean_object* v_i_2866_, lean_object* v_b_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
size_t v_sz_boxed_2871_; size_t v_i_boxed_2872_; lean_object* v_res_2873_; 
v_sz_boxed_2871_ = lean_unbox_usize(v_sz_2865_);
lean_dec(v_sz_2865_);
v_i_boxed_2872_ = lean_unbox_usize(v_i_2866_);
lean_dec(v_i_2866_);
v_res_2873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(v_mkCmd_2861_, v___x_2862_, v_className_2863_, v_as_2864_, v_sz_boxed_2871_, v_i_boxed_2872_, v_b_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v_as_2864_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_withClassInstDeps(lean_object* v_className_2874_, lean_object* v_type_2875_, lean_object* v_extraDeps_2876_, lean_object* v_mkCmd_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_inc(v_className_2874_);
v___x_2881_ = lean_alloc_closure((void*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation___boxed), 10, 3);
lean_closure_set(v___x_2881_, 0, v_className_2874_);
lean_closure_set(v___x_2881_, 1, v_type_2875_);
lean_closure_set(v___x_2881_, 2, v_extraDeps_2876_);
v___x_2882_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2881_, v_a_2878_, v_a_2879_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; lean_object* v_env_2885_; lean_object* v___x_2886_; size_t v_sz_2887_; size_t v___x_2888_; lean_object* v___x_2889_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v___x_2884_ = lean_st_ref_get(v_a_2879_);
v_env_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_ref(v_env_2885_);
lean_dec(v___x_2884_);
v___x_2886_ = lean_box(0);
v_sz_2887_ = lean_array_size(v_a_2883_);
v___x_2888_ = ((size_t)0ULL);
v___x_2889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__2(v_mkCmd_2877_, v_env_2885_, v_className_2874_, v_a_2883_, v_sz_2887_, v___x_2888_, v___x_2886_, v_a_2878_, v_a_2879_);
lean_dec(v_a_2883_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v___x_2889_, 0);
lean_dec(v_unused_2897_);
v___x_2891_ = v___x_2889_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_dec(v___x_2889_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2886_);
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2886_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
else
{
return v___x_2889_;
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v_mkCmd_2877_);
lean_dec(v_className_2874_);
v_a_2898_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2882_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2882_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_withClassInstDeps___boxed(lean_object* v_className_2906_, lean_object* v_type_2907_, lean_object* v_extraDeps_2908_, lean_object* v_mkCmd_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Elab_ConfigEval_withClassInstDeps(v_className_2906_, v_type_2907_, v_extraDeps_2908_, v_mkCmd_2909_, v_a_2910_, v_a_2911_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(lean_object* v_msgData_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___redArg(v_msgData_2914_, v___y_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1___boxed(lean_object* v_msgData_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_ConfigEval_withClassInstDeps_spec__1_spec__1(v_msgData_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2989_; uint8_t v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2989_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_planDerivation_tryInst___closed__2));
v___x_2990_ = 0;
v___x_2991_ = ((lean_object*)(l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn___closed__25_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_));
v___x_2992_ = l_Lean_registerTraceClass(v___x_2989_, v___x_2990_, v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2____boxed(lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Lean_Elab_ConfigEval_Util_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Util_1975219684____hygCtx___hyg_2_();
return v_res_2994_;
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
