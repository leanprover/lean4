// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize
// Imports: public import Lean.Elab.Tactic.FalseOrByContra public import Lean.Meta.Tactic.BVDecide.Normalize.Basic public import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow public import Lean.Meta.Tactic.BVDecide.Normalize.Simproc public import Lean.Meta.Tactic.BVDecide.Normalize.Rewrite public import Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten public import Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint public import Lean.Meta.Tactic.BVDecide.Normalize.AC public import Lean.Meta.Tactic.BVDecide.Normalize.Structures public import Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec public import Lean.Meta.Tactic.BVDecide.Normalize.Enums public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis public import Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MVarId_falseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " on\n"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Running fixpoint pipeline on:\n"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Running preprocessing pipeline on:\n"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Preprocessing goal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getPropHyps___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass;
v___x_6_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_passPipeline_9_; 
v___x_7_ = lean_box(0);
v___x_8_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
v_passPipeline_9_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_passPipeline_9_, 0, v___x_8_);
lean_ctor_set(v_passPipeline_9_, 1, v___x_7_);
return v_passPipeline_9_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_box(0);
v___x_11_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass;
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4(void){
_start:
{
lean_object* v___x_13_; lean_object* v_passPipeline_14_; lean_object* v___x_15_; 
v___x_13_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__3);
v_passPipeline_14_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
v___x_15_ = l_List_appendTR___redArg(v_passPipeline_14_, v___x_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(lean_object* v_a_16_){
_start:
{
uint8_t v_acNf_18_; uint8_t v_andFlattening_19_; uint8_t v_embeddedConstraintSubst_20_; lean_object* v_passPipeline_22_; lean_object* v_passPipeline_28_; lean_object* v_passPipeline_31_; 
v_acNf_18_ = lean_ctor_get_uint8(v_a_16_, sizeof(void*)*2 + 2);
v_andFlattening_19_ = lean_ctor_get_uint8(v_a_16_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_20_ = lean_ctor_get_uint8(v_a_16_, sizeof(void*)*2 + 4);
v_passPipeline_31_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
if (v_acNf_18_ == 0)
{
v_passPipeline_28_ = v_passPipeline_31_;
goto v___jp_27_;
}
else
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4);
v_passPipeline_28_ = v___x_32_;
goto v___jp_27_;
}
v___jp_21_:
{
if (v_embeddedConstraintSubst_20_ == 0)
{
lean_object* v___x_23_; 
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v_passPipeline_22_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0);
v___x_25_ = l_List_appendTR___redArg(v_passPipeline_22_, v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
v___jp_27_:
{
if (v_embeddedConstraintSubst_20_ == 0)
{
lean_inc(v_passPipeline_28_);
v_passPipeline_22_ = v_passPipeline_28_;
goto v___jp_21_;
}
else
{
if (v_andFlattening_19_ == 0)
{
lean_inc(v_passPipeline_28_);
v_passPipeline_22_ = v_passPipeline_28_;
goto v___jp_21_;
}
else
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1);
lean_inc(v_passPipeline_28_);
v___x_30_ = l_List_appendTR___redArg(v_passPipeline_28_, v___x_29_);
v_passPipeline_22_ = v___x_30_;
goto v___jp_21_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___boxed(lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_33_);
lean_dec_ref(v_a_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_36_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
return v_res_51_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_unsigned_to_nat(32u);
v___x_53_ = lean_mk_empty_array_with_capacity(v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_55_ = ((size_t)5ULL);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_unsigned_to_nat(32u);
v___x_58_ = lean_mk_empty_array_with_capacity(v___x_57_);
v___x_59_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__0);
v___x_60_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_56_);
lean_ctor_set(v___x_60_, 3, v___x_56_);
lean_ctor_set_usize(v___x_60_, 4, v___x_55_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; lean_object* v_traceState_64_; lean_object* v_traces_65_; lean_object* v___x_66_; lean_object* v_traceState_67_; lean_object* v_env_68_; lean_object* v_nextMacroScope_69_; lean_object* v_ngen_70_; lean_object* v_auxDeclNGen_71_; lean_object* v_cache_72_; lean_object* v_messages_73_; lean_object* v_infoState_74_; lean_object* v_snapshotTasks_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_94_; 
v___x_63_ = lean_st_ref_get(v___y_61_);
v_traceState_64_ = lean_ctor_get(v___x_63_, 4);
lean_inc_ref(v_traceState_64_);
lean_dec(v___x_63_);
v_traces_65_ = lean_ctor_get(v_traceState_64_, 0);
lean_inc_ref(v_traces_65_);
lean_dec_ref(v_traceState_64_);
v___x_66_ = lean_st_ref_take(v___y_61_);
v_traceState_67_ = lean_ctor_get(v___x_66_, 4);
v_env_68_ = lean_ctor_get(v___x_66_, 0);
v_nextMacroScope_69_ = lean_ctor_get(v___x_66_, 1);
v_ngen_70_ = lean_ctor_get(v___x_66_, 2);
v_auxDeclNGen_71_ = lean_ctor_get(v___x_66_, 3);
v_cache_72_ = lean_ctor_get(v___x_66_, 5);
v_messages_73_ = lean_ctor_get(v___x_66_, 6);
v_infoState_74_ = lean_ctor_get(v___x_66_, 7);
v_snapshotTasks_75_ = lean_ctor_get(v___x_66_, 8);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_94_ == 0)
{
v___x_77_ = v___x_66_;
v_isShared_78_ = v_isSharedCheck_94_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_snapshotTasks_75_);
lean_inc(v_infoState_74_);
lean_inc(v_messages_73_);
lean_inc(v_cache_72_);
lean_inc(v_traceState_67_);
lean_inc(v_auxDeclNGen_71_);
lean_inc(v_ngen_70_);
lean_inc(v_nextMacroScope_69_);
lean_inc(v_env_68_);
lean_dec(v___x_66_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_94_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint64_t v_tid_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_92_; 
v_tid_79_ = lean_ctor_get_uint64(v_traceState_67_, sizeof(void*)*1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_traceState_67_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_traceState_67_, 0);
lean_dec(v_unused_93_);
v___x_81_ = v_traceState_67_;
v_isShared_82_ = v_isSharedCheck_92_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_traceState_67_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_92_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_83_);
v___x_85_ = v___x_81_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_83_);
lean_ctor_set_uint64(v_reuseFailAlloc_91_, sizeof(void*)*1, v_tid_79_);
v___x_85_ = v_reuseFailAlloc_91_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_87_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_85_);
v___x_87_ = v___x_77_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_env_68_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_nextMacroScope_69_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v_ngen_70_);
lean_ctor_set(v_reuseFailAlloc_90_, 3, v_auxDeclNGen_71_);
lean_ctor_set(v_reuseFailAlloc_90_, 4, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_90_, 5, v_cache_72_);
lean_ctor_set(v_reuseFailAlloc_90_, 6, v_messages_73_);
lean_ctor_set(v_reuseFailAlloc_90_, 7, v_infoState_74_);
lean_ctor_set(v_reuseFailAlloc_90_, 8, v_snapshotTasks_75_);
v___x_87_ = v_reuseFailAlloc_90_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_st_ref_set(v___y_61_, v___x_87_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v_traces_65_);
return v___x_89_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___boxed(lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_95_);
lean_dec(v___y_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0(lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___boxed(lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0(v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(lean_object* v_opts_114_, lean_object* v_opt_115_){
_start:
{
lean_object* v_name_116_; lean_object* v_defValue_117_; lean_object* v_map_118_; lean_object* v___x_119_; 
v_name_116_ = lean_ctor_get(v_opt_115_, 0);
v_defValue_117_ = lean_ctor_get(v_opt_115_, 1);
v_map_118_ = lean_ctor_get(v_opts_114_, 0);
v___x_119_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_118_, v_name_116_);
if (lean_obj_tag(v___x_119_) == 0)
{
uint8_t v___x_120_; 
v___x_120_ = lean_unbox(v_defValue_117_);
return v___x_120_;
}
else
{
lean_object* v_val_121_; 
v_val_121_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v___x_119_, 1);
if (lean_obj_tag(v_val_121_) == 1)
{
uint8_t v_v_122_; 
v_v_122_ = lean_ctor_get_uint8(v_val_121_, 0);
lean_dec_ref_known(v_val_121_, 0);
return v_v_122_;
}
else
{
uint8_t v___x_123_; 
lean_dec(v_val_121_);
v___x_123_ = lean_unbox(v_defValue_117_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1___boxed(lean_object* v_opts_124_, lean_object* v_opt_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_124_, v_opt_125_);
lean_dec_ref(v_opt_125_);
lean_dec_ref(v_opts_124_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__0));
v___x_130_ = l_Lean_stringToMessageData(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__2));
v___x_133_ = l_Lean_stringToMessageData(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0(lean_object* v___x_134_, lean_object* v_val_135_, lean_object* v_x_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_name_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_158_; 
v_name_144_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v___x_134_, 1);
lean_dec(v_unused_159_);
v___x_146_ = v___x_134_;
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_name_144_);
lean_dec(v___x_134_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_158_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_148_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1);
v___x_149_ = l_Lean_MessageData_ofName(v_name_144_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 7);
lean_ctor_set(v___x_146_, 1, v___x_149_);
lean_ctor_set(v___x_146_, 0, v___x_148_);
v___x_151_ = v___x_146_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_157_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3);
v___x_153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v_val_135_);
v___x_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed(lean_object* v___x_160_, lean_object* v_val_161_, lean_object* v_x_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0(v___x_160_, v_val_161_, v_x_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec_ref(v_x_162_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1(lean_object* v___x_171_, lean_object* v_g_172_, lean_object* v_x_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_name_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_195_; 
v_name_181_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v___x_171_, 1);
lean_dec(v_unused_196_);
v___x_183_ = v___x_171_;
v_isShared_184_ = v_isSharedCheck_195_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_name_181_);
lean_dec(v___x_171_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_195_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__1);
v___x_186_ = l_Lean_MessageData_ofName(v_name_181_);
if (v_isShared_184_ == 0)
{
lean_ctor_set_tag(v___x_183_, 7);
lean_ctor_set(v___x_183_, 1, v___x_186_);
lean_ctor_set(v___x_183_, 0, v___x_185_);
v___x_188_ = v___x_183_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___closed__3);
v___x_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v_g_172_);
v___x_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed(lean_object* v___x_197_, lean_object* v_g_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1(v___x_197_, v_g_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec_ref(v_x_199_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(lean_object* v_msgData_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; lean_object* v_env_215_; lean_object* v___x_216_; lean_object* v_mctx_217_; lean_object* v_lctx_218_; lean_object* v_options_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_214_ = lean_st_ref_get(v___y_212_);
v_env_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_ref(v_env_215_);
lean_dec(v___x_214_);
v___x_216_ = lean_st_ref_get(v___y_210_);
v_mctx_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc_ref(v_mctx_217_);
lean_dec(v___x_216_);
v_lctx_218_ = lean_ctor_get(v___y_209_, 2);
v_options_219_ = lean_ctor_get(v___y_211_, 2);
lean_inc_ref(v_options_219_);
lean_inc_ref(v_lctx_218_);
v___x_220_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_220_, 0, v_env_215_);
lean_ctor_set(v___x_220_, 1, v_mctx_217_);
lean_ctor_set(v___x_220_, 2, v_lctx_218_);
lean_ctor_set(v___x_220_, 3, v_options_219_);
v___x_221_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_msgData_208_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7___boxed(lean_object* v_msgData_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msgData_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_230_; double v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_float_of_nat(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(lean_object* v_cls_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_ref_242_; lean_object* v___x_243_; lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_288_; 
v_ref_242_ = lean_ctor_get(v___y_239_, 5);
v___x_243_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_288_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_288_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_288_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v_traceState_249_; lean_object* v_env_250_; lean_object* v_nextMacroScope_251_; lean_object* v_ngen_252_; lean_object* v_auxDeclNGen_253_; lean_object* v_cache_254_; lean_object* v_messages_255_; lean_object* v_infoState_256_; lean_object* v_snapshotTasks_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_287_; 
v___x_248_ = lean_st_ref_take(v___y_240_);
v_traceState_249_ = lean_ctor_get(v___x_248_, 4);
v_env_250_ = lean_ctor_get(v___x_248_, 0);
v_nextMacroScope_251_ = lean_ctor_get(v___x_248_, 1);
v_ngen_252_ = lean_ctor_get(v___x_248_, 2);
v_auxDeclNGen_253_ = lean_ctor_get(v___x_248_, 3);
v_cache_254_ = lean_ctor_get(v___x_248_, 5);
v_messages_255_ = lean_ctor_get(v___x_248_, 6);
v_infoState_256_ = lean_ctor_get(v___x_248_, 7);
v_snapshotTasks_257_ = lean_ctor_get(v___x_248_, 8);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_287_ == 0)
{
v___x_259_ = v___x_248_;
v_isShared_260_ = v_isSharedCheck_287_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_snapshotTasks_257_);
lean_inc(v_infoState_256_);
lean_inc(v_messages_255_);
lean_inc(v_cache_254_);
lean_inc(v_traceState_249_);
lean_inc(v_auxDeclNGen_253_);
lean_inc(v_ngen_252_);
lean_inc(v_nextMacroScope_251_);
lean_inc(v_env_250_);
lean_dec(v___x_248_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_287_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint64_t v_tid_261_; lean_object* v_traces_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_286_; 
v_tid_261_ = lean_ctor_get_uint64(v_traceState_249_, sizeof(void*)*1);
v_traces_262_ = lean_ctor_get(v_traceState_249_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_traceState_249_);
if (v_isSharedCheck_286_ == 0)
{
v___x_264_ = v_traceState_249_;
v_isShared_265_ = v_isSharedCheck_286_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_traces_262_);
lean_dec(v_traceState_249_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_286_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; double v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
v___x_268_ = 0;
v___x_269_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1));
v___x_270_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_270_, 0, v_cls_235_);
lean_ctor_set(v___x_270_, 1, v___x_266_);
lean_ctor_set(v___x_270_, 2, v___x_269_);
lean_ctor_set_float(v___x_270_, sizeof(void*)*3, v___x_267_);
lean_ctor_set_float(v___x_270_, sizeof(void*)*3 + 8, v___x_267_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*3 + 16, v___x_268_);
v___x_271_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__2));
v___x_272_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v_a_244_);
lean_ctor_set(v___x_272_, 2, v___x_271_);
lean_inc(v_ref_242_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_ref_242_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = l_Lean_PersistentArray_push___redArg(v_traces_262_, v___x_273_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_274_);
v___x_276_ = v___x_264_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_274_);
lean_ctor_set_uint64(v_reuseFailAlloc_285_, sizeof(void*)*1, v_tid_261_);
v___x_276_ = v_reuseFailAlloc_285_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 4, v___x_276_);
v___x_278_ = v___x_259_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_env_250_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_nextMacroScope_251_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_ngen_252_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_auxDeclNGen_253_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_284_, 5, v_cache_254_);
lean_ctor_set(v_reuseFailAlloc_284_, 6, v_messages_255_);
lean_ctor_set(v_reuseFailAlloc_284_, 7, v_infoState_256_);
lean_ctor_set(v_reuseFailAlloc_284_, 8, v_snapshotTasks_257_);
v___x_278_ = v_reuseFailAlloc_284_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = lean_st_ref_set(v___y_240_, v___x_278_);
v___x_280_ = lean_box(0);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_280_);
v___x_282_ = v___x_246_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___boxed(lean_object* v_cls_289_, lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v_cls_289_, v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(lean_object* v_opts_297_, lean_object* v_opt_298_){
_start:
{
lean_object* v_name_299_; lean_object* v_defValue_300_; lean_object* v_map_301_; lean_object* v___x_302_; 
v_name_299_ = lean_ctor_get(v_opt_298_, 0);
v_defValue_300_ = lean_ctor_get(v_opt_298_, 1);
v_map_301_ = lean_ctor_get(v_opts_297_, 0);
v___x_302_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_301_, v_name_299_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_inc(v_defValue_300_);
return v_defValue_300_;
}
else
{
lean_object* v_val_303_; 
v_val_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_val_303_);
lean_dec_ref_known(v___x_302_, 1);
if (lean_obj_tag(v_val_303_) == 3)
{
lean_object* v_v_304_; 
v_v_304_ = lean_ctor_get(v_val_303_, 0);
lean_inc(v_v_304_);
lean_dec_ref_known(v_val_303_, 1);
return v_v_304_;
}
else
{
lean_dec(v_val_303_);
lean_inc(v_defValue_300_);
return v_defValue_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5___boxed(lean_object* v_opts_305_, lean_object* v_opt_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_305_, v_opt_306_);
lean_dec_ref(v_opt_306_);
lean_dec_ref(v_opts_305_);
return v_res_307_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(lean_object* v_e_308_){
_start:
{
if (lean_obj_tag(v_e_308_) == 0)
{
uint8_t v___x_309_; 
v___x_309_ = 2;
return v___x_309_;
}
else
{
lean_object* v_a_310_; 
v_a_310_ = lean_ctor_get(v_e_308_, 0);
if (lean_obj_tag(v_a_310_) == 0)
{
uint8_t v___x_311_; 
v___x_311_ = 1;
return v___x_311_;
}
else
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4___boxed(lean_object* v_e_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(v_e_313_);
lean_dec_ref(v_e_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2_spec__3(size_t v_sz_316_, size_t v_i_317_, lean_object* v_bs_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = lean_usize_dec_lt(v_i_317_, v_sz_316_);
if (v___x_319_ == 0)
{
return v_bs_318_;
}
else
{
lean_object* v_v_320_; lean_object* v_msg_321_; lean_object* v___x_322_; lean_object* v_bs_x27_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v_v_320_ = lean_array_uget_borrowed(v_bs_318_, v_i_317_);
v_msg_321_ = lean_ctor_get(v_v_320_, 1);
lean_inc_ref(v_msg_321_);
v___x_322_ = lean_unsigned_to_nat(0u);
v_bs_x27_323_ = lean_array_uset(v_bs_318_, v_i_317_, v___x_322_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_317_, v___x_324_);
v___x_326_ = lean_array_uset(v_bs_x27_323_, v_i_317_, v_msg_321_);
v_i_317_ = v___x_325_;
v_bs_318_ = v___x_326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_328_, lean_object* v_i_329_, lean_object* v_bs_330_){
_start:
{
size_t v_sz_boxed_331_; size_t v_i_boxed_332_; lean_object* v_res_333_; 
v_sz_boxed_331_ = lean_unbox_usize(v_sz_328_);
lean_dec(v_sz_328_);
v_i_boxed_332_ = lean_unbox_usize(v_i_329_);
lean_dec(v_i_329_);
v_res_333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2_spec__3(v_sz_boxed_331_, v_i_boxed_332_, v_bs_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___redArg(lean_object* v_oldTraces_334_, lean_object* v_data_335_, lean_object* v_ref_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_fileName_343_; lean_object* v_fileMap_344_; lean_object* v_options_345_; lean_object* v_currRecDepth_346_; lean_object* v_maxRecDepth_347_; lean_object* v_ref_348_; lean_object* v_currNamespace_349_; lean_object* v_openDecls_350_; lean_object* v_initHeartbeats_351_; lean_object* v_maxHeartbeats_352_; lean_object* v_quotContext_353_; lean_object* v_currMacroScope_354_; uint8_t v_diag_355_; lean_object* v_cancelTk_x3f_356_; uint8_t v_suppressElabErrors_357_; lean_object* v_inheritedTraceOptions_358_; lean_object* v___x_359_; lean_object* v_traceState_360_; lean_object* v_traces_361_; lean_object* v_ref_362_; lean_object* v___x_363_; lean_object* v___x_364_; size_t v_sz_365_; size_t v___x_366_; lean_object* v___x_367_; lean_object* v_msg_368_; lean_object* v___x_369_; lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_407_; 
v_fileName_343_ = lean_ctor_get(v___y_340_, 0);
v_fileMap_344_ = lean_ctor_get(v___y_340_, 1);
v_options_345_ = lean_ctor_get(v___y_340_, 2);
v_currRecDepth_346_ = lean_ctor_get(v___y_340_, 3);
v_maxRecDepth_347_ = lean_ctor_get(v___y_340_, 4);
v_ref_348_ = lean_ctor_get(v___y_340_, 5);
v_currNamespace_349_ = lean_ctor_get(v___y_340_, 6);
v_openDecls_350_ = lean_ctor_get(v___y_340_, 7);
v_initHeartbeats_351_ = lean_ctor_get(v___y_340_, 8);
v_maxHeartbeats_352_ = lean_ctor_get(v___y_340_, 9);
v_quotContext_353_ = lean_ctor_get(v___y_340_, 10);
v_currMacroScope_354_ = lean_ctor_get(v___y_340_, 11);
v_diag_355_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*14);
v_cancelTk_x3f_356_ = lean_ctor_get(v___y_340_, 12);
v_suppressElabErrors_357_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_358_ = lean_ctor_get(v___y_340_, 13);
v___x_359_ = lean_st_ref_get(v___y_341_);
v_traceState_360_ = lean_ctor_get(v___x_359_, 4);
lean_inc_ref(v_traceState_360_);
lean_dec(v___x_359_);
v_traces_361_ = lean_ctor_get(v_traceState_360_, 0);
lean_inc_ref(v_traces_361_);
lean_dec_ref(v_traceState_360_);
v_ref_362_ = l_Lean_replaceRef(v_ref_336_, v_ref_348_);
lean_inc_ref(v_inheritedTraceOptions_358_);
lean_inc(v_cancelTk_x3f_356_);
lean_inc(v_currMacroScope_354_);
lean_inc(v_quotContext_353_);
lean_inc(v_maxHeartbeats_352_);
lean_inc(v_initHeartbeats_351_);
lean_inc(v_openDecls_350_);
lean_inc(v_currNamespace_349_);
lean_inc(v_maxRecDepth_347_);
lean_inc(v_currRecDepth_346_);
lean_inc_ref(v_options_345_);
lean_inc_ref(v_fileMap_344_);
lean_inc_ref(v_fileName_343_);
v___x_363_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_363_, 0, v_fileName_343_);
lean_ctor_set(v___x_363_, 1, v_fileMap_344_);
lean_ctor_set(v___x_363_, 2, v_options_345_);
lean_ctor_set(v___x_363_, 3, v_currRecDepth_346_);
lean_ctor_set(v___x_363_, 4, v_maxRecDepth_347_);
lean_ctor_set(v___x_363_, 5, v_ref_362_);
lean_ctor_set(v___x_363_, 6, v_currNamespace_349_);
lean_ctor_set(v___x_363_, 7, v_openDecls_350_);
lean_ctor_set(v___x_363_, 8, v_initHeartbeats_351_);
lean_ctor_set(v___x_363_, 9, v_maxHeartbeats_352_);
lean_ctor_set(v___x_363_, 10, v_quotContext_353_);
lean_ctor_set(v___x_363_, 11, v_currMacroScope_354_);
lean_ctor_set(v___x_363_, 12, v_cancelTk_x3f_356_);
lean_ctor_set(v___x_363_, 13, v_inheritedTraceOptions_358_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*14, v_diag_355_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*14 + 1, v_suppressElabErrors_357_);
v___x_364_ = l_Lean_PersistentArray_toArray___redArg(v_traces_361_);
lean_dec_ref(v_traces_361_);
v_sz_365_ = lean_array_size(v___x_364_);
v___x_366_ = ((size_t)0ULL);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2_spec__3(v_sz_365_, v___x_366_, v___x_364_);
v_msg_368_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_368_, 0, v_data_335_);
lean_ctor_set(v_msg_368_, 1, v_msg_337_);
lean_ctor_set(v_msg_368_, 2, v___x_367_);
v___x_369_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_368_, v___y_338_, v___y_339_, v___x_363_, v___y_341_);
lean_dec_ref_known(v___x_363_, 14);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_407_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_407_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_407_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v_traceState_375_; lean_object* v_env_376_; lean_object* v_nextMacroScope_377_; lean_object* v_ngen_378_; lean_object* v_auxDeclNGen_379_; lean_object* v_cache_380_; lean_object* v_messages_381_; lean_object* v_infoState_382_; lean_object* v_snapshotTasks_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_406_; 
v___x_374_ = lean_st_ref_take(v___y_341_);
v_traceState_375_ = lean_ctor_get(v___x_374_, 4);
v_env_376_ = lean_ctor_get(v___x_374_, 0);
v_nextMacroScope_377_ = lean_ctor_get(v___x_374_, 1);
v_ngen_378_ = lean_ctor_get(v___x_374_, 2);
v_auxDeclNGen_379_ = lean_ctor_get(v___x_374_, 3);
v_cache_380_ = lean_ctor_get(v___x_374_, 5);
v_messages_381_ = lean_ctor_get(v___x_374_, 6);
v_infoState_382_ = lean_ctor_get(v___x_374_, 7);
v_snapshotTasks_383_ = lean_ctor_get(v___x_374_, 8);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_406_ == 0)
{
v___x_385_ = v___x_374_;
v_isShared_386_ = v_isSharedCheck_406_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_snapshotTasks_383_);
lean_inc(v_infoState_382_);
lean_inc(v_messages_381_);
lean_inc(v_cache_380_);
lean_inc(v_traceState_375_);
lean_inc(v_auxDeclNGen_379_);
lean_inc(v_ngen_378_);
lean_inc(v_nextMacroScope_377_);
lean_inc(v_env_376_);
lean_dec(v___x_374_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_406_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint64_t v_tid_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_404_; 
v_tid_387_ = lean_ctor_get_uint64(v_traceState_375_, sizeof(void*)*1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_traceState_375_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v_traceState_375_, 0);
lean_dec(v_unused_405_);
v___x_389_ = v_traceState_375_;
v_isShared_390_ = v_isSharedCheck_404_;
goto v_resetjp_388_;
}
else
{
lean_dec(v_traceState_375_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_404_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_ref_336_);
lean_ctor_set(v___x_391_, 1, v_a_370_);
v___x_392_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_334_, v___x_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_392_);
lean_ctor_set_uint64(v_reuseFailAlloc_403_, sizeof(void*)*1, v_tid_387_);
v___x_394_ = v_reuseFailAlloc_403_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 4, v___x_394_);
v___x_396_ = v___x_385_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_env_376_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_nextMacroScope_377_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_ngen_378_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_auxDeclNGen_379_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_402_, 5, v_cache_380_);
lean_ctor_set(v_reuseFailAlloc_402_, 6, v_messages_381_);
lean_ctor_set(v_reuseFailAlloc_402_, 7, v_infoState_382_);
lean_ctor_set(v_reuseFailAlloc_402_, 8, v_snapshotTasks_383_);
v___x_396_ = v_reuseFailAlloc_402_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_st_ref_set(v___y_341_, v___x_396_);
v___x_398_ = lean_box(0);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_398_);
v___x_400_ = v___x_372_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_408_, lean_object* v_data_409_, lean_object* v_ref_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___redArg(v_oldTraces_408_, v_data_409_, v_ref_410_, v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_a_420_ = lean_ctor_get(v_x_418_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v_x_418_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v_x_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 1);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v_x_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v_x_418_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v_x_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 0);
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg___boxed(lean_object* v_x_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_x_436_);
return v_res_438_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__0));
v___x_441_ = l_Lean_stringToMessageData(v___x_440_);
return v___x_441_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2(void){
_start:
{
lean_object* v___x_442_; double v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(1000u);
v___x_443_ = lean_float_of_nat(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(lean_object* v_cls_444_, uint8_t v_collapsed_445_, lean_object* v_tag_446_, lean_object* v_opts_447_, uint8_t v_clsEnabled_448_, lean_object* v_oldTraces_449_, lean_object* v_msg_450_, lean_object* v_resStartStop_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_fst_459_; lean_object* v_snd_460_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v_data_464_; lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v___x_477_; uint8_t v___x_478_; lean_object* v___y_480_; lean_object* v_a_481_; uint8_t v___y_496_; double v___y_527_; 
v_fst_459_ = lean_ctor_get(v_resStartStop_451_, 0);
lean_inc(v_fst_459_);
v_snd_460_ = lean_ctor_get(v_resStartStop_451_, 1);
lean_inc(v_snd_460_);
lean_dec_ref(v_resStartStop_451_);
v_fst_475_ = lean_ctor_get(v_snd_460_, 0);
lean_inc(v_fst_475_);
v_snd_476_ = lean_ctor_get(v_snd_460_, 1);
lean_inc(v_snd_476_);
lean_dec(v_snd_460_);
v___x_477_ = l_Lean_trace_profiler;
v___x_478_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_447_, v___x_477_);
if (v___x_478_ == 0)
{
v___y_496_ = v___x_478_;
goto v___jp_495_;
}
else
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = l_Lean_trace_profiler_useHeartbeats;
v___x_533_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_447_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; double v___x_536_; double v___x_537_; double v___x_538_; 
v___x_534_ = l_Lean_trace_profiler_threshold;
v___x_535_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_447_, v___x_534_);
v___x_536_ = lean_float_of_nat(v___x_535_);
v___x_537_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2);
v___x_538_ = lean_float_div(v___x_536_, v___x_537_);
v___y_527_ = v___x_538_;
goto v___jp_526_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; double v___x_541_; 
v___x_539_ = l_Lean_trace_profiler_threshold;
v___x_540_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_447_, v___x_539_);
v___x_541_ = lean_float_of_nat(v___x_540_);
v___y_527_ = v___x_541_;
goto v___jp_526_;
}
}
v___jp_461_:
{
lean_object* v___x_465_; 
lean_inc(v___y_462_);
v___x_465_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___redArg(v_oldTraces_449_, v_data_464_, v___y_462_, v___y_463_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; 
lean_dec_ref_known(v___x_465_, 1);
v___x_466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_fst_459_);
return v___x_466_;
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_fst_459_);
v_a_467_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_465_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
v___jp_479_:
{
uint8_t v_result_482_; lean_object* v___x_483_; lean_object* v___x_484_; double v___x_485_; lean_object* v_data_486_; 
v_result_482_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(v_fst_459_);
v___x_483_ = lean_box(v_result_482_);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
v___x_485_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_446_);
lean_inc_ref(v___x_484_);
lean_inc(v_cls_444_);
v_data_486_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_486_, 0, v_cls_444_);
lean_ctor_set(v_data_486_, 1, v___x_484_);
lean_ctor_set(v_data_486_, 2, v_tag_446_);
lean_ctor_set_float(v_data_486_, sizeof(void*)*3, v___x_485_);
lean_ctor_set_float(v_data_486_, sizeof(void*)*3 + 8, v___x_485_);
lean_ctor_set_uint8(v_data_486_, sizeof(void*)*3 + 16, v_collapsed_445_);
if (v___x_478_ == 0)
{
lean_dec_ref_known(v___x_484_, 1);
lean_dec(v_snd_476_);
lean_dec(v_fst_475_);
lean_dec_ref(v_tag_446_);
lean_dec(v_cls_444_);
v___y_462_ = v___y_480_;
v___y_463_ = v_a_481_;
v_data_464_ = v_data_486_;
goto v___jp_461_;
}
else
{
lean_object* v_data_487_; double v___x_488_; double v___x_489_; 
lean_dec_ref_known(v_data_486_, 3);
v_data_487_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_487_, 0, v_cls_444_);
lean_ctor_set(v_data_487_, 1, v___x_484_);
lean_ctor_set(v_data_487_, 2, v_tag_446_);
v___x_488_ = lean_unbox_float(v_fst_475_);
lean_dec(v_fst_475_);
lean_ctor_set_float(v_data_487_, sizeof(void*)*3, v___x_488_);
v___x_489_ = lean_unbox_float(v_snd_476_);
lean_dec(v_snd_476_);
lean_ctor_set_float(v_data_487_, sizeof(void*)*3 + 8, v___x_489_);
lean_ctor_set_uint8(v_data_487_, sizeof(void*)*3 + 16, v_collapsed_445_);
v___y_462_ = v___y_480_;
v___y_463_ = v_a_481_;
v_data_464_ = v_data_487_;
goto v___jp_461_;
}
}
v___jp_490_:
{
lean_object* v_ref_491_; lean_object* v___x_492_; 
v_ref_491_ = lean_ctor_get(v___y_456_, 5);
lean_inc(v___y_457_);
lean_inc_ref(v___y_456_);
lean_inc(v___y_455_);
lean_inc_ref(v___y_454_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v_fst_459_);
v___x_492_ = lean_apply_8(v_msg_450_, v_fst_459_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, lean_box(0));
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v___y_480_ = v_ref_491_;
v_a_481_ = v_a_493_;
goto v___jp_479_;
}
else
{
lean_object* v___x_494_; 
lean_dec_ref_known(v___x_492_, 1);
v___x_494_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1);
v___y_480_ = v_ref_491_;
v_a_481_ = v___x_494_;
goto v___jp_479_;
}
}
v___jp_495_:
{
if (v_clsEnabled_448_ == 0)
{
if (v___y_496_ == 0)
{
lean_object* v___x_497_; lean_object* v_traceState_498_; lean_object* v_env_499_; lean_object* v_nextMacroScope_500_; lean_object* v_ngen_501_; lean_object* v_auxDeclNGen_502_; lean_object* v_cache_503_; lean_object* v_messages_504_; lean_object* v_infoState_505_; lean_object* v_snapshotTasks_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_snd_476_);
lean_dec(v_fst_475_);
lean_dec_ref(v_msg_450_);
lean_dec_ref(v_tag_446_);
lean_dec(v_cls_444_);
v___x_497_ = lean_st_ref_take(v___y_457_);
v_traceState_498_ = lean_ctor_get(v___x_497_, 4);
v_env_499_ = lean_ctor_get(v___x_497_, 0);
v_nextMacroScope_500_ = lean_ctor_get(v___x_497_, 1);
v_ngen_501_ = lean_ctor_get(v___x_497_, 2);
v_auxDeclNGen_502_ = lean_ctor_get(v___x_497_, 3);
v_cache_503_ = lean_ctor_get(v___x_497_, 5);
v_messages_504_ = lean_ctor_get(v___x_497_, 6);
v_infoState_505_ = lean_ctor_get(v___x_497_, 7);
v_snapshotTasks_506_ = lean_ctor_get(v___x_497_, 8);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_525_ == 0)
{
v___x_508_ = v___x_497_;
v_isShared_509_ = v_isSharedCheck_525_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snapshotTasks_506_);
lean_inc(v_infoState_505_);
lean_inc(v_messages_504_);
lean_inc(v_cache_503_);
lean_inc(v_traceState_498_);
lean_inc(v_auxDeclNGen_502_);
lean_inc(v_ngen_501_);
lean_inc(v_nextMacroScope_500_);
lean_inc(v_env_499_);
lean_dec(v___x_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_525_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
uint64_t v_tid_510_; lean_object* v_traces_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_524_; 
v_tid_510_ = lean_ctor_get_uint64(v_traceState_498_, sizeof(void*)*1);
v_traces_511_ = lean_ctor_get(v_traceState_498_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_traceState_498_);
if (v_isSharedCheck_524_ == 0)
{
v___x_513_ = v_traceState_498_;
v_isShared_514_ = v_isSharedCheck_524_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_traces_511_);
lean_dec(v_traceState_498_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_524_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_449_, v_traces_511_);
lean_dec_ref(v_traces_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_515_);
lean_ctor_set_uint64(v_reuseFailAlloc_523_, sizeof(void*)*1, v_tid_510_);
v___x_517_ = v_reuseFailAlloc_523_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v___x_517_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_env_499_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_nextMacroScope_500_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_ngen_501_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_auxDeclNGen_502_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_522_, 5, v_cache_503_);
lean_ctor_set(v_reuseFailAlloc_522_, 6, v_messages_504_);
lean_ctor_set(v_reuseFailAlloc_522_, 7, v_infoState_505_);
lean_ctor_set(v_reuseFailAlloc_522_, 8, v_snapshotTasks_506_);
v___x_519_ = v_reuseFailAlloc_522_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_st_ref_set(v___y_457_, v___x_519_);
v___x_521_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_fst_459_);
return v___x_521_;
}
}
}
}
}
else
{
goto v___jp_490_;
}
}
else
{
goto v___jp_490_;
}
}
v___jp_526_:
{
double v___x_528_; double v___x_529_; double v___x_530_; uint8_t v___x_531_; 
v___x_528_ = lean_unbox_float(v_snd_476_);
v___x_529_ = lean_unbox_float(v_fst_475_);
v___x_530_ = lean_float_sub(v___x_528_, v___x_529_);
v___x_531_ = lean_float_decLt(v___y_527_, v___x_530_);
v___y_496_ = v___x_531_;
goto v___jp_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___boxed(lean_object* v_cls_542_, lean_object* v_collapsed_543_, lean_object* v_tag_544_, lean_object* v_opts_545_, lean_object* v_clsEnabled_546_, lean_object* v_oldTraces_547_, lean_object* v_msg_548_, lean_object* v_resStartStop_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
uint8_t v_collapsed_boxed_557_; uint8_t v_clsEnabled_boxed_558_; lean_object* v_res_559_; 
v_collapsed_boxed_557_ = lean_unbox(v_collapsed_543_);
v_clsEnabled_boxed_558_ = lean_unbox(v_clsEnabled_546_);
v_res_559_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v_cls_542_, v_collapsed_boxed_557_, v_tag_544_, v_opts_545_, v_clsEnabled_boxed_558_, v_oldTraces_547_, v_msg_548_, v_resStartStop_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_opts_545_);
return v_res_559_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4(void){
_start:
{
lean_object* v___x_567_; double v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(1000000000u);
v___x_568_ = lean_float_of_nat(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3));
v___x_573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__6));
v___x_574_ = l_Lean_Name_append(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__8));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__10));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(lean_object* v_g_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_box(0);
v___x_590_ = l_Lean_MVarId_falseOrByContra(v_g_581_, v___x_589_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_1381_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_1381_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_1381_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
if (lean_obj_tag(v_a_591_) == 1)
{
lean_object* v_options_595_; lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_1377_; 
lean_del_object(v___x_593_);
v_options_595_ = lean_ctor_get(v_a_586_, 2);
v_val_596_ = lean_ctor_get(v_a_591_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_a_591_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_598_ = v_a_591_;
v_isShared_599_ = v_isSharedCheck_1377_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_dec(v_a_591_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_1377_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_inheritedTraceOptions_600_; uint8_t v_hasTrace_601_; lean_object* v___x_602_; lean_object* v___y_604_; uint8_t v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; uint8_t v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v_a_617_; lean_object* v___y_627_; uint8_t v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v_a_640_; lean_object* v___y_653_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_744_; lean_object* v_g_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; uint8_t v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; uint8_t v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v_a_804_; uint8_t v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; uint8_t v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v_a_828_; uint8_t v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; uint8_t v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_896_; uint8_t v_fixedInt_897_; lean_object* v_g_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; uint8_t v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; uint8_t v___y_952_; lean_object* v_a_953_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; uint8_t v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v___y_976_; lean_object* v_a_977_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; uint8_t v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; uint8_t v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1045_; uint8_t v_fixedInt_1046_; uint8_t v_enums_1047_; lean_object* v_g_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1090_; lean_object* v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v_a_1104_; lean_object* v___y_1114_; lean_object* v___y_1115_; uint8_t v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v_a_1128_; lean_object* v___y_1141_; lean_object* v___y_1142_; uint8_t v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; uint8_t v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; uint8_t v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; lean_object* v___y_1243_; lean_object* v_a_1244_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; uint8_t v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; uint8_t v___y_1265_; lean_object* v___y_1266_; lean_object* v_a_1267_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; uint8_t v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; 
v_inheritedTraceOptions_600_ = lean_ctor_get(v_a_586_, 13);
v_hasTrace_601_ = lean_ctor_get_uint8(v_options_595_, sizeof(void*)*1);
v___x_602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3));
if (v_hasTrace_601_ == 0)
{
v___y_1354_ = v_a_582_;
v___y_1355_ = v_a_583_;
v___y_1356_ = v_a_584_;
v___y_1357_ = v_a_585_;
v___y_1358_ = v_a_586_;
v___y_1359_ = v_a_587_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
v___x_1364_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_600_, v_options_595_, v___x_1363_);
if (v___x_1364_ == 0)
{
v___y_1354_ = v_a_582_;
v___y_1355_ = v_a_583_;
v___y_1356_ = v_a_584_;
v___y_1357_ = v_a_585_;
v___y_1358_ = v_a_586_;
v___y_1359_ = v_a_587_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__11);
lean_inc(v_val_596_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_val_596_);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v___x_602_, v___x_1367_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_dec_ref_known(v___x_1368_, 1);
v___y_1354_ = v_a_582_;
v___y_1355_ = v_a_583_;
v___y_1356_ = v_a_584_;
v___y_1357_ = v_a_585_;
v___y_1358_ = v_a_586_;
v___y_1359_ = v_a_587_;
goto v___jp_1353_;
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_del_object(v___x_598_);
lean_dec(v_val_596_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
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
}
v___jp_603_:
{
lean_object* v___x_618_; double v___x_619_; double v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_618_ = lean_io_get_num_heartbeats();
v___x_619_ = lean_float_of_nat(v___y_606_);
v___x_620_ = lean_float_of_nat(v___x_618_);
v___x_621_ = lean_box_float(v___x_619_);
v___x_622_ = lean_box_float(v___x_620_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_a_617_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
lean_inc_ref(v___y_613_);
v___x_625_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_611_, v___y_613_, v___y_608_, v___y_605_, v___y_612_, v___y_614_, v___x_624_, v___y_604_, v___y_610_, v___y_615_, v___y_607_, v___y_609_, v___y_616_);
return v___x_625_;
}
v___jp_626_:
{
lean_object* v___x_641_; double v___x_642_; double v___x_643_; double v___x_644_; double v___x_645_; double v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_641_ = lean_io_mono_nanos_now();
v___x_642_ = lean_float_of_nat(v___y_630_);
v___x_643_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
v___x_644_ = lean_float_div(v___x_642_, v___x_643_);
v___x_645_ = lean_float_of_nat(v___x_641_);
v___x_646_ = lean_float_div(v___x_645_, v___x_643_);
v___x_647_ = lean_box_float(v___x_644_);
v___x_648_ = lean_box_float(v___x_646_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_a_640_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
lean_inc_ref(v___y_636_);
v___x_651_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_634_, v___y_636_, v___y_631_, v___y_628_, v___y_635_, v___y_637_, v___x_650_, v___y_627_, v___y_633_, v___y_638_, v___y_629_, v___y_632_, v___y_639_);
return v___x_651_;
}
v___jp_652_:
{
lean_object* v___x_666_; lean_object* v_a_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_666_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_665_);
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v___x_668_ = l_Lean_trace_profiler_useHeartbeats;
v___x_669_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_656_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_io_mono_nanos_now();
lean_inc(v___y_665_);
lean_inc_ref(v___y_658_);
lean_inc(v___y_655_);
lean_inc_ref(v___y_664_);
lean_inc(v___y_659_);
lean_inc_ref(v___y_653_);
v___x_671_ = lean_apply_8(v___y_662_, v___y_657_, v___y_653_, v___y_659_, v___y_664_, v___y_655_, v___y_658_, v___y_665_, lean_box(0));
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set_tag(v___x_674_, 1);
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
v___y_627_ = v___y_653_;
v___y_628_ = v___y_654_;
v___y_629_ = v___y_655_;
v___y_630_ = v___x_670_;
v___y_631_ = v___y_656_;
v___y_632_ = v___y_658_;
v___y_633_ = v___y_659_;
v___y_634_ = v___y_660_;
v___y_635_ = v_a_667_;
v___y_636_ = v___y_661_;
v___y_637_ = v___y_663_;
v___y_638_ = v___y_664_;
v___y_639_ = v___y_665_;
v_a_640_ = v___x_677_;
goto v___jp_626_;
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_671_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_671_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
v___y_627_ = v___y_653_;
v___y_628_ = v___y_654_;
v___y_629_ = v___y_655_;
v___y_630_ = v___x_670_;
v___y_631_ = v___y_656_;
v___y_632_ = v___y_658_;
v___y_633_ = v___y_659_;
v___y_634_ = v___y_660_;
v___y_635_ = v_a_667_;
v___y_636_ = v___y_661_;
v___y_637_ = v___y_663_;
v___y_638_ = v___y_664_;
v___y_639_ = v___y_665_;
v_a_640_ = v___x_685_;
goto v___jp_626_;
}
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_io_get_num_heartbeats();
lean_inc(v___y_665_);
lean_inc_ref(v___y_658_);
lean_inc(v___y_655_);
lean_inc_ref(v___y_664_);
lean_inc(v___y_659_);
lean_inc_ref(v___y_653_);
v___x_689_ = lean_apply_8(v___y_662_, v___y_657_, v___y_653_, v___y_659_, v___y_664_, v___y_655_, v___y_658_, v___y_665_, lean_box(0));
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v___y_604_ = v___y_653_;
v___y_605_ = v___y_654_;
v___y_606_ = v___x_688_;
v___y_607_ = v___y_655_;
v___y_608_ = v___y_656_;
v___y_609_ = v___y_658_;
v___y_610_ = v___y_659_;
v___y_611_ = v___y_660_;
v___y_612_ = v_a_667_;
v___y_613_ = v___y_661_;
v___y_614_ = v___y_663_;
v___y_615_ = v___y_664_;
v___y_616_ = v___y_665_;
v_a_617_ = v___x_695_;
goto v___jp_603_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_a_698_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_689_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_689_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v___y_604_ = v___y_653_;
v___y_605_ = v___y_654_;
v___y_606_ = v___x_688_;
v___y_607_ = v___y_655_;
v___y_608_ = v___y_656_;
v___y_609_ = v___y_658_;
v___y_610_ = v___y_659_;
v___y_611_ = v___y_660_;
v___y_612_ = v_a_667_;
v___y_613_ = v___y_661_;
v___y_614_ = v___y_663_;
v___y_615_ = v___y_664_;
v___y_616_ = v___y_665_;
v_a_617_ = v___x_703_;
goto v___jp_603_;
}
}
}
}
}
v___jp_706_:
{
lean_object* v___x_715_; lean_object* v_a_716_; lean_object* v___x_717_; 
v___x_715_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_709_);
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref(v___x_715_);
v___x_717_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_716_, v___y_707_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v_a_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
if (lean_obj_tag(v_a_718_) == 1)
{
uint8_t v_shortCircuit_719_; 
v_shortCircuit_719_ = lean_ctor_get_uint8(v___y_708_, sizeof(void*)*2 + 9);
if (v_shortCircuit_719_ == 0)
{
lean_dec_ref_known(v_a_718_, 1);
return v___x_717_;
}
else
{
lean_object* v_val_720_; lean_object* v___x_721_; lean_object* v_options_722_; uint8_t v_hasTrace_723_; 
lean_dec_ref_known(v___x_717_, 1);
v_val_720_ = lean_ctor_get(v_a_718_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v_a_718_, 1);
v___x_721_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_options_722_ = lean_ctor_get(v___y_713_, 2);
v_hasTrace_723_ = lean_ctor_get_uint8(v_options_722_, sizeof(void*)*1);
if (v_hasTrace_723_ == 0)
{
lean_object* v_run_x27_724_; lean_object* v___x_725_; 
v_run_x27_724_ = lean_ctor_get(v___x_721_, 1);
lean_inc_ref(v_run_x27_724_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
v___x_725_ = lean_apply_8(v_run_x27_724_, v_val_720_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, lean_box(0));
return v___x_725_;
}
else
{
lean_object* v_run_x27_726_; lean_object* v_inheritedTraceOptions_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_run_x27_726_ = lean_ctor_get(v___x_721_, 1);
v_inheritedTraceOptions_727_ = lean_ctor_get(v___y_713_, 13);
lean_inc(v_val_720_);
v___f_728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed), 10, 2);
lean_closure_set(v___f_728_, 0, v___x_721_);
lean_closure_set(v___f_728_, 1, v_val_720_);
v___x_729_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1));
v___x_730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
v___x_731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_727_, v_options_722_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = l_Lean_trace_profiler;
v___x_733_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_722_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_dec_ref(v___f_728_);
lean_inc_ref(v_run_x27_726_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
v___x_734_ = lean_apply_8(v_run_x27_726_, v_val_720_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, lean_box(0));
return v___x_734_;
}
else
{
lean_inc_ref(v_run_x27_726_);
v___y_653_ = v___y_709_;
v___y_654_ = v___x_731_;
v___y_655_ = v___y_712_;
v___y_656_ = v_options_722_;
v___y_657_ = v_val_720_;
v___y_658_ = v___y_713_;
v___y_659_ = v___y_710_;
v___y_660_ = v_hasTrace_723_;
v___y_661_ = v___x_729_;
v___y_662_ = v_run_x27_726_;
v___y_663_ = v___f_728_;
v___y_664_ = v___y_711_;
v___y_665_ = v___y_714_;
goto v___jp_652_;
}
}
else
{
lean_inc_ref(v_run_x27_726_);
v___y_653_ = v___y_709_;
v___y_654_ = v___x_731_;
v___y_655_ = v___y_712_;
v___y_656_ = v_options_722_;
v___y_657_ = v_val_720_;
v___y_658_ = v___y_713_;
v___y_659_ = v___y_710_;
v___y_660_ = v_hasTrace_723_;
v___y_661_ = v___x_729_;
v___y_662_ = v_run_x27_726_;
v___y_663_ = v___f_728_;
v___y_664_ = v___y_711_;
v___y_665_ = v___y_714_;
goto v___jp_652_;
}
}
}
}
else
{
lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_a_718_);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_742_);
v___x_736_ = v___x_717_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_dec(v___x_717_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_589_);
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_589_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
return v___x_717_;
}
}
v___jp_743_:
{
lean_object* v_options_752_; uint8_t v_hasTrace_753_; 
v_options_752_ = lean_ctor_get(v___y_750_, 2);
v_hasTrace_753_ = lean_ctor_get_uint8(v_options_752_, sizeof(void*)*1);
if (v_hasTrace_753_ == 0)
{
lean_del_object(v___x_598_);
v___y_707_ = v_g_745_;
v___y_708_ = v___y_744_;
v___y_709_ = v___y_746_;
v___y_710_ = v___y_747_;
v___y_711_ = v___y_748_;
v___y_712_ = v___y_749_;
v___y_713_ = v___y_750_;
v___y_714_ = v___y_751_;
goto v___jp_706_;
}
else
{
lean_object* v_inheritedTraceOptions_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_inheritedTraceOptions_754_ = lean_ctor_get(v___y_750_, 13);
v___x_755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
v___x_756_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_754_, v_options_752_, v___x_755_);
if (v___x_756_ == 0)
{
lean_del_object(v___x_598_);
v___y_707_ = v_g_745_;
v___y_708_ = v___y_744_;
v___y_709_ = v___y_746_;
v___y_710_ = v___y_747_;
v___y_711_ = v___y_748_;
v___y_712_ = v___y_749_;
v___y_713_ = v___y_750_;
v___y_714_ = v___y_751_;
goto v___jp_706_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__9);
lean_inc(v_g_745_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_g_745_);
v___x_759_ = v___x_598_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_g_745_);
v___x_759_ = v_reuseFailAlloc_770_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v___x_602_, v___x_760_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_dec_ref_known(v___x_761_, 1);
v___y_707_ = v_g_745_;
v___y_708_ = v___y_744_;
v___y_709_ = v___y_746_;
v___y_710_ = v___y_747_;
v___y_711_ = v___y_748_;
v___y_712_ = v___y_749_;
v___y_713_ = v___y_750_;
v___y_714_ = v___y_751_;
goto v___jp_706_;
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_g_745_);
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
}
v___jp_771_:
{
if (lean_obj_tag(v___y_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_a_780_ = lean_ctor_get(v___y_779_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___y_779_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v___y_779_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___y_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
if (lean_obj_tag(v_a_780_) == 1)
{
lean_object* v_val_784_; 
lean_del_object(v___x_782_);
v_val_784_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v_a_780_, 1);
v___y_744_ = v___y_778_;
v_g_745_ = v_val_784_;
v___y_746_ = v___y_775_;
v___y_747_ = v___y_777_;
v___y_748_ = v___y_773_;
v___y_749_ = v___y_774_;
v___y_750_ = v___y_776_;
v___y_751_ = v___y_772_;
goto v___jp_743_;
}
else
{
lean_object* v___x_786_; 
lean_dec(v_a_780_);
lean_del_object(v___x_598_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_589_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_589_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_del_object(v___x_598_);
return v___y_779_;
}
}
v___jp_789_:
{
lean_object* v___x_805_; double v___x_806_; double v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_805_ = lean_io_get_num_heartbeats();
v___x_806_ = lean_float_of_nat(v___y_800_);
v___x_807_ = lean_float_of_nat(v___x_805_);
v___x_808_ = lean_box_float(v___x_806_);
v___x_809_ = lean_box_float(v___x_807_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_a_804_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
lean_inc_ref(v___y_792_);
v___x_812_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_795_, v___y_792_, v___y_793_, v___y_790_, v___y_799_, v___y_801_, v___x_811_, v___y_798_, v___y_802_, v___y_791_, v___y_797_, v___y_803_, v___y_796_);
v___y_772_ = v___y_796_;
v___y_773_ = v___y_791_;
v___y_774_ = v___y_797_;
v___y_775_ = v___y_798_;
v___y_776_ = v___y_803_;
v___y_777_ = v___y_802_;
v___y_778_ = v___y_794_;
v___y_779_ = v___x_812_;
goto v___jp_771_;
}
v___jp_813_:
{
lean_object* v___x_829_; double v___x_830_; double v___x_831_; double v___x_832_; double v___x_833_; double v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_829_ = lean_io_mono_nanos_now();
v___x_830_ = lean_float_of_nat(v___y_817_);
v___x_831_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
v___x_832_ = lean_float_div(v___x_830_, v___x_831_);
v___x_833_ = lean_float_of_nat(v___x_829_);
v___x_834_ = lean_float_div(v___x_833_, v___x_831_);
v___x_835_ = lean_box_float(v___x_832_);
v___x_836_ = lean_box_float(v___x_834_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_a_828_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
lean_inc_ref(v___y_816_);
v___x_839_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_820_, v___y_816_, v___y_818_, v___y_814_, v___y_824_, v___y_825_, v___x_838_, v___y_823_, v___y_826_, v___y_815_, v___y_822_, v___y_827_, v___y_821_);
v___y_772_ = v___y_821_;
v___y_773_ = v___y_815_;
v___y_774_ = v___y_822_;
v___y_775_ = v___y_823_;
v___y_776_ = v___y_827_;
v___y_777_ = v___y_826_;
v___y_778_ = v___y_819_;
v___y_779_ = v___x_839_;
goto v___jp_771_;
}
v___jp_840_:
{
lean_object* v___x_855_; lean_object* v_a_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_855_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_849_);
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_855_);
v___x_857_ = l_Lean_trace_profiler_useHeartbeats;
v___x_858_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_846_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_io_mono_nanos_now();
lean_inc(v___y_849_);
lean_inc_ref(v___y_854_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_853_);
lean_inc_ref(v___y_851_);
v___x_860_ = lean_apply_8(v___y_845_, v___y_843_, v___y_851_, v___y_853_, v___y_842_, v___y_850_, v___y_854_, v___y_849_, lean_box(0));
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 1);
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
v___y_814_ = v___y_841_;
v___y_815_ = v___y_842_;
v___y_816_ = v___y_844_;
v___y_817_ = v___x_859_;
v___y_818_ = v___y_846_;
v___y_819_ = v___y_847_;
v___y_820_ = v___y_848_;
v___y_821_ = v___y_849_;
v___y_822_ = v___y_850_;
v___y_823_ = v___y_851_;
v___y_824_ = v_a_856_;
v___y_825_ = v___y_852_;
v___y_826_ = v___y_853_;
v___y_827_ = v___y_854_;
v_a_828_ = v___x_866_;
goto v___jp_813_;
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_860_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_860_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set_tag(v___x_871_, 0);
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
v___y_814_ = v___y_841_;
v___y_815_ = v___y_842_;
v___y_816_ = v___y_844_;
v___y_817_ = v___x_859_;
v___y_818_ = v___y_846_;
v___y_819_ = v___y_847_;
v___y_820_ = v___y_848_;
v___y_821_ = v___y_849_;
v___y_822_ = v___y_850_;
v___y_823_ = v___y_851_;
v___y_824_ = v_a_856_;
v___y_825_ = v___y_852_;
v___y_826_ = v___y_853_;
v___y_827_ = v___y_854_;
v_a_828_ = v___x_874_;
goto v___jp_813_;
}
}
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_io_get_num_heartbeats();
lean_inc(v___y_849_);
lean_inc_ref(v___y_854_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_853_);
lean_inc_ref(v___y_851_);
v___x_878_ = lean_apply_8(v___y_845_, v___y_843_, v___y_851_, v___y_853_, v___y_842_, v___y_850_, v___y_854_, v___y_849_, lean_box(0));
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 1);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v___y_790_ = v___y_841_;
v___y_791_ = v___y_842_;
v___y_792_ = v___y_844_;
v___y_793_ = v___y_846_;
v___y_794_ = v___y_847_;
v___y_795_ = v___y_848_;
v___y_796_ = v___y_849_;
v___y_797_ = v___y_850_;
v___y_798_ = v___y_851_;
v___y_799_ = v_a_856_;
v___y_800_ = v___x_877_;
v___y_801_ = v___y_852_;
v___y_802_ = v___y_853_;
v___y_803_ = v___y_854_;
v_a_804_ = v___x_884_;
goto v___jp_789_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_878_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_878_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 0);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
v___y_790_ = v___y_841_;
v___y_791_ = v___y_842_;
v___y_792_ = v___y_844_;
v___y_793_ = v___y_846_;
v___y_794_ = v___y_847_;
v___y_795_ = v___y_848_;
v___y_796_ = v___y_849_;
v___y_797_ = v___y_850_;
v___y_798_ = v___y_851_;
v___y_799_ = v_a_856_;
v___y_800_ = v___x_877_;
v___y_801_ = v___y_852_;
v___y_802_ = v___y_853_;
v___y_803_ = v___y_854_;
v_a_804_ = v___x_892_;
goto v___jp_789_;
}
}
}
}
}
v___jp_895_:
{
if (v_fixedInt_897_ == 0)
{
v___y_744_ = v___y_896_;
v_g_745_ = v_g_898_;
v___y_746_ = v___y_899_;
v___y_747_ = v___y_900_;
v___y_748_ = v___y_901_;
v___y_749_ = v___y_902_;
v___y_750_ = v___y_903_;
v___y_751_ = v___y_904_;
goto v___jp_743_;
}
else
{
lean_object* v___x_905_; lean_object* v_options_906_; uint8_t v_hasTrace_907_; 
v___x_905_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_options_906_ = lean_ctor_get(v___y_903_, 2);
v_hasTrace_907_ = lean_ctor_get_uint8(v_options_906_, sizeof(void*)*1);
if (v_hasTrace_907_ == 0)
{
lean_object* v_run_x27_908_; lean_object* v___x_909_; 
v_run_x27_908_ = lean_ctor_get(v___x_905_, 1);
lean_inc_ref(v_run_x27_908_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
v___x_909_ = lean_apply_8(v_run_x27_908_, v_g_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, lean_box(0));
v___y_772_ = v___y_904_;
v___y_773_ = v___y_901_;
v___y_774_ = v___y_902_;
v___y_775_ = v___y_899_;
v___y_776_ = v___y_903_;
v___y_777_ = v___y_900_;
v___y_778_ = v___y_896_;
v___y_779_ = v___x_909_;
goto v___jp_771_;
}
else
{
lean_object* v_run_x27_910_; lean_object* v_inheritedTraceOptions_911_; lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_run_x27_910_ = lean_ctor_get(v___x_905_, 1);
v_inheritedTraceOptions_911_ = lean_ctor_get(v___y_903_, 13);
lean_inc(v_g_898_);
v___f_912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed), 10, 2);
lean_closure_set(v___f_912_, 0, v___x_905_);
lean_closure_set(v___f_912_, 1, v_g_898_);
v___x_913_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1));
v___x_914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
v___x_915_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_911_, v_options_906_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = l_Lean_trace_profiler;
v___x_917_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_906_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; 
lean_dec_ref(v___f_912_);
lean_inc_ref(v_run_x27_910_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
v___x_918_ = lean_apply_8(v_run_x27_910_, v_g_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, lean_box(0));
v___y_772_ = v___y_904_;
v___y_773_ = v___y_901_;
v___y_774_ = v___y_902_;
v___y_775_ = v___y_899_;
v___y_776_ = v___y_903_;
v___y_777_ = v___y_900_;
v___y_778_ = v___y_896_;
v___y_779_ = v___x_918_;
goto v___jp_771_;
}
else
{
lean_inc_ref(v_run_x27_910_);
v___y_841_ = v___x_915_;
v___y_842_ = v___y_901_;
v___y_843_ = v_g_898_;
v___y_844_ = v___x_913_;
v___y_845_ = v_run_x27_910_;
v___y_846_ = v_options_906_;
v___y_847_ = v___y_896_;
v___y_848_ = v_hasTrace_907_;
v___y_849_ = v___y_904_;
v___y_850_ = v___y_902_;
v___y_851_ = v___y_899_;
v___y_852_ = v___f_912_;
v___y_853_ = v___y_900_;
v___y_854_ = v___y_903_;
goto v___jp_840_;
}
}
else
{
lean_inc_ref(v_run_x27_910_);
v___y_841_ = v___x_915_;
v___y_842_ = v___y_901_;
v___y_843_ = v_g_898_;
v___y_844_ = v___x_913_;
v___y_845_ = v_run_x27_910_;
v___y_846_ = v_options_906_;
v___y_847_ = v___y_896_;
v___y_848_ = v_hasTrace_907_;
v___y_849_ = v___y_904_;
v___y_850_ = v___y_902_;
v___y_851_ = v___y_899_;
v___y_852_ = v___f_912_;
v___y_853_ = v___y_900_;
v___y_854_ = v___y_903_;
goto v___jp_840_;
}
}
}
}
v___jp_919_:
{
if (lean_obj_tag(v___y_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_937_; 
v_a_928_ = lean_ctor_get(v___y_927_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___y_927_);
if (v_isSharedCheck_937_ == 0)
{
v___x_930_ = v___y_927_;
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___y_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
if (lean_obj_tag(v_a_928_) == 1)
{
lean_object* v_val_932_; uint8_t v_fixedInt_933_; 
lean_del_object(v___x_930_);
v_val_932_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v_a_928_, 1);
v_fixedInt_933_ = lean_ctor_get_uint8(v___y_926_, sizeof(void*)*2 + 6);
v___y_896_ = v___y_926_;
v_fixedInt_897_ = v_fixedInt_933_;
v_g_898_ = v_val_932_;
v___y_899_ = v___y_922_;
v___y_900_ = v___y_924_;
v___y_901_ = v___y_923_;
v___y_902_ = v___y_920_;
v___y_903_ = v___y_925_;
v___y_904_ = v___y_921_;
goto v___jp_895_;
}
else
{
lean_object* v___x_935_; 
lean_dec(v_a_928_);
lean_del_object(v___x_598_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_589_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_589_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_del_object(v___x_598_);
return v___y_927_;
}
}
v___jp_938_:
{
lean_object* v___x_954_; double v___x_955_; double v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_954_ = lean_io_get_num_heartbeats();
v___x_955_ = lean_float_of_nat(v___y_951_);
v___x_956_ = lean_float_of_nat(v___x_954_);
v___x_957_ = lean_box_float(v___x_955_);
v___x_958_ = lean_box_float(v___x_956_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_a_953_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
lean_inc_ref(v___y_948_);
v___x_961_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_944_, v___y_948_, v___y_943_, v___y_952_, v___y_949_, v___y_942_, v___x_960_, v___y_940_, v___y_950_, v___y_941_, v___y_947_, v___y_945_, v___y_939_);
v___y_920_ = v___y_947_;
v___y_921_ = v___y_939_;
v___y_922_ = v___y_940_;
v___y_923_ = v___y_941_;
v___y_924_ = v___y_950_;
v___y_925_ = v___y_945_;
v___y_926_ = v___y_946_;
v___y_927_ = v___x_961_;
goto v___jp_919_;
}
v___jp_962_:
{
lean_object* v___x_978_; double v___x_979_; double v___x_980_; double v___x_981_; double v___x_982_; double v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_978_ = lean_io_mono_nanos_now();
v___x_979_ = lean_float_of_nat(v___y_966_);
v___x_980_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
v___x_981_ = lean_float_div(v___x_979_, v___x_980_);
v___x_982_ = lean_float_of_nat(v___x_978_);
v___x_983_ = lean_float_div(v___x_982_, v___x_980_);
v___x_984_ = lean_box_float(v___x_981_);
v___x_985_ = lean_box_float(v___x_983_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_a_977_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_inc_ref(v___y_973_);
v___x_988_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_969_, v___y_973_, v___y_968_, v___y_976_, v___y_974_, v___y_967_, v___x_987_, v___y_964_, v___y_975_, v___y_965_, v___y_972_, v___y_970_, v___y_963_);
v___y_920_ = v___y_972_;
v___y_921_ = v___y_963_;
v___y_922_ = v___y_964_;
v___y_923_ = v___y_965_;
v___y_924_ = v___y_975_;
v___y_925_ = v___y_970_;
v___y_926_ = v___y_971_;
v___y_927_ = v___x_988_;
goto v___jp_919_;
}
v___jp_989_:
{
lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1004_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_990_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1007_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_995_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_io_mono_nanos_now();
lean_inc(v___y_990_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_993_);
lean_inc(v___y_1001_);
lean_inc_ref(v___y_991_);
v___x_1009_ = lean_apply_8(v___y_992_, v___y_1003_, v___y_991_, v___y_1001_, v___y_993_, v___y_999_, v___y_997_, v___y_990_, lean_box(0));
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set_tag(v___x_1012_, 1);
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v___y_963_ = v___y_990_;
v___y_964_ = v___y_991_;
v___y_965_ = v___y_993_;
v___y_966_ = v___x_1008_;
v___y_967_ = v___y_994_;
v___y_968_ = v___y_995_;
v___y_969_ = v___y_996_;
v___y_970_ = v___y_997_;
v___y_971_ = v___y_998_;
v___y_972_ = v___y_999_;
v___y_973_ = v___y_1000_;
v___y_974_ = v_a_1005_;
v___y_975_ = v___y_1001_;
v___y_976_ = v___y_1002_;
v_a_977_ = v___x_1015_;
goto v___jp_962_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1009_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1009_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 0);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v___y_963_ = v___y_990_;
v___y_964_ = v___y_991_;
v___y_965_ = v___y_993_;
v___y_966_ = v___x_1008_;
v___y_967_ = v___y_994_;
v___y_968_ = v___y_995_;
v___y_969_ = v___y_996_;
v___y_970_ = v___y_997_;
v___y_971_ = v___y_998_;
v___y_972_ = v___y_999_;
v___y_973_ = v___y_1000_;
v___y_974_ = v_a_1005_;
v___y_975_ = v___y_1001_;
v___y_976_ = v___y_1002_;
v_a_977_ = v___x_1023_;
goto v___jp_962_;
}
}
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_io_get_num_heartbeats();
lean_inc(v___y_990_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_993_);
lean_inc(v___y_1001_);
lean_inc_ref(v___y_991_);
v___x_1027_ = lean_apply_8(v___y_992_, v___y_1003_, v___y_991_, v___y_1001_, v___y_993_, v___y_999_, v___y_997_, v___y_990_, lean_box(0));
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 1);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
v___y_939_ = v___y_990_;
v___y_940_ = v___y_991_;
v___y_941_ = v___y_993_;
v___y_942_ = v___y_994_;
v___y_943_ = v___y_995_;
v___y_944_ = v___y_996_;
v___y_945_ = v___y_997_;
v___y_946_ = v___y_998_;
v___y_947_ = v___y_999_;
v___y_948_ = v___y_1000_;
v___y_949_ = v_a_1005_;
v___y_950_ = v___y_1001_;
v___y_951_ = v___x_1026_;
v___y_952_ = v___y_1002_;
v_a_953_ = v___x_1033_;
goto v___jp_938_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1027_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 0);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
v___y_939_ = v___y_990_;
v___y_940_ = v___y_991_;
v___y_941_ = v___y_993_;
v___y_942_ = v___y_994_;
v___y_943_ = v___y_995_;
v___y_944_ = v___y_996_;
v___y_945_ = v___y_997_;
v___y_946_ = v___y_998_;
v___y_947_ = v___y_999_;
v___y_948_ = v___y_1000_;
v___y_949_ = v_a_1005_;
v___y_950_ = v___y_1001_;
v___y_951_ = v___x_1026_;
v___y_952_ = v___y_1002_;
v_a_953_ = v___x_1041_;
goto v___jp_938_;
}
}
}
}
}
v___jp_1044_:
{
if (v_enums_1047_ == 0)
{
v___y_896_ = v___y_1045_;
v_fixedInt_897_ = v_fixedInt_1046_;
v_g_898_ = v_g_1048_;
v___y_899_ = v___y_1049_;
v___y_900_ = v___y_1050_;
v___y_901_ = v___y_1051_;
v___y_902_ = v___y_1052_;
v___y_903_ = v___y_1053_;
v___y_904_ = v___y_1054_;
goto v___jp_895_;
}
else
{
lean_object* v___x_1055_; lean_object* v_options_1056_; uint8_t v_hasTrace_1057_; 
v___x_1055_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_options_1056_ = lean_ctor_get(v___y_1053_, 2);
v_hasTrace_1057_ = lean_ctor_get_uint8(v_options_1056_, sizeof(void*)*1);
if (v_hasTrace_1057_ == 0)
{
lean_object* v_run_x27_1058_; lean_object* v___x_1059_; 
v_run_x27_1058_ = lean_ctor_get(v___x_1055_, 1);
lean_inc_ref(v_run_x27_1058_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
v___x_1059_ = lean_apply_8(v_run_x27_1058_, v_g_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, lean_box(0));
v___y_920_ = v___y_1052_;
v___y_921_ = v___y_1054_;
v___y_922_ = v___y_1049_;
v___y_923_ = v___y_1051_;
v___y_924_ = v___y_1050_;
v___y_925_ = v___y_1053_;
v___y_926_ = v___y_1045_;
v___y_927_ = v___x_1059_;
goto v___jp_919_;
}
else
{
lean_object* v_run_x27_1060_; lean_object* v_inheritedTraceOptions_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_run_x27_1060_ = lean_ctor_get(v___x_1055_, 1);
v_inheritedTraceOptions_1061_ = lean_ctor_get(v___y_1053_, 13);
lean_inc(v_g_1048_);
v___f_1062_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__1___boxed), 10, 2);
lean_closure_set(v___f_1062_, 0, v___x_1055_);
lean_closure_set(v___f_1062_, 1, v_g_1048_);
v___x_1063_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1));
v___x_1064_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
v___x_1065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1061_, v_options_1056_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = l_Lean_trace_profiler;
v___x_1067_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_1056_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
lean_dec_ref(v___f_1062_);
lean_inc_ref(v_run_x27_1060_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
v___x_1068_ = lean_apply_8(v_run_x27_1060_, v_g_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, lean_box(0));
v___y_920_ = v___y_1052_;
v___y_921_ = v___y_1054_;
v___y_922_ = v___y_1049_;
v___y_923_ = v___y_1051_;
v___y_924_ = v___y_1050_;
v___y_925_ = v___y_1053_;
v___y_926_ = v___y_1045_;
v___y_927_ = v___x_1068_;
goto v___jp_919_;
}
else
{
lean_inc_ref(v_run_x27_1060_);
v___y_990_ = v___y_1054_;
v___y_991_ = v___y_1049_;
v___y_992_ = v_run_x27_1060_;
v___y_993_ = v___y_1051_;
v___y_994_ = v___f_1062_;
v___y_995_ = v_options_1056_;
v___y_996_ = v_hasTrace_1057_;
v___y_997_ = v___y_1053_;
v___y_998_ = v___y_1045_;
v___y_999_ = v___y_1052_;
v___y_1000_ = v___x_1063_;
v___y_1001_ = v___y_1050_;
v___y_1002_ = v___x_1065_;
v___y_1003_ = v_g_1048_;
goto v___jp_989_;
}
}
else
{
lean_inc_ref(v_run_x27_1060_);
v___y_990_ = v___y_1054_;
v___y_991_ = v___y_1049_;
v___y_992_ = v_run_x27_1060_;
v___y_993_ = v___y_1051_;
v___y_994_ = v___f_1062_;
v___y_995_ = v_options_1056_;
v___y_996_ = v_hasTrace_1057_;
v___y_997_ = v___y_1053_;
v___y_998_ = v___y_1045_;
v___y_999_ = v___y_1052_;
v___y_1000_ = v___x_1063_;
v___y_1001_ = v___y_1050_;
v___y_1002_ = v___x_1065_;
v___y_1003_ = v_g_1048_;
goto v___jp_989_;
}
}
}
}
v___jp_1069_:
{
if (lean_obj_tag(v___y_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1088_; 
v_a_1078_ = lean_ctor_get(v___y_1077_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___y_1077_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1080_ = v___y_1077_;
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___y_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
if (lean_obj_tag(v_a_1078_) == 1)
{
lean_object* v_val_1082_; uint8_t v_fixedInt_1083_; uint8_t v_enums_1084_; 
lean_del_object(v___x_1080_);
v_val_1082_ = lean_ctor_get(v_a_1078_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v_a_1078_, 1);
v_fixedInt_1083_ = lean_ctor_get_uint8(v___y_1075_, sizeof(void*)*2 + 6);
v_enums_1084_ = lean_ctor_get_uint8(v___y_1075_, sizeof(void*)*2 + 7);
v___y_1045_ = v___y_1075_;
v_fixedInt_1046_ = v_fixedInt_1083_;
v_enums_1047_ = v_enums_1084_;
v_g_1048_ = v_val_1082_;
v___y_1049_ = v___y_1072_;
v___y_1050_ = v___y_1074_;
v___y_1051_ = v___y_1073_;
v___y_1052_ = v___y_1076_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___y_1070_;
goto v___jp_1044_;
}
else
{
lean_object* v___x_1086_; 
lean_dec(v_a_1078_);
lean_del_object(v___x_598_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_589_);
v___x_1086_ = v___x_1080_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_589_);
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
lean_del_object(v___x_598_);
return v___y_1077_;
}
}
v___jp_1089_:
{
lean_object* v___x_1105_; double v___x_1106_; double v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1105_ = lean_io_get_num_heartbeats();
v___x_1106_ = lean_float_of_nat(v___y_1094_);
v___x_1107_ = lean_float_of_nat(v___x_1105_);
v___x_1108_ = lean_box_float(v___x_1106_);
v___x_1109_ = lean_box_float(v___x_1107_);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v_a_1104_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
lean_inc_ref(v___y_1090_);
v___x_1112_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_1092_, v___y_1090_, v___y_1103_, v___y_1099_, v___y_1102_, v___y_1091_, v___x_1111_, v___y_1093_, v___y_1095_, v___y_1096_, v___y_1098_, v___y_1100_, v___y_1101_);
v___y_1070_ = v___y_1101_;
v___y_1071_ = v___y_1100_;
v___y_1072_ = v___y_1093_;
v___y_1073_ = v___y_1096_;
v___y_1074_ = v___y_1095_;
v___y_1075_ = v___y_1097_;
v___y_1076_ = v___y_1098_;
v___y_1077_ = v___x_1112_;
goto v___jp_1069_;
}
v___jp_1113_:
{
lean_object* v___x_1129_; double v___x_1130_; double v___x_1131_; double v___x_1132_; double v___x_1133_; double v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1129_ = lean_io_mono_nanos_now();
v___x_1130_ = lean_float_of_nat(v___y_1121_);
v___x_1131_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
v___x_1132_ = lean_float_div(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_float_of_nat(v___x_1129_);
v___x_1134_ = lean_float_div(v___x_1133_, v___x_1131_);
v___x_1135_ = lean_box_float(v___x_1132_);
v___x_1136_ = lean_box_float(v___x_1134_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_a_1128_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
lean_inc_ref(v___y_1114_);
v___x_1139_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_1116_, v___y_1114_, v___y_1127_, v___y_1123_, v___y_1126_, v___y_1115_, v___x_1138_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1122_, v___y_1124_, v___y_1125_);
v___y_1070_ = v___y_1125_;
v___y_1071_ = v___y_1124_;
v___y_1072_ = v___y_1117_;
v___y_1073_ = v___y_1119_;
v___y_1074_ = v___y_1118_;
v___y_1075_ = v___y_1120_;
v___y_1076_ = v___y_1122_;
v___y_1077_ = v___x_1139_;
goto v___jp_1069_;
}
v___jp_1140_:
{
lean_object* v___x_1155_; lean_object* v_a_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1155_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_1152_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v___x_1155_);
v___x_1157_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1158_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_1154_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_io_mono_nanos_now();
lean_inc(v___y_1152_);
lean_inc_ref(v___y_1151_);
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
lean_inc(v___y_1147_);
lean_inc_ref(v___y_1144_);
v___x_1160_ = lean_apply_8(v___y_1145_, v___y_1146_, v___y_1144_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1151_, v___y_1152_, lean_box(0));
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set_tag(v___x_1163_, 1);
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
v___y_1114_ = v___y_1141_;
v___y_1115_ = v___y_1142_;
v___y_1116_ = v___y_1143_;
v___y_1117_ = v___y_1144_;
v___y_1118_ = v___y_1147_;
v___y_1119_ = v___y_1148_;
v___y_1120_ = v___y_1150_;
v___y_1121_ = v___x_1159_;
v___y_1122_ = v___y_1149_;
v___y_1123_ = v___y_1153_;
v___y_1124_ = v___y_1151_;
v___y_1125_ = v___y_1152_;
v___y_1126_ = v_a_1156_;
v___y_1127_ = v___y_1154_;
v_a_1128_ = v___x_1166_;
goto v___jp_1113_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_a_1169_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1160_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1160_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 0);
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
v___y_1114_ = v___y_1141_;
v___y_1115_ = v___y_1142_;
v___y_1116_ = v___y_1143_;
v___y_1117_ = v___y_1144_;
v___y_1118_ = v___y_1147_;
v___y_1119_ = v___y_1148_;
v___y_1120_ = v___y_1150_;
v___y_1121_ = v___x_1159_;
v___y_1122_ = v___y_1149_;
v___y_1123_ = v___y_1153_;
v___y_1124_ = v___y_1151_;
v___y_1125_ = v___y_1152_;
v___y_1126_ = v_a_1156_;
v___y_1127_ = v___y_1154_;
v_a_1128_ = v___x_1174_;
goto v___jp_1113_;
}
}
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1152_);
lean_inc_ref(v___y_1151_);
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
lean_inc(v___y_1147_);
lean_inc_ref(v___y_1144_);
v___x_1178_ = lean_apply_8(v___y_1145_, v___y_1146_, v___y_1144_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1151_, v___y_1152_, lean_box(0));
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 1);
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
v___y_1090_ = v___y_1141_;
v___y_1091_ = v___y_1142_;
v___y_1092_ = v___y_1143_;
v___y_1093_ = v___y_1144_;
v___y_1094_ = v___x_1177_;
v___y_1095_ = v___y_1147_;
v___y_1096_ = v___y_1148_;
v___y_1097_ = v___y_1150_;
v___y_1098_ = v___y_1149_;
v___y_1099_ = v___y_1153_;
v___y_1100_ = v___y_1151_;
v___y_1101_ = v___y_1152_;
v___y_1102_ = v_a_1156_;
v___y_1103_ = v___y_1154_;
v_a_1104_ = v___x_1184_;
goto v___jp_1089_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_a_1187_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1178_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1178_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 0);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
v___y_1090_ = v___y_1141_;
v___y_1091_ = v___y_1142_;
v___y_1092_ = v___y_1143_;
v___y_1093_ = v___y_1144_;
v___y_1094_ = v___x_1177_;
v___y_1095_ = v___y_1147_;
v___y_1096_ = v___y_1148_;
v___y_1097_ = v___y_1150_;
v___y_1098_ = v___y_1149_;
v___y_1099_ = v___y_1153_;
v___y_1100_ = v___y_1151_;
v___y_1101_ = v___y_1152_;
v___y_1102_ = v_a_1156_;
v___y_1103_ = v___y_1154_;
v_a_1104_ = v___x_1192_;
goto v___jp_1089_;
}
}
}
}
}
v___jp_1195_:
{
if (lean_obj_tag(v___y_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1229_; 
v_a_1203_ = lean_ctor_get(v___y_1202_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___y_1202_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1205_ = v___y_1202_;
v_isShared_1206_ = v_isSharedCheck_1229_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___y_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1229_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
if (lean_obj_tag(v_a_1203_) == 1)
{
uint8_t v_structures_1207_; 
lean_del_object(v___x_1205_);
v_structures_1207_ = lean_ctor_get_uint8(v___y_1201_, sizeof(void*)*2 + 5);
if (v_structures_1207_ == 0)
{
lean_object* v_val_1208_; uint8_t v_fixedInt_1209_; uint8_t v_enums_1210_; 
v_val_1208_ = lean_ctor_get(v_a_1203_, 0);
lean_inc(v_val_1208_);
lean_dec_ref_known(v_a_1203_, 1);
v_fixedInt_1209_ = lean_ctor_get_uint8(v___y_1201_, sizeof(void*)*2 + 6);
v_enums_1210_ = lean_ctor_get_uint8(v___y_1201_, sizeof(void*)*2 + 7);
v___y_1045_ = v___y_1201_;
v_fixedInt_1046_ = v_fixedInt_1209_;
v_enums_1047_ = v_enums_1210_;
v_g_1048_ = v_val_1208_;
v___y_1049_ = v___y_1201_;
v___y_1050_ = v___y_1200_;
v___y_1051_ = v___y_1199_;
v___y_1052_ = v___y_1196_;
v___y_1053_ = v___y_1198_;
v___y_1054_ = v___y_1197_;
goto v___jp_1044_;
}
else
{
lean_object* v_val_1211_; lean_object* v___x_1212_; lean_object* v_options_1213_; uint8_t v_hasTrace_1214_; 
v_val_1211_ = lean_ctor_get(v_a_1203_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_a_1203_, 1);
v___x_1212_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_options_1213_ = lean_ctor_get(v___y_1198_, 2);
v_hasTrace_1214_ = lean_ctor_get_uint8(v_options_1213_, sizeof(void*)*1);
if (v_hasTrace_1214_ == 0)
{
lean_object* v_run_x27_1215_; lean_object* v___x_1216_; 
v_run_x27_1215_ = lean_ctor_get(v___x_1212_, 1);
lean_inc_ref(v_run_x27_1215_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1199_);
lean_inc(v___y_1200_);
lean_inc_ref(v___y_1201_);
v___x_1216_ = lean_apply_8(v_run_x27_1215_, v_val_1211_, v___y_1201_, v___y_1200_, v___y_1199_, v___y_1196_, v___y_1198_, v___y_1197_, lean_box(0));
v___y_1070_ = v___y_1197_;
v___y_1071_ = v___y_1198_;
v___y_1072_ = v___y_1201_;
v___y_1073_ = v___y_1199_;
v___y_1074_ = v___y_1200_;
v___y_1075_ = v___y_1201_;
v___y_1076_ = v___y_1196_;
v___y_1077_ = v___x_1216_;
goto v___jp_1069_;
}
else
{
lean_object* v_run_x27_1217_; lean_object* v_inheritedTraceOptions_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_run_x27_1217_ = lean_ctor_get(v___x_1212_, 1);
v_inheritedTraceOptions_1218_ = lean_ctor_get(v___y_1198_, 13);
lean_inc(v_val_1211_);
v___f_1219_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1219_, 0, v___x_1212_);
lean_closure_set(v___f_1219_, 1, v_val_1211_);
v___x_1220_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1));
v___x_1221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
v___x_1222_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1218_, v_options_1213_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = l_Lean_trace_profiler;
v___x_1224_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_1213_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v___f_1219_);
lean_inc_ref(v_run_x27_1217_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1199_);
lean_inc(v___y_1200_);
lean_inc_ref(v___y_1201_);
v___x_1225_ = lean_apply_8(v_run_x27_1217_, v_val_1211_, v___y_1201_, v___y_1200_, v___y_1199_, v___y_1196_, v___y_1198_, v___y_1197_, lean_box(0));
v___y_1070_ = v___y_1197_;
v___y_1071_ = v___y_1198_;
v___y_1072_ = v___y_1201_;
v___y_1073_ = v___y_1199_;
v___y_1074_ = v___y_1200_;
v___y_1075_ = v___y_1201_;
v___y_1076_ = v___y_1196_;
v___y_1077_ = v___x_1225_;
goto v___jp_1069_;
}
else
{
lean_inc_ref(v_run_x27_1217_);
v___y_1141_ = v___x_1220_;
v___y_1142_ = v___f_1219_;
v___y_1143_ = v_hasTrace_1214_;
v___y_1144_ = v___y_1201_;
v___y_1145_ = v_run_x27_1217_;
v___y_1146_ = v_val_1211_;
v___y_1147_ = v___y_1200_;
v___y_1148_ = v___y_1199_;
v___y_1149_ = v___y_1196_;
v___y_1150_ = v___y_1201_;
v___y_1151_ = v___y_1198_;
v___y_1152_ = v___y_1197_;
v___y_1153_ = v___x_1222_;
v___y_1154_ = v_options_1213_;
goto v___jp_1140_;
}
}
else
{
lean_inc_ref(v_run_x27_1217_);
v___y_1141_ = v___x_1220_;
v___y_1142_ = v___f_1219_;
v___y_1143_ = v_hasTrace_1214_;
v___y_1144_ = v___y_1201_;
v___y_1145_ = v_run_x27_1217_;
v___y_1146_ = v_val_1211_;
v___y_1147_ = v___y_1200_;
v___y_1148_ = v___y_1199_;
v___y_1149_ = v___y_1196_;
v___y_1150_ = v___y_1201_;
v___y_1151_ = v___y_1198_;
v___y_1152_ = v___y_1197_;
v___y_1153_ = v___x_1222_;
v___y_1154_ = v_options_1213_;
goto v___jp_1140_;
}
}
}
}
else
{
lean_object* v___x_1227_; 
lean_dec(v_a_1203_);
lean_del_object(v___x_598_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_589_);
v___x_1227_ = v___x_1205_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_589_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_del_object(v___x_598_);
return v___y_1202_;
}
}
v___jp_1230_:
{
lean_object* v___x_1245_; double v___x_1246_; double v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1245_ = lean_io_get_num_heartbeats();
v___x_1246_ = lean_float_of_nat(v___y_1237_);
v___x_1247_ = lean_float_of_nat(v___x_1245_);
v___x_1248_ = lean_box_float(v___x_1246_);
v___x_1249_ = lean_box_float(v___x_1247_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_a_1244_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
lean_inc_ref(v___y_1234_);
v___x_1252_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_1235_, v___y_1234_, v___y_1236_, v___y_1242_, v___y_1239_, v___y_1243_, v___x_1251_, v___y_1238_, v___y_1241_, v___y_1240_, v___y_1231_, v___y_1233_, v___y_1232_);
v___y_1196_ = v___y_1231_;
v___y_1197_ = v___y_1232_;
v___y_1198_ = v___y_1233_;
v___y_1199_ = v___y_1240_;
v___y_1200_ = v___y_1241_;
v___y_1201_ = v___y_1238_;
v___y_1202_ = v___x_1252_;
goto v___jp_1195_;
}
v___jp_1253_:
{
lean_object* v___x_1268_; double v___x_1269_; double v___x_1270_; double v___x_1271_; double v___x_1272_; double v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1268_ = lean_io_mono_nanos_now();
v___x_1269_ = lean_float_of_nat(v___y_1261_);
v___x_1270_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
v___x_1271_ = lean_float_div(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_float_of_nat(v___x_1268_);
v___x_1273_ = lean_float_div(v___x_1272_, v___x_1270_);
v___x_1274_ = lean_box_float(v___x_1271_);
v___x_1275_ = lean_box_float(v___x_1273_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v_a_1267_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
lean_inc_ref(v___y_1257_);
v___x_1278_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2(v___x_602_, v___y_1258_, v___y_1257_, v___y_1259_, v___y_1265_, v___y_1262_, v___y_1266_, v___x_1277_, v___y_1260_, v___y_1264_, v___y_1263_, v___y_1254_, v___y_1256_, v___y_1255_);
v___y_1196_ = v___y_1254_;
v___y_1197_ = v___y_1255_;
v___y_1198_ = v___y_1256_;
v___y_1199_ = v___y_1263_;
v___y_1200_ = v___y_1264_;
v___y_1201_ = v___y_1260_;
v___y_1202_ = v___x_1278_;
goto v___jp_1195_;
}
v___jp_1279_:
{
lean_object* v___x_1292_; lean_object* v_a_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1292_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg(v___y_1281_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1295_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v___y_1284_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_io_mono_nanos_now();
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1287_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1286_);
v___x_1297_ = lean_apply_8(v___y_1288_, v_val_596_, v___y_1286_, v___y_1289_, v___y_1287_, v___y_1280_, v___y_1282_, v___y_1281_, lean_box(0));
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 1);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
v___y_1254_ = v___y_1280_;
v___y_1255_ = v___y_1281_;
v___y_1256_ = v___y_1282_;
v___y_1257_ = v___y_1283_;
v___y_1258_ = v___y_1285_;
v___y_1259_ = v___y_1284_;
v___y_1260_ = v___y_1286_;
v___y_1261_ = v___x_1296_;
v___y_1262_ = v_a_1293_;
v___y_1263_ = v___y_1287_;
v___y_1264_ = v___y_1289_;
v___y_1265_ = v___y_1290_;
v___y_1266_ = v___y_1291_;
v_a_1267_ = v___x_1303_;
goto v___jp_1253_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_a_1306_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1297_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1297_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set_tag(v___x_1308_, 0);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
v___y_1254_ = v___y_1280_;
v___y_1255_ = v___y_1281_;
v___y_1256_ = v___y_1282_;
v___y_1257_ = v___y_1283_;
v___y_1258_ = v___y_1285_;
v___y_1259_ = v___y_1284_;
v___y_1260_ = v___y_1286_;
v___y_1261_ = v___x_1296_;
v___y_1262_ = v_a_1293_;
v___y_1263_ = v___y_1287_;
v___y_1264_ = v___y_1289_;
v___y_1265_ = v___y_1290_;
v___y_1266_ = v___y_1291_;
v_a_1267_ = v___x_1311_;
goto v___jp_1253_;
}
}
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1287_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1286_);
v___x_1315_ = lean_apply_8(v___y_1288_, v_val_596_, v___y_1286_, v___y_1289_, v___y_1287_, v___y_1280_, v___y_1282_, v___y_1281_, lean_box(0));
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 1);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
v___y_1231_ = v___y_1280_;
v___y_1232_ = v___y_1281_;
v___y_1233_ = v___y_1282_;
v___y_1234_ = v___y_1283_;
v___y_1235_ = v___y_1285_;
v___y_1236_ = v___y_1284_;
v___y_1237_ = v___x_1314_;
v___y_1238_ = v___y_1286_;
v___y_1239_ = v_a_1293_;
v___y_1240_ = v___y_1287_;
v___y_1241_ = v___y_1289_;
v___y_1242_ = v___y_1290_;
v___y_1243_ = v___y_1291_;
v_a_1244_ = v___x_1321_;
goto v___jp_1230_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_a_1324_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1315_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1315_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 0);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v___y_1231_ = v___y_1280_;
v___y_1232_ = v___y_1281_;
v___y_1233_ = v___y_1282_;
v___y_1234_ = v___y_1283_;
v___y_1235_ = v___y_1285_;
v___y_1236_ = v___y_1284_;
v___y_1237_ = v___x_1314_;
v___y_1238_ = v___y_1286_;
v___y_1239_ = v_a_1293_;
v___y_1240_ = v___y_1287_;
v___y_1241_ = v___y_1289_;
v___y_1242_ = v___y_1290_;
v___y_1243_ = v___y_1291_;
v_a_1244_ = v___x_1329_;
goto v___jp_1230_;
}
}
}
}
}
v___jp_1332_:
{
lean_object* v___x_1339_; lean_object* v_options_1340_; uint8_t v_hasTrace_1341_; 
v___x_1339_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_options_1340_ = lean_ctor_get(v___y_1335_, 2);
v_hasTrace_1341_ = lean_ctor_get_uint8(v_options_1340_, sizeof(void*)*1);
if (v_hasTrace_1341_ == 0)
{
lean_object* v_run_x27_1342_; lean_object* v___x_1343_; 
v_run_x27_1342_ = lean_ctor_get(v___x_1339_, 1);
lean_inc_ref(v_run_x27_1342_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1338_);
v___x_1343_ = lean_apply_8(v_run_x27_1342_, v_val_596_, v___y_1338_, v___y_1337_, v___y_1336_, v___y_1333_, v___y_1335_, v___y_1334_, lean_box(0));
v___y_1196_ = v___y_1333_;
v___y_1197_ = v___y_1334_;
v___y_1198_ = v___y_1335_;
v___y_1199_ = v___y_1336_;
v___y_1200_ = v___y_1337_;
v___y_1201_ = v___y_1338_;
v___y_1202_ = v___x_1343_;
goto v___jp_1195_;
}
else
{
lean_object* v_run_x27_1344_; lean_object* v_inheritedTraceOptions_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_run_x27_1344_ = lean_ctor_get(v___x_1339_, 1);
v_inheritedTraceOptions_1345_ = lean_ctor_get(v___y_1335_, 13);
lean_inc(v_val_596_);
v___f_1346_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1346_, 0, v___x_1339_);
lean_closure_set(v___f_1346_, 1, v_val_596_);
v___x_1347_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1));
v___x_1348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
v___x_1349_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1345_, v_options_1340_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = l_Lean_trace_profiler;
v___x_1351_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_1340_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec_ref(v___f_1346_);
lean_inc_ref(v_run_x27_1344_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1338_);
v___x_1352_ = lean_apply_8(v_run_x27_1344_, v_val_596_, v___y_1338_, v___y_1337_, v___y_1336_, v___y_1333_, v___y_1335_, v___y_1334_, lean_box(0));
v___y_1196_ = v___y_1333_;
v___y_1197_ = v___y_1334_;
v___y_1198_ = v___y_1335_;
v___y_1199_ = v___y_1336_;
v___y_1200_ = v___y_1337_;
v___y_1201_ = v___y_1338_;
v___y_1202_ = v___x_1352_;
goto v___jp_1195_;
}
else
{
lean_inc_ref(v_run_x27_1344_);
v___y_1280_ = v___y_1333_;
v___y_1281_ = v___y_1334_;
v___y_1282_ = v___y_1335_;
v___y_1283_ = v___x_1347_;
v___y_1284_ = v_options_1340_;
v___y_1285_ = v_hasTrace_1341_;
v___y_1286_ = v___y_1338_;
v___y_1287_ = v___y_1336_;
v___y_1288_ = v_run_x27_1344_;
v___y_1289_ = v___y_1337_;
v___y_1290_ = v___x_1349_;
v___y_1291_ = v___f_1346_;
goto v___jp_1279_;
}
}
else
{
lean_inc_ref(v_run_x27_1344_);
v___y_1280_ = v___y_1333_;
v___y_1281_ = v___y_1334_;
v___y_1282_ = v___y_1335_;
v___y_1283_ = v___x_1347_;
v___y_1284_ = v_options_1340_;
v___y_1285_ = v_hasTrace_1341_;
v___y_1286_ = v___y_1338_;
v___y_1287_ = v___y_1336_;
v___y_1288_ = v_run_x27_1344_;
v___y_1289_ = v___y_1337_;
v___y_1290_ = v___x_1349_;
v___y_1291_ = v___f_1346_;
goto v___jp_1279_;
}
}
}
v___jp_1353_:
{
uint8_t v_structures_1360_; 
v_structures_1360_ = lean_ctor_get_uint8(v___y_1354_, sizeof(void*)*2 + 5);
if (v_structures_1360_ == 0)
{
uint8_t v_enums_1361_; 
v_enums_1361_ = lean_ctor_get_uint8(v___y_1354_, sizeof(void*)*2 + 7);
if (v_enums_1361_ == 0)
{
uint8_t v_fixedInt_1362_; 
v_fixedInt_1362_ = lean_ctor_get_uint8(v___y_1354_, sizeof(void*)*2 + 6);
v___y_896_ = v___y_1354_;
v_fixedInt_897_ = v_fixedInt_1362_;
v_g_898_ = v_val_596_;
v___y_899_ = v___y_1354_;
v___y_900_ = v___y_1355_;
v___y_901_ = v___y_1356_;
v___y_902_ = v___y_1357_;
v___y_903_ = v___y_1358_;
v___y_904_ = v___y_1359_;
goto v___jp_895_;
}
else
{
v___y_1333_ = v___y_1357_;
v___y_1334_ = v___y_1359_;
v___y_1335_ = v___y_1358_;
v___y_1336_ = v___y_1356_;
v___y_1337_ = v___y_1355_;
v___y_1338_ = v___y_1354_;
goto v___jp_1332_;
}
}
else
{
v___y_1333_ = v___y_1357_;
v___y_1334_ = v___y_1359_;
v___y_1335_ = v___y_1358_;
v___y_1336_ = v___y_1356_;
v___y_1337_ = v___y_1355_;
v___y_1338_ = v___y_1354_;
goto v___jp_1332_;
}
}
}
}
else
{
lean_object* v___x_1379_; 
lean_dec(v_a_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_589_);
v___x_1379_ = v___x_593_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_589_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___boxed(lean_object* v_g_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3(lean_object* v_00_u03b1_1391_, lean_object* v_x_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___redArg(v_x_1392_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__3(v_00_u03b1_1401_, v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3(lean_object* v_cls_1411_, lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg(v_cls_1411_, v_msg_1412_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___boxed(lean_object* v_cls_1421_, lean_object* v_msg_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3(v_cls_1421_, v_msg_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(lean_object* v_oldTraces_1431_, lean_object* v_data_1432_, lean_object* v_ref_1433_, lean_object* v_msg_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___redArg(v_oldTraces_1431_, v_data_1432_, v_ref_1433_, v_msg_1434_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2___boxed(lean_object* v_oldTraces_1443_, lean_object* v_data_1444_, lean_object* v_ref_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2(v_oldTraces_1443_, v_data_1444_, v_ref_1445_, v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(lean_object* v_mvarId_1455_, lean_object* v_x_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1455_, v_x_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1471_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1462_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1462_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_1479_, lean_object* v_x_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_mvarId_1479_, v_x_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(lean_object* v_00_u03b1_1487_, lean_object* v_mvarId_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_mvarId_1488_, v_x_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___boxed(lean_object* v_00_u03b1_1496_, lean_object* v_mvarId_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(v_00_u03b1_1496_, v_mvarId_1497_, v_x_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v_traceState_1508_; lean_object* v_traces_1509_; lean_object* v___x_1510_; lean_object* v_traceState_1511_; lean_object* v_env_1512_; lean_object* v_nextMacroScope_1513_; lean_object* v_ngen_1514_; lean_object* v_auxDeclNGen_1515_; lean_object* v_cache_1516_; lean_object* v_messages_1517_; lean_object* v_infoState_1518_; lean_object* v_snapshotTasks_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1540_; 
v___x_1507_ = lean_st_ref_get(v___y_1505_);
v_traceState_1508_ = lean_ctor_get(v___x_1507_, 4);
lean_inc_ref(v_traceState_1508_);
lean_dec(v___x_1507_);
v_traces_1509_ = lean_ctor_get(v_traceState_1508_, 0);
lean_inc_ref(v_traces_1509_);
lean_dec_ref(v_traceState_1508_);
v___x_1510_ = lean_st_ref_take(v___y_1505_);
v_traceState_1511_ = lean_ctor_get(v___x_1510_, 4);
v_env_1512_ = lean_ctor_get(v___x_1510_, 0);
v_nextMacroScope_1513_ = lean_ctor_get(v___x_1510_, 1);
v_ngen_1514_ = lean_ctor_get(v___x_1510_, 2);
v_auxDeclNGen_1515_ = lean_ctor_get(v___x_1510_, 3);
v_cache_1516_ = lean_ctor_get(v___x_1510_, 5);
v_messages_1517_ = lean_ctor_get(v___x_1510_, 6);
v_infoState_1518_ = lean_ctor_get(v___x_1510_, 7);
v_snapshotTasks_1519_ = lean_ctor_get(v___x_1510_, 8);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1521_ = v___x_1510_;
v_isShared_1522_ = v_isSharedCheck_1540_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snapshotTasks_1519_);
lean_inc(v_infoState_1518_);
lean_inc(v_messages_1517_);
lean_inc(v_cache_1516_);
lean_inc(v_traceState_1511_);
lean_inc(v_auxDeclNGen_1515_);
lean_inc(v_ngen_1514_);
lean_inc(v_nextMacroScope_1513_);
lean_inc(v_env_1512_);
lean_dec(v___x_1510_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1540_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
uint64_t v_tid_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1538_; 
v_tid_1523_ = lean_ctor_get_uint64(v_traceState_1511_, sizeof(void*)*1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_traceState_1511_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v_traceState_1511_, 0);
lean_dec(v_unused_1539_);
v___x_1525_ = v_traceState_1511_;
v_isShared_1526_ = v_isSharedCheck_1538_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v_traceState_1511_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1538_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1527_ = lean_unsigned_to_nat(32u);
v___x_1528_ = lean_mk_empty_array_with_capacity(v___x_1527_);
lean_dec_ref(v___x_1528_);
v___x_1529_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__0___redArg___closed__1);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1529_);
v___x_1531_ = v___x_1525_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1529_);
lean_ctor_set_uint64(v_reuseFailAlloc_1537_, sizeof(void*)*1, v_tid_1523_);
v___x_1531_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v___x_1531_);
v___x_1533_ = v___x_1521_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_env_1512_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_nextMacroScope_1513_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_ngen_1514_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_auxDeclNGen_1515_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1536_, 5, v_cache_1516_);
lean_ctor_set(v_reuseFailAlloc_1536_, 6, v_messages_1517_);
lean_ctor_set(v_reuseFailAlloc_1536_, 7, v_infoState_1518_);
lean_ctor_set(v_reuseFailAlloc_1536_, 8, v_snapshotTasks_1519_);
v___x_1533_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_st_ref_set(v___y_1505_, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_traces_1509_);
return v___x_1535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg___boxed(lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v___y_1541_);
lean_dec(v___y_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v___y_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___boxed(lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1555_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1));
v___x_1560_ = l_Lean_MessageData_ofFormat(v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__2);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(v_x_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec_ref(v_x_1569_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(lean_object* v_oldTraces_1576_, lean_object* v_data_1577_, lean_object* v_ref_1578_, lean_object* v_msg_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_fileName_1585_; lean_object* v_fileMap_1586_; lean_object* v_options_1587_; lean_object* v_currRecDepth_1588_; lean_object* v_maxRecDepth_1589_; lean_object* v_ref_1590_; lean_object* v_currNamespace_1591_; lean_object* v_openDecls_1592_; lean_object* v_initHeartbeats_1593_; lean_object* v_maxHeartbeats_1594_; lean_object* v_quotContext_1595_; lean_object* v_currMacroScope_1596_; uint8_t v_diag_1597_; lean_object* v_cancelTk_x3f_1598_; uint8_t v_suppressElabErrors_1599_; lean_object* v_inheritedTraceOptions_1600_; lean_object* v___x_1601_; lean_object* v_traceState_1602_; lean_object* v_traces_1603_; lean_object* v_ref_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; size_t v_sz_1607_; size_t v___x_1608_; lean_object* v___x_1609_; lean_object* v_msg_1610_; lean_object* v___x_1611_; lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1649_; 
v_fileName_1585_ = lean_ctor_get(v___y_1582_, 0);
v_fileMap_1586_ = lean_ctor_get(v___y_1582_, 1);
v_options_1587_ = lean_ctor_get(v___y_1582_, 2);
v_currRecDepth_1588_ = lean_ctor_get(v___y_1582_, 3);
v_maxRecDepth_1589_ = lean_ctor_get(v___y_1582_, 4);
v_ref_1590_ = lean_ctor_get(v___y_1582_, 5);
v_currNamespace_1591_ = lean_ctor_get(v___y_1582_, 6);
v_openDecls_1592_ = lean_ctor_get(v___y_1582_, 7);
v_initHeartbeats_1593_ = lean_ctor_get(v___y_1582_, 8);
v_maxHeartbeats_1594_ = lean_ctor_get(v___y_1582_, 9);
v_quotContext_1595_ = lean_ctor_get(v___y_1582_, 10);
v_currMacroScope_1596_ = lean_ctor_get(v___y_1582_, 11);
v_diag_1597_ = lean_ctor_get_uint8(v___y_1582_, sizeof(void*)*14);
v_cancelTk_x3f_1598_ = lean_ctor_get(v___y_1582_, 12);
v_suppressElabErrors_1599_ = lean_ctor_get_uint8(v___y_1582_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1600_ = lean_ctor_get(v___y_1582_, 13);
v___x_1601_ = lean_st_ref_get(v___y_1583_);
v_traceState_1602_ = lean_ctor_get(v___x_1601_, 4);
lean_inc_ref(v_traceState_1602_);
lean_dec(v___x_1601_);
v_traces_1603_ = lean_ctor_get(v_traceState_1602_, 0);
lean_inc_ref(v_traces_1603_);
lean_dec_ref(v_traceState_1602_);
v_ref_1604_ = l_Lean_replaceRef(v_ref_1578_, v_ref_1590_);
lean_inc_ref(v_inheritedTraceOptions_1600_);
lean_inc(v_cancelTk_x3f_1598_);
lean_inc(v_currMacroScope_1596_);
lean_inc(v_quotContext_1595_);
lean_inc(v_maxHeartbeats_1594_);
lean_inc(v_initHeartbeats_1593_);
lean_inc(v_openDecls_1592_);
lean_inc(v_currNamespace_1591_);
lean_inc(v_maxRecDepth_1589_);
lean_inc(v_currRecDepth_1588_);
lean_inc_ref(v_options_1587_);
lean_inc_ref(v_fileMap_1586_);
lean_inc_ref(v_fileName_1585_);
v___x_1605_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1605_, 0, v_fileName_1585_);
lean_ctor_set(v___x_1605_, 1, v_fileMap_1586_);
lean_ctor_set(v___x_1605_, 2, v_options_1587_);
lean_ctor_set(v___x_1605_, 3, v_currRecDepth_1588_);
lean_ctor_set(v___x_1605_, 4, v_maxRecDepth_1589_);
lean_ctor_set(v___x_1605_, 5, v_ref_1604_);
lean_ctor_set(v___x_1605_, 6, v_currNamespace_1591_);
lean_ctor_set(v___x_1605_, 7, v_openDecls_1592_);
lean_ctor_set(v___x_1605_, 8, v_initHeartbeats_1593_);
lean_ctor_set(v___x_1605_, 9, v_maxHeartbeats_1594_);
lean_ctor_set(v___x_1605_, 10, v_quotContext_1595_);
lean_ctor_set(v___x_1605_, 11, v_currMacroScope_1596_);
lean_ctor_set(v___x_1605_, 12, v_cancelTk_x3f_1598_);
lean_ctor_set(v___x_1605_, 13, v_inheritedTraceOptions_1600_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*14, v_diag_1597_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*14 + 1, v_suppressElabErrors_1599_);
v___x_1606_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1603_);
lean_dec_ref(v_traces_1603_);
v_sz_1607_ = lean_array_size(v___x_1606_);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__2_spec__3(v_sz_1607_, v___x_1608_, v___x_1606_);
v_msg_1610_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1610_, 0, v_data_1577_);
lean_ctor_set(v_msg_1610_, 1, v_msg_1579_);
lean_ctor_set(v_msg_1610_, 2, v___x_1609_);
v___x_1611_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3_spec__7(v_msg_1610_, v___y_1580_, v___y_1581_, v___x_1605_, v___y_1583_);
lean_dec_ref_known(v___x_1605_, 14);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1649_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1649_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v_traceState_1617_; lean_object* v_env_1618_; lean_object* v_nextMacroScope_1619_; lean_object* v_ngen_1620_; lean_object* v_auxDeclNGen_1621_; lean_object* v_cache_1622_; lean_object* v_messages_1623_; lean_object* v_infoState_1624_; lean_object* v_snapshotTasks_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1648_; 
v___x_1616_ = lean_st_ref_take(v___y_1583_);
v_traceState_1617_ = lean_ctor_get(v___x_1616_, 4);
v_env_1618_ = lean_ctor_get(v___x_1616_, 0);
v_nextMacroScope_1619_ = lean_ctor_get(v___x_1616_, 1);
v_ngen_1620_ = lean_ctor_get(v___x_1616_, 2);
v_auxDeclNGen_1621_ = lean_ctor_get(v___x_1616_, 3);
v_cache_1622_ = lean_ctor_get(v___x_1616_, 5);
v_messages_1623_ = lean_ctor_get(v___x_1616_, 6);
v_infoState_1624_ = lean_ctor_get(v___x_1616_, 7);
v_snapshotTasks_1625_ = lean_ctor_get(v___x_1616_, 8);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1627_ = v___x_1616_;
v_isShared_1628_ = v_isSharedCheck_1648_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_snapshotTasks_1625_);
lean_inc(v_infoState_1624_);
lean_inc(v_messages_1623_);
lean_inc(v_cache_1622_);
lean_inc(v_traceState_1617_);
lean_inc(v_auxDeclNGen_1621_);
lean_inc(v_ngen_1620_);
lean_inc(v_nextMacroScope_1619_);
lean_inc(v_env_1618_);
lean_dec(v___x_1616_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1648_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
uint64_t v_tid_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1646_; 
v_tid_1629_ = lean_ctor_get_uint64(v_traceState_1617_, sizeof(void*)*1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_traceState_1617_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v_traceState_1617_, 0);
lean_dec(v_unused_1647_);
v___x_1631_ = v_traceState_1617_;
v_isShared_1632_ = v_isSharedCheck_1646_;
goto v_resetjp_1630_;
}
else
{
lean_dec(v_traceState_1617_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1646_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v_ref_1578_);
lean_ctor_set(v___x_1633_, 1, v_a_1612_);
v___x_1634_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1576_, v___x_1633_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1634_);
v___x_1636_ = v___x_1631_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1634_);
lean_ctor_set_uint64(v_reuseFailAlloc_1645_, sizeof(void*)*1, v_tid_1629_);
v___x_1636_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 4, v___x_1636_);
v___x_1638_ = v___x_1627_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_env_1618_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_nextMacroScope_1619_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_ngen_1620_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_auxDeclNGen_1621_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v_cache_1622_);
lean_ctor_set(v_reuseFailAlloc_1644_, 6, v_messages_1623_);
lean_ctor_set(v_reuseFailAlloc_1644_, 7, v_infoState_1624_);
lean_ctor_set(v_reuseFailAlloc_1644_, 8, v_snapshotTasks_1625_);
v___x_1638_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1639_ = lean_st_ref_set(v___y_1583_, v___x_1638_);
v___x_1640_ = lean_box(0);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1640_);
v___x_1642_ = v___x_1614_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___boxed(lean_object* v_oldTraces_1650_, lean_object* v_data_1651_, lean_object* v_ref_1652_, lean_object* v_msg_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(v_oldTraces_1650_, v_data_1651_, v_ref_1652_, v_msg_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1660_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v_x_1660_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v_x_1660_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v_x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 1);
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v_x_1660_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v_x_1660_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v_x_1660_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set_tag(v___x_1672_, 0);
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg___boxed(lean_object* v_x_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(lean_object* v_cls_1681_, uint8_t v_collapsed_1682_, lean_object* v_tag_1683_, lean_object* v_opts_1684_, uint8_t v_clsEnabled_1685_, lean_object* v_oldTraces_1686_, lean_object* v_msg_1687_, lean_object* v_resStartStop_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_fst_1694_; lean_object* v_snd_1695_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v_data_1699_; lean_object* v_fst_1710_; lean_object* v_snd_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___y_1715_; lean_object* v_a_1716_; uint8_t v___y_1731_; double v___y_1762_; 
v_fst_1694_ = lean_ctor_get(v_resStartStop_1688_, 0);
lean_inc(v_fst_1694_);
v_snd_1695_ = lean_ctor_get(v_resStartStop_1688_, 1);
lean_inc(v_snd_1695_);
lean_dec_ref(v_resStartStop_1688_);
v_fst_1710_ = lean_ctor_get(v_snd_1695_, 0);
lean_inc(v_fst_1710_);
v_snd_1711_ = lean_ctor_get(v_snd_1695_, 1);
lean_inc(v_snd_1711_);
lean_dec(v_snd_1695_);
v___x_1712_ = l_Lean_trace_profiler;
v___x_1713_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_1684_, v___x_1712_);
if (v___x_1713_ == 0)
{
v___y_1731_ = v___x_1713_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1768_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_opts_1684_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; double v___x_1771_; double v___x_1772_; double v___x_1773_; 
v___x_1769_ = l_Lean_trace_profiler_threshold;
v___x_1770_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_1684_, v___x_1769_);
v___x_1771_ = lean_float_of_nat(v___x_1770_);
v___x_1772_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__2);
v___x_1773_ = lean_float_div(v___x_1771_, v___x_1772_);
v___y_1762_ = v___x_1773_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; double v___x_1776_; 
v___x_1774_ = l_Lean_trace_profiler_threshold;
v___x_1775_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__5(v_opts_1684_, v___x_1774_);
v___x_1776_ = lean_float_of_nat(v___x_1775_);
v___y_1762_ = v___x_1776_;
goto v___jp_1761_;
}
}
v___jp_1696_:
{
lean_object* v___x_1700_; 
lean_inc(v___y_1697_);
v___x_1700_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(v_oldTraces_1686_, v_data_1699_, v___y_1697_, v___y_1698_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v___x_1701_; 
lean_dec_ref_known(v___x_1700_, 1);
v___x_1701_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_1694_);
return v___x_1701_;
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_fst_1694_);
v_a_1702_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1700_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1700_);
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
v___jp_1714_:
{
uint8_t v_result_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; double v___x_1720_; lean_object* v_data_1721_; 
v_result_1717_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2_spec__4(v_fst_1694_);
v___x_1718_ = lean_box(v_result_1717_);
v___x_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
v___x_1720_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_1683_);
lean_inc_ref(v___x_1719_);
lean_inc(v_cls_1681_);
v_data_1721_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1721_, 0, v_cls_1681_);
lean_ctor_set(v_data_1721_, 1, v___x_1719_);
lean_ctor_set(v_data_1721_, 2, v_tag_1683_);
lean_ctor_set_float(v_data_1721_, sizeof(void*)*3, v___x_1720_);
lean_ctor_set_float(v_data_1721_, sizeof(void*)*3 + 8, v___x_1720_);
lean_ctor_set_uint8(v_data_1721_, sizeof(void*)*3 + 16, v_collapsed_1682_);
if (v___x_1713_ == 0)
{
lean_dec_ref_known(v___x_1719_, 1);
lean_dec(v_snd_1711_);
lean_dec(v_fst_1710_);
lean_dec_ref(v_tag_1683_);
lean_dec(v_cls_1681_);
v___y_1697_ = v___y_1715_;
v___y_1698_ = v_a_1716_;
v_data_1699_ = v_data_1721_;
goto v___jp_1696_;
}
else
{
lean_object* v_data_1722_; double v___x_1723_; double v___x_1724_; 
lean_dec_ref_known(v_data_1721_, 3);
v_data_1722_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1722_, 0, v_cls_1681_);
lean_ctor_set(v_data_1722_, 1, v___x_1719_);
lean_ctor_set(v_data_1722_, 2, v_tag_1683_);
v___x_1723_ = lean_unbox_float(v_fst_1710_);
lean_dec(v_fst_1710_);
lean_ctor_set_float(v_data_1722_, sizeof(void*)*3, v___x_1723_);
v___x_1724_ = lean_unbox_float(v_snd_1711_);
lean_dec(v_snd_1711_);
lean_ctor_set_float(v_data_1722_, sizeof(void*)*3 + 8, v___x_1724_);
lean_ctor_set_uint8(v_data_1722_, sizeof(void*)*3 + 16, v_collapsed_1682_);
v___y_1697_ = v___y_1715_;
v___y_1698_ = v_a_1716_;
v_data_1699_ = v_data_1722_;
goto v___jp_1696_;
}
}
v___jp_1725_:
{
lean_object* v_ref_1726_; lean_object* v___x_1727_; 
v_ref_1726_ = lean_ctor_get(v___y_1691_, 5);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc(v_fst_1694_);
v___x_1727_ = lean_apply_6(v_msg_1687_, v_fst_1694_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, lean_box(0));
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___y_1715_ = v_ref_1726_;
v_a_1716_ = v_a_1728_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1729_; 
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__2___closed__1);
v___y_1715_ = v_ref_1726_;
v_a_1716_ = v___x_1729_;
goto v___jp_1714_;
}
}
v___jp_1730_:
{
if (v_clsEnabled_1685_ == 0)
{
if (v___y_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v_traceState_1733_; lean_object* v_env_1734_; lean_object* v_nextMacroScope_1735_; lean_object* v_ngen_1736_; lean_object* v_auxDeclNGen_1737_; lean_object* v_cache_1738_; lean_object* v_messages_1739_; lean_object* v_infoState_1740_; lean_object* v_snapshotTasks_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_snd_1711_);
lean_dec(v_fst_1710_);
lean_dec_ref(v_msg_1687_);
lean_dec_ref(v_tag_1683_);
lean_dec(v_cls_1681_);
v___x_1732_ = lean_st_ref_take(v___y_1692_);
v_traceState_1733_ = lean_ctor_get(v___x_1732_, 4);
v_env_1734_ = lean_ctor_get(v___x_1732_, 0);
v_nextMacroScope_1735_ = lean_ctor_get(v___x_1732_, 1);
v_ngen_1736_ = lean_ctor_get(v___x_1732_, 2);
v_auxDeclNGen_1737_ = lean_ctor_get(v___x_1732_, 3);
v_cache_1738_ = lean_ctor_get(v___x_1732_, 5);
v_messages_1739_ = lean_ctor_get(v___x_1732_, 6);
v_infoState_1740_ = lean_ctor_get(v___x_1732_, 7);
v_snapshotTasks_1741_ = lean_ctor_get(v___x_1732_, 8);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1743_ = v___x_1732_;
v_isShared_1744_ = v_isSharedCheck_1760_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snapshotTasks_1741_);
lean_inc(v_infoState_1740_);
lean_inc(v_messages_1739_);
lean_inc(v_cache_1738_);
lean_inc(v_traceState_1733_);
lean_inc(v_auxDeclNGen_1737_);
lean_inc(v_ngen_1736_);
lean_inc(v_nextMacroScope_1735_);
lean_inc(v_env_1734_);
lean_dec(v___x_1732_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1760_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
uint64_t v_tid_1745_; lean_object* v_traces_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1759_; 
v_tid_1745_ = lean_ctor_get_uint64(v_traceState_1733_, sizeof(void*)*1);
v_traces_1746_ = lean_ctor_get(v_traceState_1733_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_traceState_1733_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1748_ = v_traceState_1733_;
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_traces_1746_);
lean_dec(v_traceState_1733_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1686_, v_traces_1746_);
lean_dec_ref(v_traces_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1750_);
lean_ctor_set_uint64(v_reuseFailAlloc_1758_, sizeof(void*)*1, v_tid_1745_);
v___x_1752_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 4, v___x_1752_);
v___x_1754_ = v___x_1743_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_env_1734_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_nextMacroScope_1735_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_ngen_1736_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_auxDeclNGen_1737_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1757_, 5, v_cache_1738_);
lean_ctor_set(v_reuseFailAlloc_1757_, 6, v_messages_1739_);
lean_ctor_set(v_reuseFailAlloc_1757_, 7, v_infoState_1740_);
lean_ctor_set(v_reuseFailAlloc_1757_, 8, v_snapshotTasks_1741_);
v___x_1754_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_st_ref_set(v___y_1692_, v___x_1754_);
v___x_1756_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_1694_);
return v___x_1756_;
}
}
}
}
}
else
{
goto v___jp_1725_;
}
}
else
{
goto v___jp_1725_;
}
}
v___jp_1761_:
{
double v___x_1763_; double v___x_1764_; double v___x_1765_; uint8_t v___x_1766_; 
v___x_1763_ = lean_unbox_float(v_snd_1711_);
v___x_1764_ = lean_unbox_float(v_fst_1710_);
v___x_1765_ = lean_float_sub(v___x_1763_, v___x_1764_);
v___x_1766_ = lean_float_decLt(v___y_1762_, v___x_1765_);
v___y_1731_ = v___x_1766_;
goto v___jp_1730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___boxed(lean_object* v_cls_1777_, lean_object* v_collapsed_1778_, lean_object* v_tag_1779_, lean_object* v_opts_1780_, lean_object* v_clsEnabled_1781_, lean_object* v_oldTraces_1782_, lean_object* v_msg_1783_, lean_object* v_resStartStop_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
uint8_t v_collapsed_boxed_1790_; uint8_t v_clsEnabled_boxed_1791_; lean_object* v_res_1792_; 
v_collapsed_boxed_1790_ = lean_unbox(v_collapsed_1778_);
v_clsEnabled_boxed_1791_ = lean_unbox(v_clsEnabled_1781_);
v_res_1792_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1777_, v_collapsed_boxed_1790_, v_tag_1779_, v_opts_1780_, v_clsEnabled_boxed_1791_, v_oldTraces_1782_, v_msg_1783_, v_resStartStop_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_opts_1780_);
return v_res_1792_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_box(0);
v___x_1795_ = lean_unsigned_to_nat(16u);
v___x_1796_ = lean_mk_array(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2);
v___x_1801_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
lean_ctor_set(v___x_1801_, 2, v___x_1800_);
lean_ctor_set(v___x_1801_, 3, v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object* v_g_1803_, lean_object* v_cfg_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_options_1810_; uint8_t v_hasTrace_1811_; 
v_options_1810_ = lean_ctor_get(v_a_1807_, 2);
v_hasTrace_1811_ = lean_ctor_get_uint8(v_options_1810_, sizeof(void*)*1);
if (v_hasTrace_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0));
lean_inc(v_g_1803_);
v___x_1813_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_1803_, v___x_1812_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1813_, 1);
v___x_1815_ = lean_array_get_size(v_a_1814_);
lean_dec(v_a_1814_);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_unsigned_to_nat(4u);
v___x_1818_ = lean_nat_mul(v___x_1815_, v___x_1817_);
v___x_1819_ = lean_unsigned_to_nat(3u);
v___x_1820_ = lean_nat_div(v___x_1818_, v___x_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = l_Nat_nextPowerOfTwo(v___x_1820_);
lean_dec(v___x_1820_);
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_mk_array(v___x_1821_, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1816_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3);
lean_inc_ref(v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
lean_ctor_set(v___x_1826_, 2, v___x_1825_);
v___x_1827_ = lean_st_mk_ref(v___x_1826_);
v___x_1828_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_1803_, v_cfg_1804_, v___x_1827_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1837_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = lean_st_ref_get(v___x_1827_);
lean_dec(v___x_1827_);
lean_dec(v___x_1833_);
if (v_isShared_1832_ == 0)
{
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1829_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_dec(v___x_1827_);
return v___x_1828_;
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_g_1803_);
v_a_1838_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1813_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1813_);
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
else
{
lean_object* v_inheritedTraceOptions_1846_; lean_object* v___f_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v_a_1855_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v_a_1870_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v_a_1875_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v_a_1880_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v_a_1892_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v_a_1897_; 
v_inheritedTraceOptions_1846_ = lean_ctor_get(v_a_1807_, 13);
v___f_1847_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4));
v___x_1848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__3));
v___x_1849_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__3___redArg___closed__1));
v___x_1850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__7);
v___x_1851_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1846_, v_options_1810_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = l_Lean_trace_profiler;
v___x_1951_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_1810_, v___x_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0));
lean_inc(v_g_1803_);
v___x_1953_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_1803_, v___x_1952_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = lean_array_get_size(v_a_1954_);
lean_dec(v_a_1954_);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_unsigned_to_nat(4u);
v___x_1958_ = lean_nat_mul(v___x_1955_, v___x_1957_);
v___x_1959_ = lean_unsigned_to_nat(3u);
v___x_1960_ = lean_nat_div(v___x_1958_, v___x_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = l_Nat_nextPowerOfTwo(v___x_1960_);
lean_dec(v___x_1960_);
v___x_1962_ = lean_box(0);
v___x_1963_ = lean_mk_array(v___x_1961_, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1956_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3);
lean_inc_ref(v___x_1964_);
v___x_1966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v___x_1964_);
lean_ctor_set(v___x_1966_, 2, v___x_1965_);
v___x_1967_ = lean_st_mk_ref(v___x_1966_);
v___x_1968_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_1803_, v_cfg_1804_, v___x_1967_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1977_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_st_ref_get(v___x_1967_);
lean_dec(v___x_1967_);
lean_dec(v___x_1973_);
if (v_isShared_1972_ == 0)
{
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1969_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
else
{
lean_dec(v___x_1967_);
return v___x_1968_;
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_g_1803_);
v_a_1978_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1953_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1953_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
goto v___jp_1899_;
}
}
else
{
goto v___jp_1899_;
}
v___jp_1852_:
{
lean_object* v___x_1856_; double v___x_1857_; double v___x_1858_; double v___x_1859_; double v___x_1860_; double v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1856_ = lean_io_mono_nanos_now();
v___x_1857_ = lean_float_of_nat(v___y_1854_);
v___x_1858_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go___closed__4);
v___x_1859_ = lean_float_div(v___x_1857_, v___x_1858_);
v___x_1860_ = lean_float_of_nat(v___x_1856_);
v___x_1861_ = lean_float_div(v___x_1860_, v___x_1858_);
v___x_1862_ = lean_box_float(v___x_1859_);
v___x_1863_ = lean_box_float(v___x_1861_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v_a_1855_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v___x_1848_, v_hasTrace_1811_, v___x_1849_, v_options_1810_, v___x_1851_, v___y_1853_, v___f_1847_, v___x_1865_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1866_;
}
v___jp_1867_:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_a_1870_);
v___y_1853_ = v___y_1868_;
v___y_1854_ = v___y_1869_;
v_a_1855_ = v___x_1871_;
goto v___jp_1852_;
}
v___jp_1872_:
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_a_1875_);
v___y_1853_ = v___y_1873_;
v___y_1854_ = v___y_1874_;
v_a_1855_ = v___x_1876_;
goto v___jp_1852_;
}
v___jp_1877_:
{
lean_object* v___x_1881_; double v___x_1882_; double v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1881_ = lean_io_get_num_heartbeats();
v___x_1882_ = lean_float_of_nat(v___y_1879_);
v___x_1883_ = lean_float_of_nat(v___x_1881_);
v___x_1884_ = lean_box_float(v___x_1882_);
v___x_1885_ = lean_box_float(v___x_1883_);
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v_a_1880_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v___x_1848_, v_hasTrace_1811_, v___x_1849_, v_options_1810_, v___x_1851_, v___y_1878_, v___f_1847_, v___x_1887_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1888_;
}
v___jp_1889_:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v_a_1892_);
v___y_1878_ = v___y_1890_;
v___y_1879_ = v___y_1891_;
v_a_1880_ = v___x_1893_;
goto v___jp_1877_;
}
v___jp_1894_:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1897_);
v___y_1878_ = v___y_1895_;
v___y_1879_ = v___y_1896_;
v_a_1880_ = v___x_1898_;
goto v___jp_1877_;
}
v___jp_1899_:
{
lean_object* v___x_1900_; lean_object* v_a_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1900_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___redArg(v_a_1808_);
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref(v___x_1900_);
v___x_1902_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1903_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go_spec__1(v_options_1810_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_io_mono_nanos_now();
v___x_1905_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0));
lean_inc(v_g_1803_);
v___x_1906_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_1803_, v___x_1905_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = lean_array_get_size(v_a_1907_);
lean_dec(v_a_1907_);
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_unsigned_to_nat(4u);
v___x_1911_ = lean_nat_mul(v___x_1908_, v___x_1910_);
v___x_1912_ = lean_unsigned_to_nat(3u);
v___x_1913_ = lean_nat_div(v___x_1911_, v___x_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = l_Nat_nextPowerOfTwo(v___x_1913_);
lean_dec(v___x_1913_);
v___x_1915_ = lean_box(0);
v___x_1916_ = lean_mk_array(v___x_1914_, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1909_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3);
lean_inc_ref(v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
lean_ctor_set(v___x_1919_, 2, v___x_1918_);
v___x_1920_ = lean_st_mk_ref(v___x_1919_);
v___x_1921_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_1803_, v_cfg_1804_, v___x_1920_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = lean_st_ref_get(v___x_1920_);
lean_dec(v___x_1920_);
lean_dec(v___x_1923_);
v___y_1873_ = v_a_1901_;
v___y_1874_ = v___x_1904_;
v_a_1875_ = v_a_1922_;
goto v___jp_1872_;
}
else
{
lean_dec(v___x_1920_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1924_; 
v_a_1924_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1921_, 1);
v___y_1873_ = v_a_1901_;
v___y_1874_ = v___x_1904_;
v_a_1875_ = v_a_1924_;
goto v___jp_1872_;
}
else
{
lean_object* v_a_1925_; 
v_a_1925_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1921_, 1);
v___y_1868_ = v_a_1901_;
v___y_1869_ = v___x_1904_;
v_a_1870_ = v_a_1925_;
goto v___jp_1867_;
}
}
}
else
{
lean_object* v_a_1926_; 
lean_dec(v_g_1803_);
v_a_1926_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1906_, 1);
v___y_1868_ = v_a_1901_;
v___y_1869_ = v___x_1904_;
v_a_1870_ = v_a_1926_;
goto v___jp_1867_;
}
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = lean_io_get_num_heartbeats();
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0));
lean_inc(v_g_1803_);
v___x_1929_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_g_1803_, v___x_1928_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = lean_array_get_size(v_a_1930_);
lean_dec(v_a_1930_);
v___x_1932_ = lean_unsigned_to_nat(0u);
v___x_1933_ = lean_unsigned_to_nat(4u);
v___x_1934_ = lean_nat_mul(v___x_1931_, v___x_1933_);
v___x_1935_ = lean_unsigned_to_nat(3u);
v___x_1936_ = lean_nat_div(v___x_1934_, v___x_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = l_Nat_nextPowerOfTwo(v___x_1936_);
lean_dec(v___x_1936_);
v___x_1938_ = lean_box(0);
v___x_1939_ = lean_mk_array(v___x_1937_, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1932_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3);
lean_inc_ref(v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1940_);
lean_ctor_set(v___x_1942_, 2, v___x_1941_);
v___x_1943_ = lean_st_mk_ref(v___x_1942_);
v___x_1944_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_go(v_g_1803_, v_cfg_1804_, v___x_1943_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v___x_1946_ = lean_st_ref_get(v___x_1943_);
lean_dec(v___x_1943_);
lean_dec(v___x_1946_);
v___y_1895_ = v_a_1901_;
v___y_1896_ = v___x_1927_;
v_a_1897_ = v_a_1945_;
goto v___jp_1894_;
}
else
{
lean_dec(v___x_1943_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1944_, 1);
v___y_1895_ = v_a_1901_;
v___y_1896_ = v___x_1927_;
v_a_1897_ = v_a_1947_;
goto v___jp_1894_;
}
else
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1944_, 1);
v___y_1890_ = v_a_1901_;
v___y_1891_ = v___x_1927_;
v_a_1892_ = v_a_1948_;
goto v___jp_1889_;
}
}
}
else
{
lean_object* v_a_1949_; 
lean_dec(v_g_1803_);
v_a_1949_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1929_, 1);
v___y_1890_ = v_a_1901_;
v___y_1891_ = v___x_1927_;
v_a_1892_ = v_a_1949_;
goto v___jp_1889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object* v_g_1986_, lean_object* v_cfg_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v_g_1986_, v_cfg_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec_ref(v_cfg_1987_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(lean_object* v_00_u03b1_1994_, lean_object* v_x_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_1995_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2002_, lean_object* v_x_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(v_00_u03b1_2002_, v_x_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2009_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_FalseOrByContra(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_AndFlatten(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_EmbeddedConstraint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
}
#ifdef __cplusplus
}
#endif
