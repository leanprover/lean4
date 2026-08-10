// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize
// Imports: public import Lean.Elab.Tactic.FalseOrByContra public import Lean.Meta.Tactic.BVDecide.Normalize.Basic public import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow public import Lean.Meta.Tactic.BVDecide.Normalize.Simproc public import Lean.Meta.Tactic.BVDecide.Normalize.Rewrite public import Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten public import Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint public import Lean.Meta.Tactic.BVDecide.Normalize.AC public import Lean.Meta.Tactic.BVDecide.Normalize.Structures public import Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec public import Lean.Meta.Tactic.BVDecide.Normalize.Enums public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis public import Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit public import Lean.Meta.Tactic.BVDecide.Normalize.Reduction import Lean.Meta.Sym.Util import Lean.Meta.Sym.Intro
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass;
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_falseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Preprocessing goal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Running preprocessing pipeline on:\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__7_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_36_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_55_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_unsigned_to_nat(32u);
v___x_57_ = lean_mk_empty_array_with_capacity(v___x_56_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_59_ = ((size_t)5ULL);
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_unsigned_to_nat(32u);
v___x_62_ = lean_mk_empty_array_with_capacity(v___x_61_);
v___x_63_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0);
v___x_64_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_60_);
lean_ctor_set(v___x_64_, 3, v___x_60_);
lean_ctor_set_usize(v___x_64_, 4, v___x_59_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; lean_object* v_traceState_68_; lean_object* v_traces_69_; lean_object* v___x_70_; lean_object* v_traceState_71_; lean_object* v_env_72_; lean_object* v_nextMacroScope_73_; lean_object* v_ngen_74_; lean_object* v_auxDeclNGen_75_; lean_object* v_cache_76_; lean_object* v_messages_77_; lean_object* v_infoState_78_; lean_object* v_snapshotTasks_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_98_; 
v___x_67_ = lean_st_ref_get(v___y_65_);
v_traceState_68_ = lean_ctor_get(v___x_67_, 4);
lean_inc_ref(v_traceState_68_);
lean_dec(v___x_67_);
v_traces_69_ = lean_ctor_get(v_traceState_68_, 0);
lean_inc_ref(v_traces_69_);
lean_dec_ref(v_traceState_68_);
v___x_70_ = lean_st_ref_take(v___y_65_);
v_traceState_71_ = lean_ctor_get(v___x_70_, 4);
v_env_72_ = lean_ctor_get(v___x_70_, 0);
v_nextMacroScope_73_ = lean_ctor_get(v___x_70_, 1);
v_ngen_74_ = lean_ctor_get(v___x_70_, 2);
v_auxDeclNGen_75_ = lean_ctor_get(v___x_70_, 3);
v_cache_76_ = lean_ctor_get(v___x_70_, 5);
v_messages_77_ = lean_ctor_get(v___x_70_, 6);
v_infoState_78_ = lean_ctor_get(v___x_70_, 7);
v_snapshotTasks_79_ = lean_ctor_get(v___x_70_, 8);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_98_ == 0)
{
v___x_81_ = v___x_70_;
v_isShared_82_ = v_isSharedCheck_98_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_snapshotTasks_79_);
lean_inc(v_infoState_78_);
lean_inc(v_messages_77_);
lean_inc(v_cache_76_);
lean_inc(v_traceState_71_);
lean_inc(v_auxDeclNGen_75_);
lean_inc(v_ngen_74_);
lean_inc(v_nextMacroScope_73_);
lean_inc(v_env_72_);
lean_dec(v___x_70_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_98_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
uint64_t v_tid_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_96_; 
v_tid_83_ = lean_ctor_get_uint64(v_traceState_71_, sizeof(void*)*1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_traceState_71_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v_traceState_71_, 0);
lean_dec(v_unused_97_);
v___x_85_ = v_traceState_71_;
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
else
{
lean_dec(v_traceState_71_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_87_);
lean_ctor_set_uint64(v_reuseFailAlloc_95_, sizeof(void*)*1, v_tid_83_);
v___x_89_ = v_reuseFailAlloc_95_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 4, v___x_89_);
v___x_91_ = v___x_81_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_env_72_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_nextMacroScope_73_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_ngen_74_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v_auxDeclNGen_75_);
lean_ctor_set(v_reuseFailAlloc_94_, 4, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_94_, 5, v_cache_76_);
lean_ctor_set(v_reuseFailAlloc_94_, 6, v_messages_77_);
lean_ctor_set(v_reuseFailAlloc_94_, 7, v_infoState_78_);
lean_ctor_set(v_reuseFailAlloc_94_, 8, v_snapshotTasks_79_);
v___x_91_ = v_reuseFailAlloc_94_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_st_ref_set(v___y_65_, v___x_91_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v_traces_69_);
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___boxed(lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_99_);
lean_dec(v___y_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___boxed(lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_121_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(lean_object* v_opts_122_, lean_object* v_opt_123_){
_start:
{
lean_object* v_name_124_; lean_object* v_defValue_125_; lean_object* v_map_126_; lean_object* v___x_127_; 
v_name_124_ = lean_ctor_get(v_opt_123_, 0);
v_defValue_125_ = lean_ctor_get(v_opt_123_, 1);
v_map_126_ = lean_ctor_get(v_opts_122_, 0);
v___x_127_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_126_, v_name_124_);
if (lean_obj_tag(v___x_127_) == 0)
{
uint8_t v___x_128_; 
v___x_128_ = lean_unbox(v_defValue_125_);
return v___x_128_;
}
else
{
lean_object* v_val_129_; 
v_val_129_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_val_129_);
lean_dec_ref_known(v___x_127_, 1);
if (lean_obj_tag(v_val_129_) == 1)
{
uint8_t v_v_130_; 
v_v_130_ = lean_ctor_get_uint8(v_val_129_, 0);
lean_dec_ref_known(v_val_129_, 0);
return v_v_130_;
}
else
{
uint8_t v___x_131_; 
lean_dec(v_val_129_);
v___x_131_ = lean_unbox(v_defValue_125_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___boxed(lean_object* v_opts_132_, lean_object* v_opt_133_){
_start:
{
uint8_t v_res_134_; lean_object* v_r_135_; 
v_res_134_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_opts_132_, v_opt_133_);
lean_dec_ref(v_opt_133_);
lean_dec_ref(v_opts_132_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0));
v___x_138_ = l_Lean_stringToMessageData(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object* v___x_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_name_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_160_; 
v_name_150_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v___x_139_, 1);
lean_dec(v_unused_161_);
v___x_152_ = v___x_139_;
v_isShared_153_ = v_isSharedCheck_160_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_name_150_);
lean_dec(v___x_139_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_160_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1);
v___x_155_ = l_Lean_MessageData_ofName(v_name_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 7);
lean_ctor_set(v___x_152_, 1, v___x_155_);
lean_ctor_set(v___x_152_, 0, v___x_154_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_159_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; 
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object* v___x_162_, lean_object* v_x_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(v___x_162_, v_x_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec_ref(v_x_163_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__1));
v___x_178_ = l_Lean_MessageData_ofFormat(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6(lean_object* v_x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___boxed(lean_object* v_x_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6(v_x_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec_ref(v_x_191_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(lean_object* v_opts_202_, lean_object* v_opt_203_){
_start:
{
lean_object* v_name_204_; lean_object* v_defValue_205_; lean_object* v_map_206_; lean_object* v___x_207_; 
v_name_204_ = lean_ctor_get(v_opt_203_, 0);
v_defValue_205_ = lean_ctor_get(v_opt_203_, 1);
v_map_206_ = lean_ctor_get(v_opts_202_, 0);
v___x_207_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_206_, v_name_204_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_inc(v_defValue_205_);
return v_defValue_205_;
}
else
{
lean_object* v_val_208_; 
v_val_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_207_, 1);
if (lean_obj_tag(v_val_208_) == 3)
{
lean_object* v_v_209_; 
v_v_209_ = lean_ctor_get(v_val_208_, 0);
lean_inc(v_v_209_);
lean_dec_ref_known(v_val_208_, 1);
return v_v_209_;
}
else
{
lean_dec(v_val_208_);
lean_inc(v_defValue_205_);
return v_defValue_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5___boxed(lean_object* v_opts_210_, lean_object* v_opt_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(v_opts_210_, v_opt_211_);
lean_dec_ref(v_opt_211_);
lean_dec_ref(v_opts_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3(size_t v_sz_213_, size_t v_i_214_, lean_object* v_bs_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_lt(v_i_214_, v_sz_213_);
if (v___x_216_ == 0)
{
return v_bs_215_;
}
else
{
lean_object* v_v_217_; lean_object* v_msg_218_; lean_object* v___x_219_; lean_object* v_bs_x27_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v_v_217_ = lean_array_uget_borrowed(v_bs_215_, v_i_214_);
v_msg_218_ = lean_ctor_get(v_v_217_, 1);
lean_inc_ref(v_msg_218_);
v___x_219_ = lean_unsigned_to_nat(0u);
v_bs_x27_220_ = lean_array_uset(v_bs_215_, v_i_214_, v___x_219_);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_add(v_i_214_, v___x_221_);
v___x_223_ = lean_array_uset(v_bs_x27_220_, v_i_214_, v_msg_218_);
v_i_214_ = v___x_222_;
v_bs_215_ = v___x_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_225_, lean_object* v_i_226_, lean_object* v_bs_227_){
_start:
{
size_t v_sz_boxed_228_; size_t v_i_boxed_229_; lean_object* v_res_230_; 
v_sz_boxed_228_ = lean_unbox_usize(v_sz_225_);
lean_dec(v_sz_225_);
v_i_boxed_229_ = lean_unbox_usize(v_i_226_);
lean_dec(v_i_226_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3(v_sz_boxed_228_, v_i_boxed_229_, v_bs_227_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3_spec__7(lean_object* v_msgData_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; lean_object* v_env_238_; lean_object* v___x_239_; lean_object* v_mctx_240_; lean_object* v_lctx_241_; lean_object* v_options_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_237_ = lean_st_ref_get(v___y_235_);
v_env_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc_ref(v_env_238_);
lean_dec(v___x_237_);
v___x_239_ = lean_st_ref_get(v___y_233_);
v_mctx_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc_ref(v_mctx_240_);
lean_dec(v___x_239_);
v_lctx_241_ = lean_ctor_get(v___y_232_, 2);
v_options_242_ = lean_ctor_get(v___y_234_, 2);
lean_inc_ref(v_options_242_);
lean_inc_ref(v_lctx_241_);
v___x_243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_243_, 0, v_env_238_);
lean_ctor_set(v___x_243_, 1, v_mctx_240_);
lean_ctor_set(v___x_243_, 2, v_lctx_241_);
lean_ctor_set(v___x_243_, 3, v_options_242_);
v___x_244_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_msgData_231_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3_spec__7___boxed(lean_object* v_msgData_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3_spec__7(v_msgData_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(lean_object* v_oldTraces_253_, lean_object* v_data_254_, lean_object* v_ref_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_fileName_262_; lean_object* v_fileMap_263_; lean_object* v_options_264_; lean_object* v_currRecDepth_265_; lean_object* v_maxRecDepth_266_; lean_object* v_ref_267_; lean_object* v_currNamespace_268_; lean_object* v_openDecls_269_; lean_object* v_initHeartbeats_270_; lean_object* v_maxHeartbeats_271_; lean_object* v_quotContext_272_; lean_object* v_currMacroScope_273_; uint8_t v_diag_274_; lean_object* v_cancelTk_x3f_275_; uint8_t v_suppressElabErrors_276_; lean_object* v_inheritedTraceOptions_277_; lean_object* v___x_278_; lean_object* v_traceState_279_; lean_object* v_traces_280_; lean_object* v_ref_281_; lean_object* v___x_282_; lean_object* v___x_283_; size_t v_sz_284_; size_t v___x_285_; lean_object* v___x_286_; lean_object* v_msg_287_; lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_326_; 
v_fileName_262_ = lean_ctor_get(v___y_259_, 0);
v_fileMap_263_ = lean_ctor_get(v___y_259_, 1);
v_options_264_ = lean_ctor_get(v___y_259_, 2);
v_currRecDepth_265_ = lean_ctor_get(v___y_259_, 3);
v_maxRecDepth_266_ = lean_ctor_get(v___y_259_, 4);
v_ref_267_ = lean_ctor_get(v___y_259_, 5);
v_currNamespace_268_ = lean_ctor_get(v___y_259_, 6);
v_openDecls_269_ = lean_ctor_get(v___y_259_, 7);
v_initHeartbeats_270_ = lean_ctor_get(v___y_259_, 8);
v_maxHeartbeats_271_ = lean_ctor_get(v___y_259_, 9);
v_quotContext_272_ = lean_ctor_get(v___y_259_, 10);
v_currMacroScope_273_ = lean_ctor_get(v___y_259_, 11);
v_diag_274_ = lean_ctor_get_uint8(v___y_259_, sizeof(void*)*14);
v_cancelTk_x3f_275_ = lean_ctor_get(v___y_259_, 12);
v_suppressElabErrors_276_ = lean_ctor_get_uint8(v___y_259_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_277_ = lean_ctor_get(v___y_259_, 13);
v___x_278_ = lean_st_ref_get(v___y_260_);
v_traceState_279_ = lean_ctor_get(v___x_278_, 4);
lean_inc_ref(v_traceState_279_);
lean_dec(v___x_278_);
v_traces_280_ = lean_ctor_get(v_traceState_279_, 0);
lean_inc_ref(v_traces_280_);
lean_dec_ref(v_traceState_279_);
v_ref_281_ = l_Lean_replaceRef(v_ref_255_, v_ref_267_);
lean_inc_ref(v_inheritedTraceOptions_277_);
lean_inc(v_cancelTk_x3f_275_);
lean_inc(v_currMacroScope_273_);
lean_inc(v_quotContext_272_);
lean_inc(v_maxHeartbeats_271_);
lean_inc(v_initHeartbeats_270_);
lean_inc(v_openDecls_269_);
lean_inc(v_currNamespace_268_);
lean_inc(v_maxRecDepth_266_);
lean_inc(v_currRecDepth_265_);
lean_inc_ref(v_options_264_);
lean_inc_ref(v_fileMap_263_);
lean_inc_ref(v_fileName_262_);
v___x_282_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_282_, 0, v_fileName_262_);
lean_ctor_set(v___x_282_, 1, v_fileMap_263_);
lean_ctor_set(v___x_282_, 2, v_options_264_);
lean_ctor_set(v___x_282_, 3, v_currRecDepth_265_);
lean_ctor_set(v___x_282_, 4, v_maxRecDepth_266_);
lean_ctor_set(v___x_282_, 5, v_ref_281_);
lean_ctor_set(v___x_282_, 6, v_currNamespace_268_);
lean_ctor_set(v___x_282_, 7, v_openDecls_269_);
lean_ctor_set(v___x_282_, 8, v_initHeartbeats_270_);
lean_ctor_set(v___x_282_, 9, v_maxHeartbeats_271_);
lean_ctor_set(v___x_282_, 10, v_quotContext_272_);
lean_ctor_set(v___x_282_, 11, v_currMacroScope_273_);
lean_ctor_set(v___x_282_, 12, v_cancelTk_x3f_275_);
lean_ctor_set(v___x_282_, 13, v_inheritedTraceOptions_277_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14, v_diag_274_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14 + 1, v_suppressElabErrors_276_);
v___x_283_ = l_Lean_PersistentArray_toArray___redArg(v_traces_280_);
lean_dec_ref(v_traces_280_);
v_sz_284_ = lean_array_size(v___x_283_);
v___x_285_ = ((size_t)0ULL);
v___x_286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3(v_sz_284_, v___x_285_, v___x_283_);
v_msg_287_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_287_, 0, v_data_254_);
lean_ctor_set(v_msg_287_, 1, v_msg_256_);
lean_ctor_set(v_msg_287_, 2, v___x_286_);
v___x_288_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3_spec__7(v_msg_287_, v___y_257_, v___y_258_, v___x_282_, v___y_260_);
lean_dec_ref_known(v___x_282_, 14);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_326_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_326_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_326_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v_traceState_294_; lean_object* v_env_295_; lean_object* v_nextMacroScope_296_; lean_object* v_ngen_297_; lean_object* v_auxDeclNGen_298_; lean_object* v_cache_299_; lean_object* v_messages_300_; lean_object* v_infoState_301_; lean_object* v_snapshotTasks_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_325_; 
v___x_293_ = lean_st_ref_take(v___y_260_);
v_traceState_294_ = lean_ctor_get(v___x_293_, 4);
v_env_295_ = lean_ctor_get(v___x_293_, 0);
v_nextMacroScope_296_ = lean_ctor_get(v___x_293_, 1);
v_ngen_297_ = lean_ctor_get(v___x_293_, 2);
v_auxDeclNGen_298_ = lean_ctor_get(v___x_293_, 3);
v_cache_299_ = lean_ctor_get(v___x_293_, 5);
v_messages_300_ = lean_ctor_get(v___x_293_, 6);
v_infoState_301_ = lean_ctor_get(v___x_293_, 7);
v_snapshotTasks_302_ = lean_ctor_get(v___x_293_, 8);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_325_ == 0)
{
v___x_304_ = v___x_293_;
v_isShared_305_ = v_isSharedCheck_325_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_snapshotTasks_302_);
lean_inc(v_infoState_301_);
lean_inc(v_messages_300_);
lean_inc(v_cache_299_);
lean_inc(v_traceState_294_);
lean_inc(v_auxDeclNGen_298_);
lean_inc(v_ngen_297_);
lean_inc(v_nextMacroScope_296_);
lean_inc(v_env_295_);
lean_dec(v___x_293_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_325_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
uint64_t v_tid_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_323_; 
v_tid_306_ = lean_ctor_get_uint64(v_traceState_294_, sizeof(void*)*1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_traceState_294_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v_traceState_294_, 0);
lean_dec(v_unused_324_);
v___x_308_ = v_traceState_294_;
v_isShared_309_ = v_isSharedCheck_323_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_traceState_294_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_323_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_ref_255_);
lean_ctor_set(v___x_310_, 1, v_a_289_);
v___x_311_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_253_, v___x_310_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_313_ = v___x_308_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_311_);
lean_ctor_set_uint64(v_reuseFailAlloc_322_, sizeof(void*)*1, v_tid_306_);
v___x_313_ = v_reuseFailAlloc_322_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_315_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 4, v___x_313_);
v___x_315_ = v___x_304_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_env_295_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_nextMacroScope_296_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_ngen_297_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_auxDeclNGen_298_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_321_, 5, v_cache_299_);
lean_ctor_set(v_reuseFailAlloc_321_, 6, v_messages_300_);
lean_ctor_set(v_reuseFailAlloc_321_, 7, v_infoState_301_);
lean_ctor_set(v_reuseFailAlloc_321_, 8, v_snapshotTasks_302_);
v___x_315_ = v_reuseFailAlloc_321_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = lean_st_ref_set(v___y_260_, v___x_315_);
v___x_317_ = lean_box(0);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_317_);
v___x_319_ = v___x_291_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_327_, lean_object* v_data_328_, lean_object* v_ref_329_, lean_object* v_msg_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(v_oldTraces_327_, v_data_328_, v_ref_329_, v_msg_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_a_339_ = lean_ctor_get(v_x_337_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v_x_337_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v_x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 1);
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v_x_337_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v_x_337_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v_x_337_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 0);
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg___boxed(lean_object* v_x_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_355_);
return v_res_357_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4(lean_object* v_e_358_){
_start:
{
if (lean_obj_tag(v_e_358_) == 0)
{
uint8_t v___x_359_; 
v___x_359_ = 2;
return v___x_359_;
}
else
{
lean_object* v_a_360_; uint8_t v___x_361_; 
v_a_360_ = lean_ctor_get(v_e_358_, 0);
v___x_361_ = lean_unbox(v_a_360_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; 
v___x_362_ = 1;
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4___boxed(lean_object* v_e_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4(v_e_364_);
lean_dec_ref(v_e_364_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0(void){
_start:
{
lean_object* v___x_367_; double v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_float_of_nat(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__1));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3(void){
_start:
{
lean_object* v___x_372_; double v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(1000u);
v___x_373_ = lean_float_of_nat(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(lean_object* v_cls_374_, uint8_t v_collapsed_375_, lean_object* v_tag_376_, lean_object* v_opts_377_, uint8_t v_clsEnabled_378_, lean_object* v_oldTraces_379_, lean_object* v_msg_380_, lean_object* v_resStartStop_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v_data_396_; lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___y_412_; lean_object* v_a_413_; uint8_t v___y_428_; double v___y_459_; 
v_fst_391_ = lean_ctor_get(v_resStartStop_381_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v_resStartStop_381_, 1);
lean_inc(v_snd_392_);
lean_dec_ref(v_resStartStop_381_);
v_fst_407_ = lean_ctor_get(v_snd_392_, 0);
lean_inc(v_fst_407_);
v_snd_408_ = lean_ctor_get(v_snd_392_, 1);
lean_inc(v_snd_408_);
lean_dec(v_snd_392_);
v___x_409_ = l_Lean_trace_profiler;
v___x_410_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_opts_377_, v___x_409_);
if (v___x_410_ == 0)
{
v___y_428_ = v___x_410_;
goto v___jp_427_;
}
else
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = l_Lean_trace_profiler_useHeartbeats;
v___x_465_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_opts_377_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; double v___x_468_; double v___x_469_; double v___x_470_; 
v___x_466_ = l_Lean_trace_profiler_threshold;
v___x_467_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(v_opts_377_, v___x_466_);
v___x_468_ = lean_float_of_nat(v___x_467_);
v___x_469_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3);
v___x_470_ = lean_float_div(v___x_468_, v___x_469_);
v___y_459_ = v___x_470_;
goto v___jp_458_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; double v___x_473_; 
v___x_471_ = l_Lean_trace_profiler_threshold;
v___x_472_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(v_opts_377_, v___x_471_);
v___x_473_ = lean_float_of_nat(v___x_472_);
v___y_459_ = v___x_473_;
goto v___jp_458_;
}
}
v___jp_393_:
{
lean_object* v___x_397_; 
lean_inc(v___y_394_);
v___x_397_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(v_oldTraces_379_, v_data_396_, v___y_394_, v___y_395_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; 
lean_dec_ref_known(v___x_397_, 1);
v___x_398_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_391_);
return v___x_398_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_fst_391_);
v_a_399_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_397_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_397_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
v___jp_411_:
{
uint8_t v_result_414_; lean_object* v___x_415_; lean_object* v___x_416_; double v___x_417_; lean_object* v_data_418_; 
v_result_414_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4(v_fst_391_);
v___x_415_ = lean_box(v_result_414_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0);
lean_inc_ref(v_tag_376_);
lean_inc_ref(v___x_416_);
lean_inc(v_cls_374_);
v_data_418_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_418_, 0, v_cls_374_);
lean_ctor_set(v_data_418_, 1, v___x_416_);
lean_ctor_set(v_data_418_, 2, v_tag_376_);
lean_ctor_set_float(v_data_418_, sizeof(void*)*3, v___x_417_);
lean_ctor_set_float(v_data_418_, sizeof(void*)*3 + 8, v___x_417_);
lean_ctor_set_uint8(v_data_418_, sizeof(void*)*3 + 16, v_collapsed_375_);
if (v___x_410_ == 0)
{
lean_dec_ref_known(v___x_416_, 1);
lean_dec(v_snd_408_);
lean_dec(v_fst_407_);
lean_dec_ref(v_tag_376_);
lean_dec(v_cls_374_);
v___y_394_ = v___y_412_;
v___y_395_ = v_a_413_;
v_data_396_ = v_data_418_;
goto v___jp_393_;
}
else
{
lean_object* v_data_419_; double v___x_420_; double v___x_421_; 
lean_dec_ref_known(v_data_418_, 3);
v_data_419_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_419_, 0, v_cls_374_);
lean_ctor_set(v_data_419_, 1, v___x_416_);
lean_ctor_set(v_data_419_, 2, v_tag_376_);
v___x_420_ = lean_unbox_float(v_fst_407_);
lean_dec(v_fst_407_);
lean_ctor_set_float(v_data_419_, sizeof(void*)*3, v___x_420_);
v___x_421_ = lean_unbox_float(v_snd_408_);
lean_dec(v_snd_408_);
lean_ctor_set_float(v_data_419_, sizeof(void*)*3 + 8, v___x_421_);
lean_ctor_set_uint8(v_data_419_, sizeof(void*)*3 + 16, v_collapsed_375_);
v___y_394_ = v___y_412_;
v___y_395_ = v_a_413_;
v_data_396_ = v_data_419_;
goto v___jp_393_;
}
}
v___jp_422_:
{
lean_object* v_ref_423_; lean_object* v___x_424_; 
v_ref_423_ = lean_ctor_get(v___y_388_, 5);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
lean_inc(v_fst_391_);
v___x_424_ = lean_apply_10(v_msg_380_, v_fst_391_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, lean_box(0));
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___y_412_ = v_ref_423_;
v_a_413_ = v_a_425_;
goto v___jp_411_;
}
else
{
lean_object* v___x_426_; 
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2);
v___y_412_ = v_ref_423_;
v_a_413_ = v___x_426_;
goto v___jp_411_;
}
}
v___jp_427_:
{
if (v_clsEnabled_378_ == 0)
{
if (v___y_428_ == 0)
{
lean_object* v___x_429_; lean_object* v_traceState_430_; lean_object* v_env_431_; lean_object* v_nextMacroScope_432_; lean_object* v_ngen_433_; lean_object* v_auxDeclNGen_434_; lean_object* v_cache_435_; lean_object* v_messages_436_; lean_object* v_infoState_437_; lean_object* v_snapshotTasks_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_457_; 
lean_dec(v_snd_408_);
lean_dec(v_fst_407_);
lean_dec_ref(v_msg_380_);
lean_dec_ref(v_tag_376_);
lean_dec(v_cls_374_);
v___x_429_ = lean_st_ref_take(v___y_389_);
v_traceState_430_ = lean_ctor_get(v___x_429_, 4);
v_env_431_ = lean_ctor_get(v___x_429_, 0);
v_nextMacroScope_432_ = lean_ctor_get(v___x_429_, 1);
v_ngen_433_ = lean_ctor_get(v___x_429_, 2);
v_auxDeclNGen_434_ = lean_ctor_get(v___x_429_, 3);
v_cache_435_ = lean_ctor_get(v___x_429_, 5);
v_messages_436_ = lean_ctor_get(v___x_429_, 6);
v_infoState_437_ = lean_ctor_get(v___x_429_, 7);
v_snapshotTasks_438_ = lean_ctor_get(v___x_429_, 8);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_457_ == 0)
{
v___x_440_ = v___x_429_;
v_isShared_441_ = v_isSharedCheck_457_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snapshotTasks_438_);
lean_inc(v_infoState_437_);
lean_inc(v_messages_436_);
lean_inc(v_cache_435_);
lean_inc(v_traceState_430_);
lean_inc(v_auxDeclNGen_434_);
lean_inc(v_ngen_433_);
lean_inc(v_nextMacroScope_432_);
lean_inc(v_env_431_);
lean_dec(v___x_429_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_457_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint64_t v_tid_442_; lean_object* v_traces_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_456_; 
v_tid_442_ = lean_ctor_get_uint64(v_traceState_430_, sizeof(void*)*1);
v_traces_443_ = lean_ctor_get(v_traceState_430_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_traceState_430_);
if (v_isSharedCheck_456_ == 0)
{
v___x_445_ = v_traceState_430_;
v_isShared_446_ = v_isSharedCheck_456_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_traces_443_);
lean_dec(v_traceState_430_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_456_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_379_, v_traces_443_);
lean_dec_ref(v_traces_443_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_447_);
lean_ctor_set_uint64(v_reuseFailAlloc_455_, sizeof(void*)*1, v_tid_442_);
v___x_449_ = v_reuseFailAlloc_455_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 4, v___x_449_);
v___x_451_ = v___x_440_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_env_431_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_nextMacroScope_432_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_ngen_433_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_auxDeclNGen_434_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_cache_435_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_messages_436_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_infoState_437_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_snapshotTasks_438_);
v___x_451_ = v_reuseFailAlloc_454_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_st_ref_set(v___y_389_, v___x_451_);
v___x_453_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_391_);
return v___x_453_;
}
}
}
}
}
else
{
goto v___jp_422_;
}
}
else
{
goto v___jp_422_;
}
}
v___jp_458_:
{
double v___x_460_; double v___x_461_; double v___x_462_; uint8_t v___x_463_; 
v___x_460_ = lean_unbox_float(v_snd_408_);
v___x_461_ = lean_unbox_float(v_fst_407_);
v___x_462_ = lean_float_sub(v___x_460_, v___x_461_);
v___x_463_ = lean_float_decLt(v___y_459_, v___x_462_);
v___y_428_ = v___x_463_;
goto v___jp_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___boxed(lean_object** _args){
lean_object* v_cls_474_ = _args[0];
lean_object* v_collapsed_475_ = _args[1];
lean_object* v_tag_476_ = _args[2];
lean_object* v_opts_477_ = _args[3];
lean_object* v_clsEnabled_478_ = _args[4];
lean_object* v_oldTraces_479_ = _args[5];
lean_object* v_msg_480_ = _args[6];
lean_object* v_resStartStop_481_ = _args[7];
lean_object* v___y_482_ = _args[8];
lean_object* v___y_483_ = _args[9];
lean_object* v___y_484_ = _args[10];
lean_object* v___y_485_ = _args[11];
lean_object* v___y_486_ = _args[12];
lean_object* v___y_487_ = _args[13];
lean_object* v___y_488_ = _args[14];
lean_object* v___y_489_ = _args[15];
lean_object* v___y_490_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_491_; uint8_t v_clsEnabled_boxed_492_; lean_object* v_res_493_; 
v_collapsed_boxed_491_ = lean_unbox(v_collapsed_475_);
v_clsEnabled_boxed_492_ = lean_unbox(v_clsEnabled_478_);
v_res_493_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_474_, v_collapsed_boxed_491_, v_tag_476_, v_opts_477_, v_clsEnabled_boxed_492_, v_oldTraces_479_, v_msg_480_, v_resStartStop_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v_opts_477_);
return v_res_493_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0(void){
_start:
{
lean_object* v___x_494_; double v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(1000000000u);
v___x_495_ = lean_float_of_nat(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1(void){
_start:
{
lean_object* v___x_496_; lean_object* v___f_497_; 
v___x_496_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v___f_497_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 11, 1);
lean_closure_set(v___f_497_, 0, v___x_496_);
return v___f_497_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4(void){
_start:
{
lean_object* v___x_501_; lean_object* v___f_502_; 
v___x_501_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v___f_502_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 11, 1);
lean_closure_set(v___f_502_, 0, v___x_501_);
return v___f_502_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5(void){
_start:
{
lean_object* v___x_503_; lean_object* v___f_504_; 
v___x_503_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v___f_504_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 11, 1);
lean_closure_set(v___f_504_, 0, v___x_503_);
return v___f_504_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6(void){
_start:
{
lean_object* v___x_505_; lean_object* v___f_506_; 
v___x_505_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v___f_506_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 11, 1);
lean_closure_set(v___f_506_, 0, v___x_505_);
return v___f_506_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7(void){
_start:
{
lean_object* v___x_507_; lean_object* v___f_508_; 
v___x_507_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v___f_508_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 11, 1);
lean_closure_set(v___f_508_, 0, v___x_507_);
return v___f_508_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8(void){
_start:
{
lean_object* v___x_509_; lean_object* v___f_510_; 
v___x_509_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v___f_510_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 11, 1);
lean_closure_set(v___f_510_, 0, v___x_509_);
return v___f_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8(uint8_t v___x_511_, uint8_t v_hasTrace_512_, lean_object* v_cls_513_, lean_object* v___x_514_, lean_object* v___x_515_, lean_object* v_____r_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___y_527_; uint8_t v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v_a_557_; uint8_t v___y_570_; uint8_t v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v_a_584_; uint8_t v___y_594_; uint8_t v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; uint8_t v_structures_646_; uint8_t v_fixedInt_647_; uint8_t v_enums_648_; uint8_t v_shortCircuit_649_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_711_; uint8_t v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; uint8_t v___y_723_; lean_object* v___y_724_; lean_object* v_a_725_; lean_object* v___y_738_; uint8_t v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; uint8_t v___y_750_; lean_object* v___y_751_; lean_object* v_a_752_; lean_object* v___y_762_; uint8_t v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; uint8_t v___y_774_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; uint8_t v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; uint8_t v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v_a_872_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; uint8_t v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; uint8_t v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v_a_896_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; uint8_t v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_1005_; lean_object* v___y_1006_; uint8_t v___y_1007_; lean_object* v___y_1008_; uint8_t v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v_a_1019_; lean_object* v___y_1029_; uint8_t v___y_1030_; lean_object* v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v_a_1043_; lean_object* v___y_1056_; uint8_t v___y_1057_; uint8_t v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; uint8_t v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; uint8_t v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v_a_1157_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; uint8_t v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; uint8_t v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v_a_1184_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; uint8_t v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; uint8_t v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1270_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; uint8_t v___y_1285_; lean_object* v___y_1286_; uint8_t v___y_1287_; lean_object* v_a_1288_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; uint8_t v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1306_; lean_object* v_a_1307_; lean_object* v___y_1317_; lean_object* v___y_1318_; uint8_t v___y_1319_; lean_object* v___y_1320_; uint8_t v___y_1321_; 
v_structures_646_ = lean_ctor_get_uint8(v___y_517_, sizeof(void*)*2 + 5);
v_fixedInt_647_ = lean_ctor_get_uint8(v___y_517_, sizeof(void*)*2 + 6);
v_enums_648_ = lean_ctor_get_uint8(v___y_517_, sizeof(void*)*2 + 7);
v_shortCircuit_649_ = lean_ctor_get_uint8(v___y_517_, sizeof(void*)*2 + 9);
if (v_structures_646_ == 0)
{
if (v_enums_648_ == 0)
{
v___y_1247_ = v___y_517_;
v___y_1248_ = v___y_518_;
v___y_1249_ = v___y_519_;
v___y_1250_ = v___y_520_;
v___y_1251_ = v___y_521_;
v___y_1252_ = v___y_522_;
v___y_1253_ = v___y_523_;
v___y_1254_ = v___y_524_;
goto v___jp_1246_;
}
else
{
goto v___jp_1361_;
}
}
else
{
goto v___jp_1361_;
}
v___jp_526_:
{
if (lean_obj_tag(v___y_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_541_; 
v_a_528_ = lean_ctor_get(v___y_527_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___y_527_);
if (v_isSharedCheck_541_ == 0)
{
v___x_530_ = v___y_527_;
v_isShared_531_ = v_isSharedCheck_541_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___y_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_541_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
uint8_t v___x_532_; 
v___x_532_ = lean_unbox(v_a_528_);
lean_dec(v_a_528_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_box(v___x_511_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_533_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_box(v_hasTrace_512_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_537_);
v___x_539_ = v___x_530_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
return v___y_527_;
}
}
v___jp_542_:
{
lean_object* v___x_558_; double v___x_559_; double v___x_560_; double v___x_561_; double v___x_562_; double v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_558_ = lean_io_mono_nanos_now();
v___x_559_ = lean_float_of_nat(v___y_556_);
v___x_560_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_561_ = lean_float_div(v___x_559_, v___x_560_);
v___x_562_ = lean_float_of_nat(v___x_558_);
v___x_563_ = lean_float_div(v___x_562_, v___x_560_);
v___x_564_ = lean_box_float(v___x_561_);
v___x_565_ = lean_box_float(v___x_563_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_a_557_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
lean_inc_ref(v___y_545_);
v___x_568_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_543_, v___x_514_, v___y_553_, v___y_544_, v___y_551_, v___y_545_, v___x_567_, v___y_550_, v___y_555_, v___y_547_, v___y_546_, v___y_549_, v___y_552_, v___y_548_, v___y_554_);
v___y_527_ = v___x_568_;
goto v___jp_526_;
}
v___jp_569_:
{
lean_object* v___x_585_; double v___x_586_; double v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_585_ = lean_io_get_num_heartbeats();
v___x_586_ = lean_float_of_nat(v___y_583_);
v___x_587_ = lean_float_of_nat(v___x_585_);
v___x_588_ = lean_box_float(v___x_586_);
v___x_589_ = lean_box_float(v___x_587_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_584_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
lean_inc_ref(v___y_572_);
v___x_592_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_570_, v___x_514_, v___y_580_, v___y_571_, v___y_578_, v___y_572_, v___x_591_, v___y_577_, v___y_582_, v___y_574_, v___y_573_, v___y_576_, v___y_579_, v___y_575_, v___y_581_);
v___y_527_ = v___x_592_;
goto v___jp_526_;
}
v___jp_593_:
{
lean_object* v___x_607_; lean_object* v_a_608_; uint8_t v___x_609_; 
v___x_607_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_604_);
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref(v___x_607_);
v___x_609_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_603_, v___x_515_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_io_mono_nanos_now();
lean_inc(v___y_604_);
lean_inc_ref(v___y_599_);
lean_inc(v___y_602_);
lean_inc_ref(v___y_600_);
lean_inc(v___y_597_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_605_);
lean_inc_ref(v___y_601_);
v___x_611_ = lean_apply_9(v___y_606_, v___y_601_, v___y_605_, v___y_598_, v___y_597_, v___y_600_, v___y_602_, v___y_599_, v___y_604_, lean_box(0));
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set_tag(v___x_614_, 1);
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v___y_543_ = v___y_594_;
v___y_544_ = v___y_595_;
v___y_545_ = v___y_596_;
v___y_546_ = v___y_597_;
v___y_547_ = v___y_598_;
v___y_548_ = v___y_599_;
v___y_549_ = v___y_600_;
v___y_550_ = v___y_601_;
v___y_551_ = v_a_608_;
v___y_552_ = v___y_602_;
v___y_553_ = v___y_603_;
v___y_554_ = v___y_604_;
v___y_555_ = v___y_605_;
v___y_556_ = v___x_610_;
v_a_557_ = v___x_617_;
goto v___jp_542_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_a_620_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set_tag(v___x_622_, 0);
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
v___y_543_ = v___y_594_;
v___y_544_ = v___y_595_;
v___y_545_ = v___y_596_;
v___y_546_ = v___y_597_;
v___y_547_ = v___y_598_;
v___y_548_ = v___y_599_;
v___y_549_ = v___y_600_;
v___y_550_ = v___y_601_;
v___y_551_ = v_a_608_;
v___y_552_ = v___y_602_;
v___y_553_ = v___y_603_;
v___y_554_ = v___y_604_;
v___y_555_ = v___y_605_;
v___y_556_ = v___x_610_;
v_a_557_ = v___x_625_;
goto v___jp_542_;
}
}
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_io_get_num_heartbeats();
lean_inc(v___y_604_);
lean_inc_ref(v___y_599_);
lean_inc(v___y_602_);
lean_inc_ref(v___y_600_);
lean_inc(v___y_597_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_605_);
lean_inc_ref(v___y_601_);
v___x_629_ = lean_apply_9(v___y_606_, v___y_601_, v___y_605_, v___y_598_, v___y_597_, v___y_600_, v___y_602_, v___y_599_, v___y_604_, lean_box(0));
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
v___y_570_ = v___y_594_;
v___y_571_ = v___y_595_;
v___y_572_ = v___y_596_;
v___y_573_ = v___y_597_;
v___y_574_ = v___y_598_;
v___y_575_ = v___y_599_;
v___y_576_ = v___y_600_;
v___y_577_ = v___y_601_;
v___y_578_ = v_a_608_;
v___y_579_ = v___y_602_;
v___y_580_ = v___y_603_;
v___y_581_ = v___y_604_;
v___y_582_ = v___y_605_;
v___y_583_ = v___x_628_;
v_a_584_ = v___x_635_;
goto v___jp_569_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
v_a_638_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_629_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_629_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 0);
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v___y_570_ = v___y_594_;
v___y_571_ = v___y_595_;
v___y_572_ = v___y_596_;
v___y_573_ = v___y_597_;
v___y_574_ = v___y_598_;
v___y_575_ = v___y_599_;
v___y_576_ = v___y_600_;
v___y_577_ = v___y_601_;
v___y_578_ = v_a_608_;
v___y_579_ = v___y_602_;
v___y_580_ = v___y_603_;
v___y_581_ = v___y_604_;
v___y_582_ = v___y_605_;
v___y_583_ = v___x_628_;
v_a_584_ = v___x_643_;
goto v___jp_569_;
}
}
}
}
}
v___jp_650_:
{
lean_object* v___x_659_; lean_object* v_a_660_; lean_object* v___x_661_; 
v___x_659_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_651_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
v___x_661_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_660_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v_a_660_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_689_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_689_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_689_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_689_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
uint8_t v___x_666_; 
v___x_666_ = lean_unbox(v_a_662_);
lean_dec(v_a_662_);
if (v___x_666_ == 0)
{
if (v_shortCircuit_649_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
v___x_667_ = lean_box(v___x_511_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_667_);
v___x_669_ = v___x_664_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
lean_object* v___x_671_; lean_object* v_options_672_; uint8_t v_hasTrace_673_; 
lean_del_object(v___x_664_);
v___x_671_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_options_672_ = lean_ctor_get(v___y_657_, 2);
v_hasTrace_673_ = lean_ctor_get_uint8(v_options_672_, sizeof(void*)*1);
if (v_hasTrace_673_ == 0)
{
lean_object* v_run_x27_674_; lean_object* v___x_675_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
v_run_x27_674_ = lean_ctor_get(v___x_671_, 1);
lean_inc_ref(v_run_x27_674_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc(v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc(v___y_652_);
lean_inc_ref(v___y_651_);
v___x_675_ = lean_apply_9(v_run_x27_674_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, lean_box(0));
v___y_527_ = v___x_675_;
goto v___jp_526_;
}
else
{
lean_object* v_run_x27_676_; lean_object* v_inheritedTraceOptions_677_; lean_object* v___f_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_run_x27_676_ = lean_ctor_get(v___x_671_, 1);
v_inheritedTraceOptions_677_ = lean_ctor_get(v___y_657_, 13);
v___f_678_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1);
v___x_679_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_513_);
v___x_680_ = l_Lean_Name_append(v___x_679_, v_cls_513_);
v___x_681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_677_, v_options_672_, v___x_680_);
lean_dec(v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = l_Lean_trace_profiler;
v___x_683_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_672_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
lean_inc_ref(v_run_x27_676_);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc(v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc(v___y_652_);
lean_inc_ref(v___y_651_);
v___x_684_ = lean_apply_9(v_run_x27_676_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, lean_box(0));
v___y_527_ = v___x_684_;
goto v___jp_526_;
}
else
{
lean_inc_ref(v_run_x27_676_);
v___y_594_ = v_hasTrace_673_;
v___y_595_ = v___x_681_;
v___y_596_ = v___f_678_;
v___y_597_ = v___y_654_;
v___y_598_ = v___y_653_;
v___y_599_ = v___y_657_;
v___y_600_ = v___y_655_;
v___y_601_ = v___y_651_;
v___y_602_ = v___y_656_;
v___y_603_ = v_options_672_;
v___y_604_ = v___y_658_;
v___y_605_ = v___y_652_;
v___y_606_ = v_run_x27_676_;
goto v___jp_593_;
}
}
else
{
lean_inc_ref(v_run_x27_676_);
v___y_594_ = v_hasTrace_673_;
v___y_595_ = v___x_681_;
v___y_596_ = v___f_678_;
v___y_597_ = v___y_654_;
v___y_598_ = v___y_653_;
v___y_599_ = v___y_657_;
v___y_600_ = v___y_655_;
v___y_601_ = v___y_651_;
v___y_602_ = v___y_656_;
v___y_603_ = v_options_672_;
v___y_604_ = v___y_658_;
v___y_605_ = v___y_652_;
v___y_606_ = v_run_x27_676_;
goto v___jp_593_;
}
}
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_687_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
v___x_685_ = lean_box(v_hasTrace_512_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_685_);
v___x_687_ = v___x_664_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
return v___x_661_;
}
}
v___jp_690_:
{
if (lean_obj_tag(v___y_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_709_; 
v_a_700_ = lean_ctor_get(v___y_699_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___y_699_);
if (v_isSharedCheck_709_ == 0)
{
v___x_702_ = v___y_699_;
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___y_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
uint8_t v___x_704_; 
v___x_704_ = lean_unbox(v_a_700_);
lean_dec(v_a_700_);
if (v___x_704_ == 0)
{
lean_del_object(v___x_702_);
v___y_651_ = v___y_691_;
v___y_652_ = v___y_696_;
v___y_653_ = v___y_697_;
v___y_654_ = v___y_693_;
v___y_655_ = v___y_695_;
v___y_656_ = v___y_694_;
v___y_657_ = v___y_698_;
v___y_658_ = v___y_692_;
goto v___jp_650_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
v___x_705_ = lean_box(v_hasTrace_512_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_705_);
v___x_707_ = v___x_702_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
return v___y_699_;
}
}
v___jp_710_:
{
lean_object* v___x_726_; double v___x_727_; double v___x_728_; double v___x_729_; double v___x_730_; double v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_726_ = lean_io_mono_nanos_now();
v___x_727_ = lean_float_of_nat(v___y_715_);
v___x_728_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_729_ = lean_float_div(v___x_727_, v___x_728_);
v___x_730_ = lean_float_of_nat(v___x_726_);
v___x_731_ = lean_float_div(v___x_730_, v___x_728_);
v___x_732_ = lean_box_float(v___x_729_);
v___x_733_ = lean_box_float(v___x_731_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v_a_725_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
lean_inc_ref(v___y_716_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_736_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_723_, v___x_514_, v___y_719_, v___y_712_, v___y_713_, v___y_716_, v___x_735_, v___y_711_, v___y_720_, v___y_722_, v___y_718_, v___y_721_, v___y_714_, v___y_724_, v___y_717_);
v___y_691_ = v___y_711_;
v___y_692_ = v___y_717_;
v___y_693_ = v___y_718_;
v___y_694_ = v___y_714_;
v___y_695_ = v___y_721_;
v___y_696_ = v___y_720_;
v___y_697_ = v___y_722_;
v___y_698_ = v___y_724_;
v___y_699_ = v___x_736_;
goto v___jp_690_;
}
v___jp_737_:
{
lean_object* v___x_753_; double v___x_754_; double v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_753_ = lean_io_get_num_heartbeats();
v___x_754_ = lean_float_of_nat(v___y_745_);
v___x_755_ = lean_float_of_nat(v___x_753_);
v___x_756_ = lean_box_float(v___x_754_);
v___x_757_ = lean_box_float(v___x_755_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_a_752_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
lean_inc_ref(v___y_742_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_760_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_750_, v___x_514_, v___y_746_, v___y_739_, v___y_740_, v___y_742_, v___x_759_, v___y_738_, v___y_747_, v___y_749_, v___y_744_, v___y_748_, v___y_741_, v___y_751_, v___y_743_);
v___y_691_ = v___y_738_;
v___y_692_ = v___y_743_;
v___y_693_ = v___y_744_;
v___y_694_ = v___y_741_;
v___y_695_ = v___y_748_;
v___y_696_ = v___y_747_;
v___y_697_ = v___y_749_;
v___y_698_ = v___y_751_;
v___y_699_ = v___x_760_;
goto v___jp_690_;
}
v___jp_761_:
{
lean_object* v___x_775_; lean_object* v_a_776_; uint8_t v___x_777_; 
v___x_775_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_766_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_775_);
v___x_777_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_768_, v___x_515_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_io_mono_nanos_now();
lean_inc(v___y_766_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_764_);
lean_inc_ref(v___y_770_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_772_);
lean_inc(v___y_769_);
lean_inc_ref(v___y_762_);
v___x_779_ = lean_apply_9(v___y_771_, v___y_762_, v___y_769_, v___y_772_, v___y_767_, v___y_770_, v___y_764_, v___y_773_, v___y_766_, lean_box(0));
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 1);
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v___y_711_ = v___y_762_;
v___y_712_ = v___y_763_;
v___y_713_ = v_a_776_;
v___y_714_ = v___y_764_;
v___y_715_ = v___x_778_;
v___y_716_ = v___y_765_;
v___y_717_ = v___y_766_;
v___y_718_ = v___y_767_;
v___y_719_ = v___y_768_;
v___y_720_ = v___y_769_;
v___y_721_ = v___y_770_;
v___y_722_ = v___y_772_;
v___y_723_ = v___y_774_;
v___y_724_ = v___y_773_;
v_a_725_ = v___x_785_;
goto v___jp_710_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_779_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_779_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 0);
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v___y_711_ = v___y_762_;
v___y_712_ = v___y_763_;
v___y_713_ = v_a_776_;
v___y_714_ = v___y_764_;
v___y_715_ = v___x_778_;
v___y_716_ = v___y_765_;
v___y_717_ = v___y_766_;
v___y_718_ = v___y_767_;
v___y_719_ = v___y_768_;
v___y_720_ = v___y_769_;
v___y_721_ = v___y_770_;
v___y_722_ = v___y_772_;
v___y_723_ = v___y_774_;
v___y_724_ = v___y_773_;
v_a_725_ = v___x_793_;
goto v___jp_710_;
}
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_io_get_num_heartbeats();
lean_inc(v___y_766_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_764_);
lean_inc_ref(v___y_770_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_772_);
lean_inc(v___y_769_);
lean_inc_ref(v___y_762_);
v___x_797_ = lean_apply_9(v___y_771_, v___y_762_, v___y_769_, v___y_772_, v___y_767_, v___y_770_, v___y_764_, v___y_773_, v___y_766_, lean_box(0));
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 1);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v___y_738_ = v___y_762_;
v___y_739_ = v___y_763_;
v___y_740_ = v_a_776_;
v___y_741_ = v___y_764_;
v___y_742_ = v___y_765_;
v___y_743_ = v___y_766_;
v___y_744_ = v___y_767_;
v___y_745_ = v___x_796_;
v___y_746_ = v___y_768_;
v___y_747_ = v___y_769_;
v___y_748_ = v___y_770_;
v___y_749_ = v___y_772_;
v___y_750_ = v___y_774_;
v___y_751_ = v___y_773_;
v_a_752_ = v___x_803_;
goto v___jp_737_;
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
v_a_806_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_797_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_797_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 0);
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_738_ = v___y_762_;
v___y_739_ = v___y_763_;
v___y_740_ = v_a_776_;
v___y_741_ = v___y_764_;
v___y_742_ = v___y_765_;
v___y_743_ = v___y_766_;
v___y_744_ = v___y_767_;
v___y_745_ = v___x_796_;
v___y_746_ = v___y_768_;
v___y_747_ = v___y_769_;
v___y_748_ = v___y_770_;
v___y_749_ = v___y_772_;
v___y_750_ = v___y_774_;
v___y_751_ = v___y_773_;
v_a_752_ = v___x_811_;
goto v___jp_737_;
}
}
}
}
}
v___jp_814_:
{
if (v_fixedInt_647_ == 0)
{
v___y_651_ = v___y_815_;
v___y_652_ = v___y_816_;
v___y_653_ = v___y_817_;
v___y_654_ = v___y_818_;
v___y_655_ = v___y_819_;
v___y_656_ = v___y_820_;
v___y_657_ = v___y_821_;
v___y_658_ = v___y_822_;
goto v___jp_650_;
}
else
{
lean_object* v___x_823_; lean_object* v_options_824_; uint8_t v_hasTrace_825_; 
v___x_823_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_options_824_ = lean_ctor_get(v___y_821_, 2);
v_hasTrace_825_ = lean_ctor_get_uint8(v_options_824_, sizeof(void*)*1);
if (v_hasTrace_825_ == 0)
{
lean_object* v_run_x27_826_; lean_object* v___x_827_; 
v_run_x27_826_ = lean_ctor_get(v___x_823_, 1);
lean_inc_ref(v_run_x27_826_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
v___x_827_ = lean_apply_9(v_run_x27_826_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, lean_box(0));
v___y_691_ = v___y_815_;
v___y_692_ = v___y_822_;
v___y_693_ = v___y_818_;
v___y_694_ = v___y_820_;
v___y_695_ = v___y_819_;
v___y_696_ = v___y_816_;
v___y_697_ = v___y_817_;
v___y_698_ = v___y_821_;
v___y_699_ = v___x_827_;
goto v___jp_690_;
}
else
{
lean_object* v_run_x27_828_; lean_object* v_inheritedTraceOptions_829_; lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_run_x27_828_ = lean_ctor_get(v___x_823_, 1);
v_inheritedTraceOptions_829_ = lean_ctor_get(v___y_821_, 13);
v___f_830_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4);
v___x_831_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_513_);
v___x_832_ = l_Lean_Name_append(v___x_831_, v_cls_513_);
v___x_833_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_829_, v_options_824_, v___x_832_);
lean_dec(v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = l_Lean_trace_profiler;
v___x_835_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_824_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_inc_ref(v_run_x27_828_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
v___x_836_ = lean_apply_9(v_run_x27_828_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, lean_box(0));
v___y_691_ = v___y_815_;
v___y_692_ = v___y_822_;
v___y_693_ = v___y_818_;
v___y_694_ = v___y_820_;
v___y_695_ = v___y_819_;
v___y_696_ = v___y_816_;
v___y_697_ = v___y_817_;
v___y_698_ = v___y_821_;
v___y_699_ = v___x_836_;
goto v___jp_690_;
}
else
{
lean_inc_ref(v_run_x27_828_);
v___y_762_ = v___y_815_;
v___y_763_ = v___x_833_;
v___y_764_ = v___y_820_;
v___y_765_ = v___f_830_;
v___y_766_ = v___y_822_;
v___y_767_ = v___y_818_;
v___y_768_ = v_options_824_;
v___y_769_ = v___y_816_;
v___y_770_ = v___y_819_;
v___y_771_ = v_run_x27_828_;
v___y_772_ = v___y_817_;
v___y_773_ = v___y_821_;
v___y_774_ = v_hasTrace_825_;
goto v___jp_761_;
}
}
else
{
lean_inc_ref(v_run_x27_828_);
v___y_762_ = v___y_815_;
v___y_763_ = v___x_833_;
v___y_764_ = v___y_820_;
v___y_765_ = v___f_830_;
v___y_766_ = v___y_822_;
v___y_767_ = v___y_818_;
v___y_768_ = v_options_824_;
v___y_769_ = v___y_816_;
v___y_770_ = v___y_819_;
v___y_771_ = v_run_x27_828_;
v___y_772_ = v___y_817_;
v___y_773_ = v___y_821_;
v___y_774_ = v_hasTrace_825_;
goto v___jp_761_;
}
}
}
}
v___jp_837_:
{
if (lean_obj_tag(v___y_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_856_; 
v_a_847_ = lean_ctor_get(v___y_846_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___y_846_);
if (v_isSharedCheck_856_ == 0)
{
v___x_849_ = v___y_846_;
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___y_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
uint8_t v___x_851_; 
v___x_851_ = lean_unbox(v_a_847_);
lean_dec(v_a_847_);
if (v___x_851_ == 0)
{
lean_del_object(v___x_849_);
v___y_815_ = v___y_841_;
v___y_816_ = v___y_842_;
v___y_817_ = v___y_845_;
v___y_818_ = v___y_844_;
v___y_819_ = v___y_839_;
v___y_820_ = v___y_840_;
v___y_821_ = v___y_843_;
v___y_822_ = v___y_838_;
goto v___jp_814_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_854_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
v___x_852_ = lean_box(v_hasTrace_512_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_852_);
v___x_854_ = v___x_849_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
return v___y_846_;
}
}
v___jp_857_:
{
lean_object* v___x_873_; double v___x_874_; double v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_873_ = lean_io_get_num_heartbeats();
v___x_874_ = lean_float_of_nat(v___y_858_);
v___x_875_ = lean_float_of_nat(v___x_873_);
v___x_876_ = lean_box_float(v___x_874_);
v___x_877_ = lean_box_float(v___x_875_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_a_872_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
lean_inc_ref(v___y_865_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_880_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_868_, v___x_514_, v___y_863_, v___y_862_, v___y_866_, v___y_865_, v___x_879_, v___y_861_, v___y_869_, v___y_864_, v___y_870_, v___y_859_, v___y_860_, v___y_871_, v___y_867_);
v___y_838_ = v___y_867_;
v___y_839_ = v___y_859_;
v___y_840_ = v___y_860_;
v___y_841_ = v___y_861_;
v___y_842_ = v___y_869_;
v___y_843_ = v___y_871_;
v___y_844_ = v___y_870_;
v___y_845_ = v___y_864_;
v___y_846_ = v___x_880_;
goto v___jp_837_;
}
v___jp_881_:
{
lean_object* v___x_897_; double v___x_898_; double v___x_899_; double v___x_900_; double v___x_901_; double v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_897_ = lean_io_mono_nanos_now();
v___x_898_ = lean_float_of_nat(v___y_886_);
v___x_899_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_900_ = lean_float_div(v___x_898_, v___x_899_);
v___x_901_ = lean_float_of_nat(v___x_897_);
v___x_902_ = lean_float_div(v___x_901_, v___x_899_);
v___x_903_ = lean_box_float(v___x_900_);
v___x_904_ = lean_box_float(v___x_902_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v_a_896_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
lean_inc_ref(v___y_889_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_907_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_892_, v___x_514_, v___y_887_, v___y_885_, v___y_890_, v___y_889_, v___x_906_, v___y_884_, v___y_893_, v___y_888_, v___y_894_, v___y_882_, v___y_883_, v___y_895_, v___y_891_);
v___y_838_ = v___y_891_;
v___y_839_ = v___y_882_;
v___y_840_ = v___y_883_;
v___y_841_ = v___y_884_;
v___y_842_ = v___y_893_;
v___y_843_ = v___y_895_;
v___y_844_ = v___y_894_;
v___y_845_ = v___y_888_;
v___y_846_ = v___x_907_;
goto v___jp_837_;
}
v___jp_908_:
{
lean_object* v___x_922_; lean_object* v_a_923_; uint8_t v___x_924_; 
v___x_922_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_917_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v___x_922_);
v___x_924_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_913_, v___x_515_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_io_mono_nanos_now();
lean_inc(v___y_917_);
lean_inc_ref(v___y_921_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_920_);
lean_inc_ref(v___y_914_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_911_);
v___x_926_ = lean_apply_9(v___y_916_, v___y_911_, v___y_919_, v___y_914_, v___y_920_, v___y_909_, v___y_910_, v___y_921_, v___y_917_, lean_box(0));
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
lean_ctor_set_tag(v___x_929_, 1);
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
v___y_882_ = v___y_909_;
v___y_883_ = v___y_910_;
v___y_884_ = v___y_911_;
v___y_885_ = v___y_912_;
v___y_886_ = v___x_925_;
v___y_887_ = v___y_913_;
v___y_888_ = v___y_914_;
v___y_889_ = v___y_915_;
v___y_890_ = v_a_923_;
v___y_891_ = v___y_917_;
v___y_892_ = v___y_918_;
v___y_893_ = v___y_919_;
v___y_894_ = v___y_920_;
v___y_895_ = v___y_921_;
v_a_896_ = v___x_932_;
goto v___jp_881_;
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
v_a_935_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_926_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_926_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set_tag(v___x_937_, 0);
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
v___y_882_ = v___y_909_;
v___y_883_ = v___y_910_;
v___y_884_ = v___y_911_;
v___y_885_ = v___y_912_;
v___y_886_ = v___x_925_;
v___y_887_ = v___y_913_;
v___y_888_ = v___y_914_;
v___y_889_ = v___y_915_;
v___y_890_ = v_a_923_;
v___y_891_ = v___y_917_;
v___y_892_ = v___y_918_;
v___y_893_ = v___y_919_;
v___y_894_ = v___y_920_;
v___y_895_ = v___y_921_;
v_a_896_ = v___x_940_;
goto v___jp_881_;
}
}
}
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_io_get_num_heartbeats();
lean_inc(v___y_917_);
lean_inc_ref(v___y_921_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_920_);
lean_inc_ref(v___y_914_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_911_);
v___x_944_ = lean_apply_9(v___y_916_, v___y_911_, v___y_919_, v___y_914_, v___y_920_, v___y_909_, v___y_910_, v___y_921_, v___y_917_, lean_box(0));
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 1);
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
v___y_858_ = v___x_943_;
v___y_859_ = v___y_909_;
v___y_860_ = v___y_910_;
v___y_861_ = v___y_911_;
v___y_862_ = v___y_912_;
v___y_863_ = v___y_913_;
v___y_864_ = v___y_914_;
v___y_865_ = v___y_915_;
v___y_866_ = v_a_923_;
v___y_867_ = v___y_917_;
v___y_868_ = v___y_918_;
v___y_869_ = v___y_919_;
v___y_870_ = v___y_920_;
v___y_871_ = v___y_921_;
v_a_872_ = v___x_950_;
goto v___jp_857_;
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_953_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_944_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_944_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 0);
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
v___y_858_ = v___x_943_;
v___y_859_ = v___y_909_;
v___y_860_ = v___y_910_;
v___y_861_ = v___y_911_;
v___y_862_ = v___y_912_;
v___y_863_ = v___y_913_;
v___y_864_ = v___y_914_;
v___y_865_ = v___y_915_;
v___y_866_ = v_a_923_;
v___y_867_ = v___y_917_;
v___y_868_ = v___y_918_;
v___y_869_ = v___y_919_;
v___y_870_ = v___y_920_;
v___y_871_ = v___y_921_;
v_a_872_ = v___x_958_;
goto v___jp_857_;
}
}
}
}
}
v___jp_961_:
{
if (v_enums_648_ == 0)
{
v___y_815_ = v___y_962_;
v___y_816_ = v___y_963_;
v___y_817_ = v___y_964_;
v___y_818_ = v___y_965_;
v___y_819_ = v___y_966_;
v___y_820_ = v___y_967_;
v___y_821_ = v___y_968_;
v___y_822_ = v___y_969_;
goto v___jp_814_;
}
else
{
lean_object* v___x_970_; lean_object* v_options_971_; uint8_t v_hasTrace_972_; 
v___x_970_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_options_971_ = lean_ctor_get(v___y_968_, 2);
v_hasTrace_972_ = lean_ctor_get_uint8(v_options_971_, sizeof(void*)*1);
if (v_hasTrace_972_ == 0)
{
lean_object* v_run_x27_973_; lean_object* v___x_974_; 
v_run_x27_973_ = lean_ctor_get(v___x_970_, 1);
lean_inc_ref(v_run_x27_973_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
v___x_974_ = lean_apply_9(v_run_x27_973_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
v___y_838_ = v___y_969_;
v___y_839_ = v___y_966_;
v___y_840_ = v___y_967_;
v___y_841_ = v___y_962_;
v___y_842_ = v___y_963_;
v___y_843_ = v___y_968_;
v___y_844_ = v___y_965_;
v___y_845_ = v___y_964_;
v___y_846_ = v___x_974_;
goto v___jp_837_;
}
else
{
lean_object* v_run_x27_975_; lean_object* v_inheritedTraceOptions_976_; lean_object* v___f_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_run_x27_975_ = lean_ctor_get(v___x_970_, 1);
v_inheritedTraceOptions_976_ = lean_ctor_get(v___y_968_, 13);
v___f_977_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5);
v___x_978_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_513_);
v___x_979_ = l_Lean_Name_append(v___x_978_, v_cls_513_);
v___x_980_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_976_, v_options_971_, v___x_979_);
lean_dec(v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = l_Lean_trace_profiler;
v___x_982_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_971_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_inc_ref(v_run_x27_975_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
v___x_983_ = lean_apply_9(v_run_x27_975_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
v___y_838_ = v___y_969_;
v___y_839_ = v___y_966_;
v___y_840_ = v___y_967_;
v___y_841_ = v___y_962_;
v___y_842_ = v___y_963_;
v___y_843_ = v___y_968_;
v___y_844_ = v___y_965_;
v___y_845_ = v___y_964_;
v___y_846_ = v___x_983_;
goto v___jp_837_;
}
else
{
lean_inc_ref(v_run_x27_975_);
v___y_909_ = v___y_966_;
v___y_910_ = v___y_967_;
v___y_911_ = v___y_962_;
v___y_912_ = v___x_980_;
v___y_913_ = v_options_971_;
v___y_914_ = v___y_964_;
v___y_915_ = v___f_977_;
v___y_916_ = v_run_x27_975_;
v___y_917_ = v___y_969_;
v___y_918_ = v_hasTrace_972_;
v___y_919_ = v___y_963_;
v___y_920_ = v___y_965_;
v___y_921_ = v___y_968_;
goto v___jp_908_;
}
}
else
{
lean_inc_ref(v_run_x27_975_);
v___y_909_ = v___y_966_;
v___y_910_ = v___y_967_;
v___y_911_ = v___y_962_;
v___y_912_ = v___x_980_;
v___y_913_ = v_options_971_;
v___y_914_ = v___y_964_;
v___y_915_ = v___f_977_;
v___y_916_ = v_run_x27_975_;
v___y_917_ = v___y_969_;
v___y_918_ = v_hasTrace_972_;
v___y_919_ = v___y_963_;
v___y_920_ = v___y_965_;
v___y_921_ = v___y_968_;
goto v___jp_908_;
}
}
}
}
v___jp_984_:
{
if (lean_obj_tag(v___y_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1003_; 
v_a_994_ = lean_ctor_get(v___y_993_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___y_993_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_996_ = v___y_993_;
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___y_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; 
v___x_998_ = lean_unbox(v_a_994_);
lean_dec(v_a_994_);
if (v___x_998_ == 0)
{
lean_del_object(v___x_996_);
v___y_962_ = v___y_985_;
v___y_963_ = v___y_989_;
v___y_964_ = v___y_988_;
v___y_965_ = v___y_986_;
v___y_966_ = v___y_987_;
v___y_967_ = v___y_990_;
v___y_968_ = v___y_992_;
v___y_969_ = v___y_991_;
goto v___jp_961_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
v___x_999_ = lean_box(v_hasTrace_512_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
return v___y_993_;
}
}
v___jp_1004_:
{
lean_object* v___x_1020_; double v___x_1021_; double v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1020_ = lean_io_get_num_heartbeats();
v___x_1021_ = lean_float_of_nat(v___y_1005_);
v___x_1022_ = lean_float_of_nat(v___x_1020_);
v___x_1023_ = lean_box_float(v___x_1021_);
v___x_1024_ = lean_box_float(v___x_1022_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_a_1019_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
lean_inc_ref(v___y_1018_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_1027_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_1009_, v___x_514_, v___y_1015_, v___y_1007_, v___y_1008_, v___y_1018_, v___x_1026_, v___y_1006_, v___y_1014_, v___y_1012_, v___y_1011_, v___y_1013_, v___y_1016_, v___y_1017_, v___y_1010_);
v___y_985_ = v___y_1006_;
v___y_986_ = v___y_1011_;
v___y_987_ = v___y_1013_;
v___y_988_ = v___y_1012_;
v___y_989_ = v___y_1014_;
v___y_990_ = v___y_1016_;
v___y_991_ = v___y_1010_;
v___y_992_ = v___y_1017_;
v___y_993_ = v___x_1027_;
goto v___jp_984_;
}
v___jp_1028_:
{
lean_object* v___x_1044_; double v___x_1045_; double v___x_1046_; double v___x_1047_; double v___x_1048_; double v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1044_ = lean_io_mono_nanos_now();
v___x_1045_ = lean_float_of_nat(v___y_1038_);
v___x_1046_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1047_ = lean_float_div(v___x_1045_, v___x_1046_);
v___x_1048_ = lean_float_of_nat(v___x_1044_);
v___x_1049_ = lean_float_div(v___x_1048_, v___x_1046_);
v___x_1050_ = lean_box_float(v___x_1047_);
v___x_1051_ = lean_box_float(v___x_1049_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_a_1043_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
lean_inc_ref(v___y_1042_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_1054_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_1032_, v___x_514_, v___y_1039_, v___y_1030_, v___y_1031_, v___y_1042_, v___x_1053_, v___y_1029_, v___y_1037_, v___y_1035_, v___y_1034_, v___y_1036_, v___y_1040_, v___y_1041_, v___y_1033_);
v___y_985_ = v___y_1029_;
v___y_986_ = v___y_1034_;
v___y_987_ = v___y_1036_;
v___y_988_ = v___y_1035_;
v___y_989_ = v___y_1037_;
v___y_990_ = v___y_1040_;
v___y_991_ = v___y_1033_;
v___y_992_ = v___y_1041_;
v___y_993_ = v___x_1054_;
goto v___jp_984_;
}
v___jp_1055_:
{
lean_object* v___x_1069_; lean_object* v_a_1070_; uint8_t v___x_1071_; 
v___x_1069_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1059_);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1066_, v___x_515_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_io_mono_nanos_now();
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1062_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1056_);
v___x_1073_ = lean_apply_9(v___y_1060_, v___y_1056_, v___y_1064_, v___y_1062_, v___y_1061_, v___y_1063_, v___y_1065_, v___y_1067_, v___y_1059_, lean_box(0));
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 1);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
v___y_1029_ = v___y_1056_;
v___y_1030_ = v___y_1057_;
v___y_1031_ = v_a_1070_;
v___y_1032_ = v___y_1058_;
v___y_1033_ = v___y_1059_;
v___y_1034_ = v___y_1061_;
v___y_1035_ = v___y_1062_;
v___y_1036_ = v___y_1063_;
v___y_1037_ = v___y_1064_;
v___y_1038_ = v___x_1072_;
v___y_1039_ = v___y_1066_;
v___y_1040_ = v___y_1065_;
v___y_1041_ = v___y_1067_;
v___y_1042_ = v___y_1068_;
v_a_1043_ = v___x_1079_;
goto v___jp_1028_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1073_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1073_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 0);
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
v___y_1029_ = v___y_1056_;
v___y_1030_ = v___y_1057_;
v___y_1031_ = v_a_1070_;
v___y_1032_ = v___y_1058_;
v___y_1033_ = v___y_1059_;
v___y_1034_ = v___y_1061_;
v___y_1035_ = v___y_1062_;
v___y_1036_ = v___y_1063_;
v___y_1037_ = v___y_1064_;
v___y_1038_ = v___x_1072_;
v___y_1039_ = v___y_1066_;
v___y_1040_ = v___y_1065_;
v___y_1041_ = v___y_1067_;
v___y_1042_ = v___y_1068_;
v_a_1043_ = v___x_1087_;
goto v___jp_1028_;
}
}
}
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1062_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1056_);
v___x_1091_ = lean_apply_9(v___y_1060_, v___y_1056_, v___y_1064_, v___y_1062_, v___y_1061_, v___y_1063_, v___y_1065_, v___y_1067_, v___y_1059_, lean_box(0));
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 1);
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
v___y_1005_ = v___x_1090_;
v___y_1006_ = v___y_1056_;
v___y_1007_ = v___y_1057_;
v___y_1008_ = v_a_1070_;
v___y_1009_ = v___y_1058_;
v___y_1010_ = v___y_1059_;
v___y_1011_ = v___y_1061_;
v___y_1012_ = v___y_1062_;
v___y_1013_ = v___y_1063_;
v___y_1014_ = v___y_1064_;
v___y_1015_ = v___y_1066_;
v___y_1016_ = v___y_1065_;
v___y_1017_ = v___y_1067_;
v___y_1018_ = v___y_1068_;
v_a_1019_ = v___x_1097_;
goto v___jp_1004_;
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1091_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1091_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 0);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
v___y_1005_ = v___x_1090_;
v___y_1006_ = v___y_1056_;
v___y_1007_ = v___y_1057_;
v___y_1008_ = v_a_1070_;
v___y_1009_ = v___y_1058_;
v___y_1010_ = v___y_1059_;
v___y_1011_ = v___y_1061_;
v___y_1012_ = v___y_1062_;
v___y_1013_ = v___y_1063_;
v___y_1014_ = v___y_1064_;
v___y_1015_ = v___y_1066_;
v___y_1016_ = v___y_1065_;
v___y_1017_ = v___y_1067_;
v___y_1018_ = v___y_1068_;
v_a_1019_ = v___x_1105_;
goto v___jp_1004_;
}
}
}
}
}
v___jp_1108_:
{
if (lean_obj_tag(v___y_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1141_; 
v_a_1118_ = lean_ctor_get(v___y_1117_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___y_1117_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1120_ = v___y_1117_;
v_isShared_1121_ = v_isSharedCheck_1141_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___y_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1141_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_unbox(v_a_1118_);
lean_dec(v_a_1118_);
if (v___x_1122_ == 0)
{
lean_del_object(v___x_1120_);
if (v_structures_646_ == 0)
{
v___y_962_ = v___y_1109_;
v___y_963_ = v___y_1113_;
v___y_964_ = v___y_1112_;
v___y_965_ = v___y_1110_;
v___y_966_ = v___y_1111_;
v___y_967_ = v___y_1114_;
v___y_968_ = v___y_1116_;
v___y_969_ = v___y_1115_;
goto v___jp_961_;
}
else
{
lean_object* v___x_1123_; lean_object* v_options_1124_; uint8_t v_hasTrace_1125_; 
v___x_1123_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_options_1124_ = lean_ctor_get(v___y_1116_, 2);
v_hasTrace_1125_ = lean_ctor_get_uint8(v_options_1124_, sizeof(void*)*1);
if (v_hasTrace_1125_ == 0)
{
lean_object* v_run_x27_1126_; lean_object* v___x_1127_; 
v_run_x27_1126_ = lean_ctor_get(v___x_1123_, 1);
lean_inc_ref(v_run_x27_1126_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1111_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1112_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1109_);
v___x_1127_ = lean_apply_9(v_run_x27_1126_, v___y_1109_, v___y_1113_, v___y_1112_, v___y_1110_, v___y_1111_, v___y_1114_, v___y_1116_, v___y_1115_, lean_box(0));
v___y_985_ = v___y_1109_;
v___y_986_ = v___y_1110_;
v___y_987_ = v___y_1111_;
v___y_988_ = v___y_1112_;
v___y_989_ = v___y_1113_;
v___y_990_ = v___y_1114_;
v___y_991_ = v___y_1115_;
v___y_992_ = v___y_1116_;
v___y_993_ = v___x_1127_;
goto v___jp_984_;
}
else
{
lean_object* v_run_x27_1128_; lean_object* v_inheritedTraceOptions_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_run_x27_1128_ = lean_ctor_get(v___x_1123_, 1);
v_inheritedTraceOptions_1129_ = lean_ctor_get(v___y_1116_, 13);
v___f_1130_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6);
v___x_1131_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_513_);
v___x_1132_ = l_Lean_Name_append(v___x_1131_, v_cls_513_);
v___x_1133_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1129_, v_options_1124_, v___x_1132_);
lean_dec(v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = l_Lean_trace_profiler;
v___x_1135_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1124_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_inc_ref(v_run_x27_1128_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1111_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1112_);
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1109_);
v___x_1136_ = lean_apply_9(v_run_x27_1128_, v___y_1109_, v___y_1113_, v___y_1112_, v___y_1110_, v___y_1111_, v___y_1114_, v___y_1116_, v___y_1115_, lean_box(0));
v___y_985_ = v___y_1109_;
v___y_986_ = v___y_1110_;
v___y_987_ = v___y_1111_;
v___y_988_ = v___y_1112_;
v___y_989_ = v___y_1113_;
v___y_990_ = v___y_1114_;
v___y_991_ = v___y_1115_;
v___y_992_ = v___y_1116_;
v___y_993_ = v___x_1136_;
goto v___jp_984_;
}
else
{
lean_inc_ref(v_run_x27_1128_);
v___y_1056_ = v___y_1109_;
v___y_1057_ = v___x_1133_;
v___y_1058_ = v_hasTrace_1125_;
v___y_1059_ = v___y_1115_;
v___y_1060_ = v_run_x27_1128_;
v___y_1061_ = v___y_1110_;
v___y_1062_ = v___y_1112_;
v___y_1063_ = v___y_1111_;
v___y_1064_ = v___y_1113_;
v___y_1065_ = v___y_1114_;
v___y_1066_ = v_options_1124_;
v___y_1067_ = v___y_1116_;
v___y_1068_ = v___f_1130_;
goto v___jp_1055_;
}
}
else
{
lean_inc_ref(v_run_x27_1128_);
v___y_1056_ = v___y_1109_;
v___y_1057_ = v___x_1133_;
v___y_1058_ = v_hasTrace_1125_;
v___y_1059_ = v___y_1115_;
v___y_1060_ = v_run_x27_1128_;
v___y_1061_ = v___y_1110_;
v___y_1062_ = v___y_1112_;
v___y_1063_ = v___y_1111_;
v___y_1064_ = v___y_1113_;
v___y_1065_ = v___y_1114_;
v___y_1066_ = v_options_1124_;
v___y_1067_ = v___y_1116_;
v___y_1068_ = v___f_1130_;
goto v___jp_1055_;
}
}
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
v___x_1137_ = lean_box(v_hasTrace_512_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1137_);
v___x_1139_ = v___x_1120_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
return v___y_1117_;
}
}
v___jp_1142_:
{
lean_object* v___x_1158_; double v___x_1159_; double v___x_1160_; double v___x_1161_; double v___x_1162_; double v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1158_ = lean_io_mono_nanos_now();
v___x_1159_ = lean_float_of_nat(v___y_1156_);
v___x_1160_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1161_ = lean_float_div(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_float_of_nat(v___x_1158_);
v___x_1163_ = lean_float_div(v___x_1162_, v___x_1160_);
v___x_1164_ = lean_box_float(v___x_1161_);
v___x_1165_ = lean_box_float(v___x_1163_);
v___x_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1157_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
lean_inc_ref(v___y_1151_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_1168_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_1147_, v___x_514_, v___y_1145_, v___y_1153_, v___y_1150_, v___y_1151_, v___x_1167_, v___y_1143_, v___y_1152_, v___y_1148_, v___y_1146_, v___y_1149_, v___y_1154_, v___y_1155_, v___y_1144_);
v___y_1109_ = v___y_1143_;
v___y_1110_ = v___y_1146_;
v___y_1111_ = v___y_1149_;
v___y_1112_ = v___y_1148_;
v___y_1113_ = v___y_1152_;
v___y_1114_ = v___y_1154_;
v___y_1115_ = v___y_1144_;
v___y_1116_ = v___y_1155_;
v___y_1117_ = v___x_1168_;
goto v___jp_1108_;
}
v___jp_1169_:
{
lean_object* v___x_1185_; double v___x_1186_; double v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1185_ = lean_io_get_num_heartbeats();
v___x_1186_ = lean_float_of_nat(v___y_1174_);
v___x_1187_ = lean_float_of_nat(v___x_1185_);
v___x_1188_ = lean_box_float(v___x_1186_);
v___x_1189_ = lean_box_float(v___x_1187_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1184_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
lean_inc_ref(v___y_1179_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_1192_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_1175_, v___x_514_, v___y_1172_, v___y_1181_, v___y_1178_, v___y_1179_, v___x_1191_, v___y_1170_, v___y_1180_, v___y_1176_, v___y_1173_, v___y_1177_, v___y_1182_, v___y_1183_, v___y_1171_);
v___y_1109_ = v___y_1170_;
v___y_1110_ = v___y_1173_;
v___y_1111_ = v___y_1177_;
v___y_1112_ = v___y_1176_;
v___y_1113_ = v___y_1180_;
v___y_1114_ = v___y_1182_;
v___y_1115_ = v___y_1171_;
v___y_1116_ = v___y_1183_;
v___y_1117_ = v___x_1192_;
goto v___jp_1108_;
}
v___jp_1193_:
{
lean_object* v___x_1207_; lean_object* v_a_1208_; uint8_t v___x_1209_; 
v___x_1207_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1196_);
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1198_, v___x_515_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_io_mono_nanos_now();
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1206_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1199_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1194_);
v___x_1211_ = lean_apply_9(v___y_1195_, v___y_1194_, v___y_1202_, v___y_1199_, v___y_1197_, v___y_1200_, v___y_1204_, v___y_1206_, v___y_1196_, lean_box(0));
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set_tag(v___x_1214_, 1);
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
v___y_1143_ = v___y_1194_;
v___y_1144_ = v___y_1196_;
v___y_1145_ = v___y_1198_;
v___y_1146_ = v___y_1197_;
v___y_1147_ = v___y_1201_;
v___y_1148_ = v___y_1199_;
v___y_1149_ = v___y_1200_;
v___y_1150_ = v_a_1208_;
v___y_1151_ = v___y_1203_;
v___y_1152_ = v___y_1202_;
v___y_1153_ = v___y_1205_;
v___y_1154_ = v___y_1204_;
v___y_1155_ = v___y_1206_;
v___y_1156_ = v___x_1210_;
v_a_1157_ = v___x_1217_;
goto v___jp_1142_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1211_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1211_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 0);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v___y_1143_ = v___y_1194_;
v___y_1144_ = v___y_1196_;
v___y_1145_ = v___y_1198_;
v___y_1146_ = v___y_1197_;
v___y_1147_ = v___y_1201_;
v___y_1148_ = v___y_1199_;
v___y_1149_ = v___y_1200_;
v___y_1150_ = v_a_1208_;
v___y_1151_ = v___y_1203_;
v___y_1152_ = v___y_1202_;
v___y_1153_ = v___y_1205_;
v___y_1154_ = v___y_1204_;
v___y_1155_ = v___y_1206_;
v___y_1156_ = v___x_1210_;
v_a_1157_ = v___x_1225_;
goto v___jp_1142_;
}
}
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1206_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1199_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1194_);
v___x_1229_ = lean_apply_9(v___y_1195_, v___y_1194_, v___y_1202_, v___y_1199_, v___y_1197_, v___y_1200_, v___y_1204_, v___y_1206_, v___y_1196_, lean_box(0));
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set_tag(v___x_1232_, 1);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
v___y_1170_ = v___y_1194_;
v___y_1171_ = v___y_1196_;
v___y_1172_ = v___y_1198_;
v___y_1173_ = v___y_1197_;
v___y_1174_ = v___x_1228_;
v___y_1175_ = v___y_1201_;
v___y_1176_ = v___y_1199_;
v___y_1177_ = v___y_1200_;
v___y_1178_ = v_a_1208_;
v___y_1179_ = v___y_1203_;
v___y_1180_ = v___y_1202_;
v___y_1181_ = v___y_1205_;
v___y_1182_ = v___y_1204_;
v___y_1183_ = v___y_1206_;
v_a_1184_ = v___x_1235_;
goto v___jp_1169_;
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_a_1238_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1229_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1229_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 0);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
v___y_1170_ = v___y_1194_;
v___y_1171_ = v___y_1196_;
v___y_1172_ = v___y_1198_;
v___y_1173_ = v___y_1197_;
v___y_1174_ = v___x_1228_;
v___y_1175_ = v___y_1201_;
v___y_1176_ = v___y_1199_;
v___y_1177_ = v___y_1200_;
v___y_1178_ = v_a_1208_;
v___y_1179_ = v___y_1203_;
v___y_1180_ = v___y_1202_;
v___y_1181_ = v___y_1205_;
v___y_1182_ = v___y_1204_;
v___y_1183_ = v___y_1206_;
v_a_1184_ = v___x_1243_;
goto v___jp_1169_;
}
}
}
}
}
v___jp_1246_:
{
lean_object* v___x_1255_; lean_object* v_options_1256_; uint8_t v_hasTrace_1257_; 
v___x_1255_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v_options_1256_ = lean_ctor_get(v___y_1253_, 2);
v_hasTrace_1257_ = lean_ctor_get_uint8(v_options_1256_, sizeof(void*)*1);
if (v_hasTrace_1257_ == 0)
{
lean_object* v_run_x27_1258_; lean_object* v___x_1259_; 
v_run_x27_1258_ = lean_ctor_get(v___x_1255_, 1);
lean_inc_ref(v_run_x27_1258_);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
v___x_1259_ = lean_apply_9(v_run_x27_1258_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, lean_box(0));
v___y_1109_ = v___y_1247_;
v___y_1110_ = v___y_1250_;
v___y_1111_ = v___y_1251_;
v___y_1112_ = v___y_1249_;
v___y_1113_ = v___y_1248_;
v___y_1114_ = v___y_1252_;
v___y_1115_ = v___y_1254_;
v___y_1116_ = v___y_1253_;
v___y_1117_ = v___x_1259_;
goto v___jp_1108_;
}
else
{
lean_object* v_run_x27_1260_; lean_object* v_inheritedTraceOptions_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_run_x27_1260_ = lean_ctor_get(v___x_1255_, 1);
v_inheritedTraceOptions_1261_ = lean_ctor_get(v___y_1253_, 13);
v___f_1262_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7);
v___x_1263_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_513_);
v___x_1264_ = l_Lean_Name_append(v___x_1263_, v_cls_513_);
v___x_1265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1261_, v_options_1256_, v___x_1264_);
lean_dec(v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = l_Lean_trace_profiler;
v___x_1267_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1256_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_inc_ref(v_run_x27_1260_);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
v___x_1268_ = lean_apply_9(v_run_x27_1260_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, lean_box(0));
v___y_1109_ = v___y_1247_;
v___y_1110_ = v___y_1250_;
v___y_1111_ = v___y_1251_;
v___y_1112_ = v___y_1249_;
v___y_1113_ = v___y_1248_;
v___y_1114_ = v___y_1252_;
v___y_1115_ = v___y_1254_;
v___y_1116_ = v___y_1253_;
v___y_1117_ = v___x_1268_;
goto v___jp_1108_;
}
else
{
lean_inc_ref(v_run_x27_1260_);
v___y_1194_ = v___y_1247_;
v___y_1195_ = v_run_x27_1260_;
v___y_1196_ = v___y_1254_;
v___y_1197_ = v___y_1250_;
v___y_1198_ = v_options_1256_;
v___y_1199_ = v___y_1249_;
v___y_1200_ = v___y_1251_;
v___y_1201_ = v_hasTrace_1257_;
v___y_1202_ = v___y_1248_;
v___y_1203_ = v___f_1262_;
v___y_1204_ = v___y_1252_;
v___y_1205_ = v___x_1265_;
v___y_1206_ = v___y_1253_;
goto v___jp_1193_;
}
}
else
{
lean_inc_ref(v_run_x27_1260_);
v___y_1194_ = v___y_1247_;
v___y_1195_ = v_run_x27_1260_;
v___y_1196_ = v___y_1254_;
v___y_1197_ = v___y_1250_;
v___y_1198_ = v_options_1256_;
v___y_1199_ = v___y_1249_;
v___y_1200_ = v___y_1251_;
v___y_1201_ = v_hasTrace_1257_;
v___y_1202_ = v___y_1248_;
v___y_1203_ = v___f_1262_;
v___y_1204_ = v___y_1252_;
v___y_1205_ = v___x_1265_;
v___y_1206_ = v___y_1253_;
goto v___jp_1193_;
}
}
}
v___jp_1269_:
{
if (lean_obj_tag(v___y_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1280_; 
v_a_1271_ = lean_ctor_get(v___y_1270_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___y_1270_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1273_ = v___y_1270_;
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___y_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1280_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_unbox(v_a_1271_);
lean_dec(v_a_1271_);
if (v___x_1275_ == 0)
{
lean_del_object(v___x_1273_);
v___y_1247_ = v___y_517_;
v___y_1248_ = v___y_518_;
v___y_1249_ = v___y_519_;
v___y_1250_ = v___y_520_;
v___y_1251_ = v___y_521_;
v___y_1252_ = v___y_522_;
v___y_1253_ = v___y_523_;
v___y_1254_ = v___y_524_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
v___x_1276_ = lean_box(v_hasTrace_512_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_dec_ref(v___x_514_);
lean_dec(v_cls_513_);
return v___y_1270_;
}
}
v___jp_1281_:
{
lean_object* v___x_1289_; double v___x_1290_; double v___x_1291_; double v___x_1292_; double v___x_1293_; double v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1289_ = lean_io_mono_nanos_now();
v___x_1290_ = lean_float_of_nat(v___y_1283_);
v___x_1291_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1292_ = lean_float_div(v___x_1290_, v___x_1291_);
v___x_1293_ = lean_float_of_nat(v___x_1289_);
v___x_1294_ = lean_float_div(v___x_1293_, v___x_1291_);
v___x_1295_ = lean_box_float(v___x_1292_);
v___x_1296_ = lean_box_float(v___x_1294_);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_a_1288_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
lean_inc_ref(v___y_1286_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_1299_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_1287_, v___x_514_, v___y_1282_, v___y_1285_, v___y_1284_, v___y_1286_, v___x_1298_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
v___y_1270_ = v___x_1299_;
goto v___jp_1269_;
}
v___jp_1300_:
{
lean_object* v___x_1308_; double v___x_1309_; double v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1308_ = lean_io_get_num_heartbeats();
v___x_1309_ = lean_float_of_nat(v___y_1301_);
v___x_1310_ = lean_float_of_nat(v___x_1308_);
v___x_1311_ = lean_box_float(v___x_1309_);
v___x_1312_ = lean_box_float(v___x_1310_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v_a_1307_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
lean_inc_ref(v___y_1305_);
lean_inc_ref(v___x_514_);
lean_inc(v_cls_513_);
v___x_1315_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_513_, v___y_1306_, v___x_514_, v___y_1302_, v___y_1304_, v___y_1303_, v___y_1305_, v___x_1314_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
v___y_1270_ = v___x_1315_;
goto v___jp_1269_;
}
v___jp_1316_:
{
lean_object* v___x_1322_; lean_object* v_a_1323_; uint8_t v___x_1324_; 
v___x_1322_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_524_);
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref(v___x_1322_);
v___x_1324_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1318_, v___x_515_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_io_mono_nanos_now();
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
v___x_1326_ = lean_apply_9(v___y_1317_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, lean_box(0));
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 1);
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
v___y_1282_ = v___y_1318_;
v___y_1283_ = v___x_1325_;
v___y_1284_ = v_a_1323_;
v___y_1285_ = v___y_1319_;
v___y_1286_ = v___y_1320_;
v___y_1287_ = v___y_1321_;
v_a_1288_ = v___x_1332_;
goto v___jp_1281_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_a_1335_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1326_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1326_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 0);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
v___y_1282_ = v___y_1318_;
v___y_1283_ = v___x_1325_;
v___y_1284_ = v_a_1323_;
v___y_1285_ = v___y_1319_;
v___y_1286_ = v___y_1320_;
v___y_1287_ = v___y_1321_;
v_a_1288_ = v___x_1340_;
goto v___jp_1281_;
}
}
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_io_get_num_heartbeats();
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
v___x_1344_ = lean_apply_9(v___y_1317_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, lean_box(0));
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 1);
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v___y_1301_ = v___x_1343_;
v___y_1302_ = v___y_1318_;
v___y_1303_ = v_a_1323_;
v___y_1304_ = v___y_1319_;
v___y_1305_ = v___y_1320_;
v___y_1306_ = v___y_1321_;
v_a_1307_ = v___x_1350_;
goto v___jp_1300_;
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1344_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1344_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 0);
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
v___y_1301_ = v___x_1343_;
v___y_1302_ = v___y_1318_;
v___y_1303_ = v_a_1323_;
v___y_1304_ = v___y_1319_;
v___y_1305_ = v___y_1320_;
v___y_1306_ = v___y_1321_;
v_a_1307_ = v___x_1358_;
goto v___jp_1300_;
}
}
}
}
}
v___jp_1361_:
{
lean_object* v___x_1362_; lean_object* v_options_1363_; uint8_t v_hasTrace_1364_; 
v___x_1362_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_options_1363_ = lean_ctor_get(v___y_523_, 2);
v_hasTrace_1364_ = lean_ctor_get_uint8(v_options_1363_, sizeof(void*)*1);
if (v_hasTrace_1364_ == 0)
{
lean_object* v_run_x27_1365_; lean_object* v___x_1366_; 
v_run_x27_1365_ = lean_ctor_get(v___x_1362_, 1);
lean_inc_ref(v_run_x27_1365_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
v___x_1366_ = lean_apply_9(v_run_x27_1365_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, lean_box(0));
v___y_1270_ = v___x_1366_;
goto v___jp_1269_;
}
else
{
lean_object* v_run_x27_1367_; lean_object* v_inheritedTraceOptions_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_run_x27_1367_ = lean_ctor_get(v___x_1362_, 1);
v_inheritedTraceOptions_1368_ = lean_ctor_get(v___y_523_, 13);
v___f_1369_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8);
v___x_1370_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_513_);
v___x_1371_ = l_Lean_Name_append(v___x_1370_, v_cls_513_);
v___x_1372_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1368_, v_options_1363_, v___x_1371_);
lean_dec(v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = l_Lean_trace_profiler;
v___x_1374_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1363_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_inc_ref(v_run_x27_1367_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
v___x_1375_ = lean_apply_9(v_run_x27_1367_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, lean_box(0));
v___y_1270_ = v___x_1375_;
goto v___jp_1269_;
}
else
{
lean_inc_ref(v_run_x27_1367_);
v___y_1317_ = v_run_x27_1367_;
v___y_1318_ = v_options_1363_;
v___y_1319_ = v___x_1372_;
v___y_1320_ = v___f_1369_;
v___y_1321_ = v_hasTrace_1364_;
goto v___jp_1316_;
}
}
else
{
lean_inc_ref(v_run_x27_1367_);
v___y_1317_ = v_run_x27_1367_;
v___y_1318_ = v_options_1363_;
v___y_1319_ = v___x_1372_;
v___y_1320_ = v___f_1369_;
v___y_1321_ = v_hasTrace_1364_;
goto v___jp_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___boxed(lean_object* v___x_1376_, lean_object* v_hasTrace_1377_, lean_object* v_cls_1378_, lean_object* v___x_1379_, lean_object* v___x_1380_, lean_object* v_____r_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v___x_477267__boxed_1391_; uint8_t v_hasTrace_boxed_1392_; lean_object* v_res_1393_; 
v___x_477267__boxed_1391_ = lean_unbox(v___x_1376_);
v_hasTrace_boxed_1392_ = lean_unbox(v_hasTrace_1377_);
v_res_1393_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8(v___x_477267__boxed_1391_, v_hasTrace_boxed_1392_, v_cls_1378_, v___x_1379_, v___x_1380_, v_____r_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v___x_1380_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9(uint8_t v___x_1394_, lean_object* v_cls_1395_, lean_object* v___x_1396_, lean_object* v___x_1397_, lean_object* v_____r_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v___y_1409_; lean_object* v___y_1410_; uint8_t v___y_1426_; lean_object* v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; uint8_t v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v_a_1441_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; uint8_t v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v_a_1469_; lean_object* v___y_1479_; uint8_t v___y_1480_; lean_object* v___y_1481_; uint8_t v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; uint8_t v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; uint8_t v_structures_1532_; uint8_t v_fixedInt_1533_; uint8_t v_enums_1534_; uint8_t v_shortCircuit_1535_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; uint8_t v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; uint8_t v___y_1610_; lean_object* v___y_1611_; lean_object* v_a_1612_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; uint8_t v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; uint8_t v___y_1637_; lean_object* v___y_1638_; lean_object* v_a_1639_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; uint8_t v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; uint8_t v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; uint8_t v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; uint8_t v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v_a_1759_; lean_object* v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; uint8_t v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v_a_1783_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; uint8_t v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1902_; uint8_t v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v_a_1906_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; uint8_t v___y_1926_; uint8_t v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v_a_1930_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; uint8_t v___y_1952_; uint8_t v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; uint8_t v___y_2040_; uint8_t v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v_a_2044_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; uint8_t v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v_a_2071_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; uint8_t v___y_2090_; uint8_t v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2157_; lean_object* v___y_2169_; lean_object* v___y_2170_; uint8_t v___y_2171_; lean_object* v___y_2172_; uint8_t v___y_2173_; lean_object* v___y_2174_; lean_object* v_a_2175_; lean_object* v___y_2188_; lean_object* v___y_2189_; uint8_t v___y_2190_; uint8_t v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v_a_2194_; lean_object* v___y_2204_; uint8_t v___y_2205_; uint8_t v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; uint8_t v___y_2249_; 
v_structures_1532_ = lean_ctor_get_uint8(v___y_1399_, sizeof(void*)*2 + 5);
v_fixedInt_1533_ = lean_ctor_get_uint8(v___y_1399_, sizeof(void*)*2 + 6);
v_enums_1534_ = lean_ctor_get_uint8(v___y_1399_, sizeof(void*)*2 + 7);
v_shortCircuit_1535_ = lean_ctor_get_uint8(v___y_1399_, sizeof(void*)*2 + 9);
if (v_structures_1532_ == 0)
{
v___y_2249_ = v_enums_1534_;
goto v___jp_2248_;
}
else
{
v___y_2249_ = v___x_1394_;
goto v___jp_2248_;
}
v___jp_1408_:
{
if (lean_obj_tag(v___y_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1424_; 
v_a_1411_ = lean_ctor_get(v___y_1410_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___y_1410_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1413_ = v___y_1410_;
v_isShared_1414_ = v_isSharedCheck_1424_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___y_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1424_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_unbox(v_a_1411_);
lean_dec(v_a_1411_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_box(v___y_1409_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1416_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_box(v___x_1394_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1420_);
v___x_1422_ = v___x_1413_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
return v___y_1410_;
}
}
v___jp_1425_:
{
lean_object* v___x_1442_; double v___x_1443_; double v___x_1444_; double v___x_1445_; double v___x_1446_; double v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1442_ = lean_io_mono_nanos_now();
v___x_1443_ = lean_float_of_nat(v___y_1436_);
v___x_1444_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1445_ = lean_float_div(v___x_1443_, v___x_1444_);
v___x_1446_ = lean_float_of_nat(v___x_1442_);
v___x_1447_ = lean_float_div(v___x_1446_, v___x_1444_);
v___x_1448_ = lean_box_float(v___x_1445_);
v___x_1449_ = lean_box_float(v___x_1447_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1441_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
lean_inc_ref(v___y_1440_);
v___x_1452_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_1428_, v___x_1396_, v___y_1430_, v___y_1426_, v___y_1437_, v___y_1440_, v___x_1451_, v___y_1429_, v___y_1438_, v___y_1434_, v___y_1427_, v___y_1432_, v___y_1431_, v___y_1439_, v___y_1433_);
v___y_1409_ = v___y_1435_;
v___y_1410_ = v___x_1452_;
goto v___jp_1408_;
}
v___jp_1453_:
{
lean_object* v___x_1470_; double v___x_1471_; double v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1470_ = lean_io_get_num_heartbeats();
v___x_1471_ = lean_float_of_nat(v___y_1454_);
v___x_1472_ = lean_float_of_nat(v___x_1470_);
v___x_1473_ = lean_box_float(v___x_1471_);
v___x_1474_ = lean_box_float(v___x_1472_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1473_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_a_1469_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
lean_inc_ref(v___y_1468_);
v___x_1477_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_1457_, v___x_1396_, v___y_1459_, v___y_1455_, v___y_1465_, v___y_1468_, v___x_1476_, v___y_1458_, v___y_1466_, v___y_1463_, v___y_1456_, v___y_1461_, v___y_1460_, v___y_1467_, v___y_1462_);
v___y_1409_ = v___y_1464_;
v___y_1410_ = v___x_1477_;
goto v___jp_1408_;
}
v___jp_1478_:
{
lean_object* v___x_1493_; lean_object* v_a_1494_; uint8_t v___x_1495_; 
v___x_1493_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1486_);
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1484_, v___x_1397_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_io_mono_nanos_now();
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1490_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1485_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1481_);
v___x_1497_ = lean_apply_9(v___y_1492_, v___y_1481_, v___y_1489_, v___y_1487_, v___y_1479_, v___y_1485_, v___y_1483_, v___y_1490_, v___y_1486_, lean_box(0));
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set_tag(v___x_1500_, 1);
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
v___y_1426_ = v___y_1480_;
v___y_1427_ = v___y_1479_;
v___y_1428_ = v___y_1482_;
v___y_1429_ = v___y_1481_;
v___y_1430_ = v___y_1484_;
v___y_1431_ = v___y_1483_;
v___y_1432_ = v___y_1485_;
v___y_1433_ = v___y_1486_;
v___y_1434_ = v___y_1487_;
v___y_1435_ = v___y_1488_;
v___y_1436_ = v___x_1496_;
v___y_1437_ = v_a_1494_;
v___y_1438_ = v___y_1489_;
v___y_1439_ = v___y_1490_;
v___y_1440_ = v___y_1491_;
v_a_1441_ = v___x_1503_;
goto v___jp_1425_;
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_a_1506_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1497_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1497_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
v___y_1426_ = v___y_1480_;
v___y_1427_ = v___y_1479_;
v___y_1428_ = v___y_1482_;
v___y_1429_ = v___y_1481_;
v___y_1430_ = v___y_1484_;
v___y_1431_ = v___y_1483_;
v___y_1432_ = v___y_1485_;
v___y_1433_ = v___y_1486_;
v___y_1434_ = v___y_1487_;
v___y_1435_ = v___y_1488_;
v___y_1436_ = v___x_1496_;
v___y_1437_ = v_a_1494_;
v___y_1438_ = v___y_1489_;
v___y_1439_ = v___y_1490_;
v___y_1440_ = v___y_1491_;
v_a_1441_ = v___x_1511_;
goto v___jp_1425_;
}
}
}
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1490_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1485_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1487_);
lean_inc(v___y_1489_);
lean_inc_ref(v___y_1481_);
v___x_1515_ = lean_apply_9(v___y_1492_, v___y_1481_, v___y_1489_, v___y_1487_, v___y_1479_, v___y_1485_, v___y_1483_, v___y_1490_, v___y_1486_, lean_box(0));
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 1);
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
v___y_1454_ = v___x_1514_;
v___y_1455_ = v___y_1480_;
v___y_1456_ = v___y_1479_;
v___y_1457_ = v___y_1482_;
v___y_1458_ = v___y_1481_;
v___y_1459_ = v___y_1484_;
v___y_1460_ = v___y_1483_;
v___y_1461_ = v___y_1485_;
v___y_1462_ = v___y_1486_;
v___y_1463_ = v___y_1487_;
v___y_1464_ = v___y_1488_;
v___y_1465_ = v_a_1494_;
v___y_1466_ = v___y_1489_;
v___y_1467_ = v___y_1490_;
v___y_1468_ = v___y_1491_;
v_a_1469_ = v___x_1521_;
goto v___jp_1453_;
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_a_1524_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1515_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1515_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 0);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
v___y_1454_ = v___x_1514_;
v___y_1455_ = v___y_1480_;
v___y_1456_ = v___y_1479_;
v___y_1457_ = v___y_1482_;
v___y_1458_ = v___y_1481_;
v___y_1459_ = v___y_1484_;
v___y_1460_ = v___y_1483_;
v___y_1461_ = v___y_1485_;
v___y_1462_ = v___y_1486_;
v___y_1463_ = v___y_1487_;
v___y_1464_ = v___y_1488_;
v___y_1465_ = v_a_1494_;
v___y_1466_ = v___y_1489_;
v___y_1467_ = v___y_1490_;
v___y_1468_ = v___y_1491_;
v_a_1469_ = v___x_1529_;
goto v___jp_1453_;
}
}
}
}
}
v___jp_1536_:
{
lean_object* v___x_1545_; lean_object* v_a_1546_; lean_object* v___x_1547_; 
v___x_1545_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_1537_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_1546_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v_a_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; uint8_t v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
v___x_1549_ = lean_unbox(v_a_1548_);
if (v___x_1549_ == 0)
{
if (v_shortCircuit_1535_ == 0)
{
lean_dec(v_a_1548_);
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
return v___x_1547_;
}
else
{
lean_object* v___x_1550_; lean_object* v_options_1551_; uint8_t v_hasTrace_1552_; 
lean_dec_ref_known(v___x_1547_, 1);
v___x_1550_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_options_1551_ = lean_ctor_get(v___y_1543_, 2);
v_hasTrace_1552_ = lean_ctor_get_uint8(v_options_1551_, sizeof(void*)*1);
if (v_hasTrace_1552_ == 0)
{
lean_object* v_run_x27_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
v_run_x27_1553_ = lean_ctor_get(v___x_1550_, 1);
lean_inc_ref(v_run_x27_1553_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
v___x_1554_ = lean_apply_9(v_run_x27_1553_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, lean_box(0));
v___x_1555_ = lean_unbox(v_a_1548_);
lean_dec(v_a_1548_);
v___y_1409_ = v___x_1555_;
v___y_1410_ = v___x_1554_;
goto v___jp_1408_;
}
else
{
lean_object* v_run_x27_1556_; lean_object* v_inheritedTraceOptions_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v_run_x27_1556_ = lean_ctor_get(v___x_1550_, 1);
v_inheritedTraceOptions_1557_ = lean_ctor_get(v___y_1543_, 13);
v___f_1558_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1);
v___x_1559_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1395_);
v___x_1560_ = l_Lean_Name_append(v___x_1559_, v_cls_1395_);
v___x_1561_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1557_, v_options_1551_, v___x_1560_);
lean_dec(v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = l_Lean_trace_profiler;
v___x_1563_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1551_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
lean_inc_ref(v_run_x27_1556_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc_ref(v___y_1537_);
v___x_1564_ = lean_apply_9(v_run_x27_1556_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, lean_box(0));
v___x_1565_ = lean_unbox(v_a_1548_);
lean_dec(v_a_1548_);
v___y_1409_ = v___x_1565_;
v___y_1410_ = v___x_1564_;
goto v___jp_1408_;
}
else
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_unbox(v_a_1548_);
lean_dec(v_a_1548_);
lean_inc_ref(v_run_x27_1556_);
v___y_1479_ = v___y_1540_;
v___y_1480_ = v___x_1561_;
v___y_1481_ = v___y_1537_;
v___y_1482_ = v_hasTrace_1552_;
v___y_1483_ = v___y_1542_;
v___y_1484_ = v_options_1551_;
v___y_1485_ = v___y_1541_;
v___y_1486_ = v___y_1544_;
v___y_1487_ = v___y_1539_;
v___y_1488_ = v___x_1566_;
v___y_1489_ = v___y_1538_;
v___y_1490_ = v___y_1543_;
v___y_1491_ = v___f_1558_;
v___y_1492_ = v_run_x27_1556_;
goto v___jp_1478_;
}
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_unbox(v_a_1548_);
lean_dec(v_a_1548_);
lean_inc_ref(v_run_x27_1556_);
v___y_1479_ = v___y_1540_;
v___y_1480_ = v___x_1561_;
v___y_1481_ = v___y_1537_;
v___y_1482_ = v_hasTrace_1552_;
v___y_1483_ = v___y_1542_;
v___y_1484_ = v_options_1551_;
v___y_1485_ = v___y_1541_;
v___y_1486_ = v___y_1544_;
v___y_1487_ = v___y_1539_;
v___y_1488_ = v___x_1567_;
v___y_1489_ = v___y_1538_;
v___y_1490_ = v___y_1543_;
v___y_1491_ = v___f_1558_;
v___y_1492_ = v_run_x27_1556_;
goto v___jp_1478_;
}
}
}
}
else
{
lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_a_1548_);
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v___x_1547_, 0);
lean_dec(v_unused_1576_);
v___x_1569_ = v___x_1547_;
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v___x_1547_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_box(v___x_1394_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
return v___x_1547_;
}
}
v___jp_1577_:
{
if (lean_obj_tag(v___y_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1596_; 
v_a_1587_ = lean_ctor_get(v___y_1586_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___y_1586_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1589_ = v___y_1586_;
v_isShared_1590_ = v_isSharedCheck_1596_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___y_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1596_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_unbox(v_a_1587_);
lean_dec(v_a_1587_);
if (v___x_1591_ == 0)
{
lean_del_object(v___x_1589_);
v___y_1537_ = v___y_1582_;
v___y_1538_ = v___y_1579_;
v___y_1539_ = v___y_1578_;
v___y_1540_ = v___y_1583_;
v___y_1541_ = v___y_1584_;
v___y_1542_ = v___y_1581_;
v___y_1543_ = v___y_1585_;
v___y_1544_ = v___y_1580_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
v___x_1592_ = lean_box(v___x_1394_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1592_);
v___x_1594_ = v___x_1589_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
return v___y_1586_;
}
}
v___jp_1597_:
{
lean_object* v___x_1613_; double v___x_1614_; double v___x_1615_; double v___x_1616_; double v___x_1617_; double v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1613_ = lean_io_mono_nanos_now();
v___x_1614_ = lean_float_of_nat(v___y_1604_);
v___x_1615_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1616_ = lean_float_div(v___x_1614_, v___x_1615_);
v___x_1617_ = lean_float_of_nat(v___x_1613_);
v___x_1618_ = lean_float_div(v___x_1617_, v___x_1615_);
v___x_1619_ = lean_box_float(v___x_1616_);
v___x_1620_ = lean_box_float(v___x_1618_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v_a_1612_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
lean_inc_ref(v___y_1600_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_1623_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_1610_, v___x_1396_, v___y_1611_, v___y_1606_, v___y_1602_, v___y_1600_, v___x_1622_, v___y_1608_, v___y_1607_, v___y_1598_, v___y_1609_, v___y_1603_, v___y_1601_, v___y_1605_, v___y_1599_);
v___y_1578_ = v___y_1598_;
v___y_1579_ = v___y_1607_;
v___y_1580_ = v___y_1599_;
v___y_1581_ = v___y_1601_;
v___y_1582_ = v___y_1608_;
v___y_1583_ = v___y_1609_;
v___y_1584_ = v___y_1603_;
v___y_1585_ = v___y_1605_;
v___y_1586_ = v___x_1623_;
goto v___jp_1577_;
}
v___jp_1624_:
{
lean_object* v___x_1640_; double v___x_1641_; double v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1640_ = lean_io_get_num_heartbeats();
v___x_1641_ = lean_float_of_nat(v___y_1629_);
v___x_1642_ = lean_float_of_nat(v___x_1640_);
v___x_1643_ = lean_box_float(v___x_1641_);
v___x_1644_ = lean_box_float(v___x_1642_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_a_1639_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
lean_inc_ref(v___y_1627_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_1647_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_1637_, v___x_1396_, v___y_1638_, v___y_1633_, v___y_1630_, v___y_1627_, v___x_1646_, v___y_1635_, v___y_1634_, v___y_1625_, v___y_1636_, v___y_1631_, v___y_1628_, v___y_1632_, v___y_1626_);
v___y_1578_ = v___y_1625_;
v___y_1579_ = v___y_1634_;
v___y_1580_ = v___y_1626_;
v___y_1581_ = v___y_1628_;
v___y_1582_ = v___y_1635_;
v___y_1583_ = v___y_1636_;
v___y_1584_ = v___y_1631_;
v___y_1585_ = v___y_1632_;
v___y_1586_ = v___x_1647_;
goto v___jp_1577_;
}
v___jp_1648_:
{
lean_object* v___x_1662_; lean_object* v_a_1663_; uint8_t v___x_1664_; 
v___x_1662_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1651_);
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref(v___x_1662_);
v___x_1664_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1661_, v___x_1397_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_io_mono_nanos_now();
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1658_);
v___x_1666_ = lean_apply_9(v___y_1653_, v___y_1658_, v___y_1657_, v___y_1649_, v___y_1659_, v___y_1654_, v___y_1650_, v___y_1655_, v___y_1651_, lean_box(0));
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 1);
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
v___y_1598_ = v___y_1649_;
v___y_1599_ = v___y_1651_;
v___y_1600_ = v___y_1652_;
v___y_1601_ = v___y_1650_;
v___y_1602_ = v_a_1663_;
v___y_1603_ = v___y_1654_;
v___y_1604_ = v___x_1665_;
v___y_1605_ = v___y_1655_;
v___y_1606_ = v___y_1656_;
v___y_1607_ = v___y_1657_;
v___y_1608_ = v___y_1658_;
v___y_1609_ = v___y_1659_;
v___y_1610_ = v___y_1660_;
v___y_1611_ = v___y_1661_;
v_a_1612_ = v___x_1672_;
goto v___jp_1597_;
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1666_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1666_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 0);
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
v___y_1598_ = v___y_1649_;
v___y_1599_ = v___y_1651_;
v___y_1600_ = v___y_1652_;
v___y_1601_ = v___y_1650_;
v___y_1602_ = v_a_1663_;
v___y_1603_ = v___y_1654_;
v___y_1604_ = v___x_1665_;
v___y_1605_ = v___y_1655_;
v___y_1606_ = v___y_1656_;
v___y_1607_ = v___y_1657_;
v___y_1608_ = v___y_1658_;
v___y_1609_ = v___y_1659_;
v___y_1610_ = v___y_1660_;
v___y_1611_ = v___y_1661_;
v_a_1612_ = v___x_1680_;
goto v___jp_1597_;
}
}
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1658_);
v___x_1684_ = lean_apply_9(v___y_1653_, v___y_1658_, v___y_1657_, v___y_1649_, v___y_1659_, v___y_1654_, v___y_1650_, v___y_1655_, v___y_1651_, lean_box(0));
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 1);
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
v___y_1625_ = v___y_1649_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1650_;
v___y_1629_ = v___x_1683_;
v___y_1630_ = v_a_1663_;
v___y_1631_ = v___y_1654_;
v___y_1632_ = v___y_1655_;
v___y_1633_ = v___y_1656_;
v___y_1634_ = v___y_1657_;
v___y_1635_ = v___y_1658_;
v___y_1636_ = v___y_1659_;
v___y_1637_ = v___y_1660_;
v___y_1638_ = v___y_1661_;
v_a_1639_ = v___x_1690_;
goto v___jp_1624_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1684_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1684_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 0);
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
v___y_1625_ = v___y_1649_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1650_;
v___y_1629_ = v___x_1683_;
v___y_1630_ = v_a_1663_;
v___y_1631_ = v___y_1654_;
v___y_1632_ = v___y_1655_;
v___y_1633_ = v___y_1656_;
v___y_1634_ = v___y_1657_;
v___y_1635_ = v___y_1658_;
v___y_1636_ = v___y_1659_;
v___y_1637_ = v___y_1660_;
v___y_1638_ = v___y_1661_;
v_a_1639_ = v___x_1698_;
goto v___jp_1624_;
}
}
}
}
}
v___jp_1701_:
{
if (v_fixedInt_1533_ == 0)
{
v___y_1537_ = v___y_1702_;
v___y_1538_ = v___y_1703_;
v___y_1539_ = v___y_1704_;
v___y_1540_ = v___y_1705_;
v___y_1541_ = v___y_1706_;
v___y_1542_ = v___y_1707_;
v___y_1543_ = v___y_1708_;
v___y_1544_ = v___y_1709_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1710_; lean_object* v_options_1711_; uint8_t v_hasTrace_1712_; 
v___x_1710_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_options_1711_ = lean_ctor_get(v___y_1708_, 2);
v_hasTrace_1712_ = lean_ctor_get_uint8(v_options_1711_, sizeof(void*)*1);
if (v_hasTrace_1712_ == 0)
{
lean_object* v_run_x27_1713_; lean_object* v___x_1714_; 
v_run_x27_1713_ = lean_ctor_get(v___x_1710_, 1);
lean_inc_ref(v_run_x27_1713_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
v___x_1714_ = lean_apply_9(v_run_x27_1713_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, lean_box(0));
v___y_1578_ = v___y_1704_;
v___y_1579_ = v___y_1703_;
v___y_1580_ = v___y_1709_;
v___y_1581_ = v___y_1707_;
v___y_1582_ = v___y_1702_;
v___y_1583_ = v___y_1705_;
v___y_1584_ = v___y_1706_;
v___y_1585_ = v___y_1708_;
v___y_1586_ = v___x_1714_;
goto v___jp_1577_;
}
else
{
lean_object* v_run_x27_1715_; lean_object* v_inheritedTraceOptions_1716_; lean_object* v___f_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v_run_x27_1715_ = lean_ctor_get(v___x_1710_, 1);
v_inheritedTraceOptions_1716_ = lean_ctor_get(v___y_1708_, 13);
v___f_1717_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4);
v___x_1718_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1395_);
v___x_1719_ = l_Lean_Name_append(v___x_1718_, v_cls_1395_);
v___x_1720_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1716_, v_options_1711_, v___x_1719_);
lean_dec(v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1721_ = l_Lean_trace_profiler;
v___x_1722_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1711_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; 
lean_inc_ref(v_run_x27_1715_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
v___x_1723_ = lean_apply_9(v_run_x27_1715_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, lean_box(0));
v___y_1578_ = v___y_1704_;
v___y_1579_ = v___y_1703_;
v___y_1580_ = v___y_1709_;
v___y_1581_ = v___y_1707_;
v___y_1582_ = v___y_1702_;
v___y_1583_ = v___y_1705_;
v___y_1584_ = v___y_1706_;
v___y_1585_ = v___y_1708_;
v___y_1586_ = v___x_1723_;
goto v___jp_1577_;
}
else
{
lean_inc_ref(v_run_x27_1715_);
v___y_1649_ = v___y_1704_;
v___y_1650_ = v___y_1707_;
v___y_1651_ = v___y_1709_;
v___y_1652_ = v___f_1717_;
v___y_1653_ = v_run_x27_1715_;
v___y_1654_ = v___y_1706_;
v___y_1655_ = v___y_1708_;
v___y_1656_ = v___x_1720_;
v___y_1657_ = v___y_1703_;
v___y_1658_ = v___y_1702_;
v___y_1659_ = v___y_1705_;
v___y_1660_ = v_hasTrace_1712_;
v___y_1661_ = v_options_1711_;
goto v___jp_1648_;
}
}
else
{
lean_inc_ref(v_run_x27_1715_);
v___y_1649_ = v___y_1704_;
v___y_1650_ = v___y_1707_;
v___y_1651_ = v___y_1709_;
v___y_1652_ = v___f_1717_;
v___y_1653_ = v_run_x27_1715_;
v___y_1654_ = v___y_1706_;
v___y_1655_ = v___y_1708_;
v___y_1656_ = v___x_1720_;
v___y_1657_ = v___y_1703_;
v___y_1658_ = v___y_1702_;
v___y_1659_ = v___y_1705_;
v___y_1660_ = v_hasTrace_1712_;
v___y_1661_ = v_options_1711_;
goto v___jp_1648_;
}
}
}
}
v___jp_1724_:
{
if (lean_obj_tag(v___y_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1743_; 
v_a_1734_ = lean_ctor_get(v___y_1733_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___y_1733_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1736_ = v___y_1733_;
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___y_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_unbox(v_a_1734_);
lean_dec(v_a_1734_);
if (v___x_1738_ == 0)
{
lean_del_object(v___x_1736_);
v___y_1702_ = v___y_1729_;
v___y_1703_ = v___y_1730_;
v___y_1704_ = v___y_1731_;
v___y_1705_ = v___y_1732_;
v___y_1706_ = v___y_1728_;
v___y_1707_ = v___y_1726_;
v___y_1708_ = v___y_1727_;
v___y_1709_ = v___y_1725_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
v___x_1739_ = lean_box(v___x_1394_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1739_);
v___x_1741_ = v___x_1736_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
return v___y_1733_;
}
}
v___jp_1744_:
{
lean_object* v___x_1760_; double v___x_1761_; double v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1760_ = lean_io_get_num_heartbeats();
v___x_1761_ = lean_float_of_nat(v___y_1746_);
v___x_1762_ = lean_float_of_nat(v___x_1760_);
v___x_1763_ = lean_box_float(v___x_1761_);
v___x_1764_ = lean_box_float(v___x_1762_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_a_1759_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
lean_inc_ref(v___y_1751_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_1767_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_1754_, v___x_1396_, v___y_1750_, v___y_1748_, v___y_1747_, v___y_1751_, v___x_1766_, v___y_1749_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1755_, v___y_1752_, v___y_1753_, v___y_1745_);
v___y_1725_ = v___y_1745_;
v___y_1726_ = v___y_1752_;
v___y_1727_ = v___y_1753_;
v___y_1728_ = v___y_1755_;
v___y_1729_ = v___y_1749_;
v___y_1730_ = v___y_1756_;
v___y_1731_ = v___y_1757_;
v___y_1732_ = v___y_1758_;
v___y_1733_ = v___x_1767_;
goto v___jp_1724_;
}
v___jp_1768_:
{
lean_object* v___x_1784_; double v___x_1785_; double v___x_1786_; double v___x_1787_; double v___x_1788_; double v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1784_ = lean_io_mono_nanos_now();
v___x_1785_ = lean_float_of_nat(v___y_1773_);
v___x_1786_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1787_ = lean_float_div(v___x_1785_, v___x_1786_);
v___x_1788_ = lean_float_of_nat(v___x_1784_);
v___x_1789_ = lean_float_div(v___x_1788_, v___x_1786_);
v___x_1790_ = lean_box_float(v___x_1787_);
v___x_1791_ = lean_box_float(v___x_1789_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_a_1783_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
lean_inc_ref(v___y_1775_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_1794_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_1778_, v___x_1396_, v___y_1774_, v___y_1771_, v___y_1770_, v___y_1775_, v___x_1793_, v___y_1772_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1779_, v___y_1776_, v___y_1777_, v___y_1769_);
v___y_1725_ = v___y_1769_;
v___y_1726_ = v___y_1776_;
v___y_1727_ = v___y_1777_;
v___y_1728_ = v___y_1779_;
v___y_1729_ = v___y_1772_;
v___y_1730_ = v___y_1780_;
v___y_1731_ = v___y_1781_;
v___y_1732_ = v___y_1782_;
v___y_1733_ = v___x_1794_;
goto v___jp_1724_;
}
v___jp_1795_:
{
lean_object* v___x_1809_; lean_object* v_a_1810_; uint8_t v___x_1811_; 
v___x_1809_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1796_);
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref(v___x_1809_);
v___x_1811_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1800_, v___x_1397_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_io_mono_nanos_now();
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1799_);
v___x_1813_ = lean_apply_9(v___y_1797_, v___y_1799_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1804_, v___y_1802_, v___y_1803_, v___y_1796_, lean_box(0));
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set_tag(v___x_1816_, 1);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
v___y_1769_ = v___y_1796_;
v___y_1770_ = v_a_1810_;
v___y_1771_ = v___y_1798_;
v___y_1772_ = v___y_1799_;
v___y_1773_ = v___x_1812_;
v___y_1774_ = v___y_1800_;
v___y_1775_ = v___y_1801_;
v___y_1776_ = v___y_1802_;
v___y_1777_ = v___y_1803_;
v___y_1778_ = v___y_1805_;
v___y_1779_ = v___y_1804_;
v___y_1780_ = v___y_1806_;
v___y_1781_ = v___y_1807_;
v___y_1782_ = v___y_1808_;
v_a_1783_ = v___x_1819_;
goto v___jp_1768_;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1813_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1813_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
v___y_1769_ = v___y_1796_;
v___y_1770_ = v_a_1810_;
v___y_1771_ = v___y_1798_;
v___y_1772_ = v___y_1799_;
v___y_1773_ = v___x_1812_;
v___y_1774_ = v___y_1800_;
v___y_1775_ = v___y_1801_;
v___y_1776_ = v___y_1802_;
v___y_1777_ = v___y_1803_;
v___y_1778_ = v___y_1805_;
v___y_1779_ = v___y_1804_;
v___y_1780_ = v___y_1806_;
v___y_1781_ = v___y_1807_;
v___y_1782_ = v___y_1808_;
v_a_1783_ = v___x_1827_;
goto v___jp_1768_;
}
}
}
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1799_);
v___x_1831_ = lean_apply_9(v___y_1797_, v___y_1799_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1804_, v___y_1802_, v___y_1803_, v___y_1796_, lean_box(0));
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 1);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
v___y_1745_ = v___y_1796_;
v___y_1746_ = v___x_1830_;
v___y_1747_ = v_a_1810_;
v___y_1748_ = v___y_1798_;
v___y_1749_ = v___y_1799_;
v___y_1750_ = v___y_1800_;
v___y_1751_ = v___y_1801_;
v___y_1752_ = v___y_1802_;
v___y_1753_ = v___y_1803_;
v___y_1754_ = v___y_1805_;
v___y_1755_ = v___y_1804_;
v___y_1756_ = v___y_1806_;
v___y_1757_ = v___y_1807_;
v___y_1758_ = v___y_1808_;
v_a_1759_ = v___x_1837_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1831_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1831_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 0);
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
v___y_1745_ = v___y_1796_;
v___y_1746_ = v___x_1830_;
v___y_1747_ = v_a_1810_;
v___y_1748_ = v___y_1798_;
v___y_1749_ = v___y_1799_;
v___y_1750_ = v___y_1800_;
v___y_1751_ = v___y_1801_;
v___y_1752_ = v___y_1802_;
v___y_1753_ = v___y_1803_;
v___y_1754_ = v___y_1805_;
v___y_1755_ = v___y_1804_;
v___y_1756_ = v___y_1806_;
v___y_1757_ = v___y_1807_;
v___y_1758_ = v___y_1808_;
v_a_1759_ = v___x_1845_;
goto v___jp_1744_;
}
}
}
}
}
v___jp_1848_:
{
if (v_enums_1534_ == 0)
{
v___y_1702_ = v___y_1849_;
v___y_1703_ = v___y_1850_;
v___y_1704_ = v___y_1851_;
v___y_1705_ = v___y_1852_;
v___y_1706_ = v___y_1853_;
v___y_1707_ = v___y_1854_;
v___y_1708_ = v___y_1855_;
v___y_1709_ = v___y_1856_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1857_; lean_object* v_options_1858_; uint8_t v_hasTrace_1859_; 
v___x_1857_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_options_1858_ = lean_ctor_get(v___y_1855_, 2);
v_hasTrace_1859_ = lean_ctor_get_uint8(v_options_1858_, sizeof(void*)*1);
if (v_hasTrace_1859_ == 0)
{
lean_object* v_run_x27_1860_; lean_object* v___x_1861_; 
v_run_x27_1860_ = lean_ctor_get(v___x_1857_, 1);
lean_inc_ref(v_run_x27_1860_);
lean_inc(v___y_1856_);
lean_inc_ref(v___y_1855_);
lean_inc(v___y_1854_);
lean_inc_ref(v___y_1853_);
lean_inc(v___y_1852_);
lean_inc_ref(v___y_1851_);
lean_inc(v___y_1850_);
lean_inc_ref(v___y_1849_);
v___x_1861_ = lean_apply_9(v_run_x27_1860_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, lean_box(0));
v___y_1725_ = v___y_1856_;
v___y_1726_ = v___y_1854_;
v___y_1727_ = v___y_1855_;
v___y_1728_ = v___y_1853_;
v___y_1729_ = v___y_1849_;
v___y_1730_ = v___y_1850_;
v___y_1731_ = v___y_1851_;
v___y_1732_ = v___y_1852_;
v___y_1733_ = v___x_1861_;
goto v___jp_1724_;
}
else
{
lean_object* v_run_x27_1862_; lean_object* v_inheritedTraceOptions_1863_; lean_object* v___f_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_run_x27_1862_ = lean_ctor_get(v___x_1857_, 1);
v_inheritedTraceOptions_1863_ = lean_ctor_get(v___y_1855_, 13);
v___f_1864_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5);
v___x_1865_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1395_);
v___x_1866_ = l_Lean_Name_append(v___x_1865_, v_cls_1395_);
v___x_1867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1863_, v_options_1858_, v___x_1866_);
lean_dec(v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = l_Lean_trace_profiler;
v___x_1869_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1858_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
lean_inc_ref(v_run_x27_1862_);
lean_inc(v___y_1856_);
lean_inc_ref(v___y_1855_);
lean_inc(v___y_1854_);
lean_inc_ref(v___y_1853_);
lean_inc(v___y_1852_);
lean_inc_ref(v___y_1851_);
lean_inc(v___y_1850_);
lean_inc_ref(v___y_1849_);
v___x_1870_ = lean_apply_9(v_run_x27_1862_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, lean_box(0));
v___y_1725_ = v___y_1856_;
v___y_1726_ = v___y_1854_;
v___y_1727_ = v___y_1855_;
v___y_1728_ = v___y_1853_;
v___y_1729_ = v___y_1849_;
v___y_1730_ = v___y_1850_;
v___y_1731_ = v___y_1851_;
v___y_1732_ = v___y_1852_;
v___y_1733_ = v___x_1870_;
goto v___jp_1724_;
}
else
{
lean_inc_ref(v_run_x27_1862_);
v___y_1796_ = v___y_1856_;
v___y_1797_ = v_run_x27_1862_;
v___y_1798_ = v___x_1867_;
v___y_1799_ = v___y_1849_;
v___y_1800_ = v_options_1858_;
v___y_1801_ = v___f_1864_;
v___y_1802_ = v___y_1854_;
v___y_1803_ = v___y_1855_;
v___y_1804_ = v___y_1853_;
v___y_1805_ = v_hasTrace_1859_;
v___y_1806_ = v___y_1850_;
v___y_1807_ = v___y_1851_;
v___y_1808_ = v___y_1852_;
goto v___jp_1795_;
}
}
else
{
lean_inc_ref(v_run_x27_1862_);
v___y_1796_ = v___y_1856_;
v___y_1797_ = v_run_x27_1862_;
v___y_1798_ = v___x_1867_;
v___y_1799_ = v___y_1849_;
v___y_1800_ = v_options_1858_;
v___y_1801_ = v___f_1864_;
v___y_1802_ = v___y_1854_;
v___y_1803_ = v___y_1855_;
v___y_1804_ = v___y_1853_;
v___y_1805_ = v_hasTrace_1859_;
v___y_1806_ = v___y_1850_;
v___y_1807_ = v___y_1851_;
v___y_1808_ = v___y_1852_;
goto v___jp_1795_;
}
}
}
}
v___jp_1871_:
{
if (lean_obj_tag(v___y_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1890_; 
v_a_1881_ = lean_ctor_get(v___y_1880_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___y_1880_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1883_ = v___y_1880_;
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___y_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_unbox(v_a_1881_);
lean_dec(v_a_1881_);
if (v___x_1885_ == 0)
{
lean_del_object(v___x_1883_);
v___y_1849_ = v___y_1879_;
v___y_1850_ = v___y_1872_;
v___y_1851_ = v___y_1877_;
v___y_1852_ = v___y_1876_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1874_;
v___y_1855_ = v___y_1873_;
v___y_1856_ = v___y_1875_;
goto v___jp_1848_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
v___x_1886_ = lean_box(v___x_1394_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
return v___y_1880_;
}
}
v___jp_1891_:
{
lean_object* v___x_1907_; double v___x_1908_; double v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1907_ = lean_io_get_num_heartbeats();
v___x_1908_ = lean_float_of_nat(v___y_1896_);
v___x_1909_ = lean_float_of_nat(v___x_1907_);
v___x_1910_ = lean_box_float(v___x_1908_);
v___x_1911_ = lean_box_float(v___x_1909_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_a_1906_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
lean_inc_ref(v___y_1899_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_1914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_1903_, v___x_1396_, v___y_1898_, v___y_1902_, v___y_1895_, v___y_1899_, v___x_1913_, v___y_1905_, v___y_1900_, v___y_1897_, v___y_1894_, v___y_1904_, v___y_1893_, v___y_1892_, v___y_1901_);
v___y_1872_ = v___y_1900_;
v___y_1873_ = v___y_1892_;
v___y_1874_ = v___y_1893_;
v___y_1875_ = v___y_1901_;
v___y_1876_ = v___y_1894_;
v___y_1877_ = v___y_1897_;
v___y_1878_ = v___y_1904_;
v___y_1879_ = v___y_1905_;
v___y_1880_ = v___x_1914_;
goto v___jp_1871_;
}
v___jp_1915_:
{
lean_object* v___x_1931_; double v___x_1932_; double v___x_1933_; double v___x_1934_; double v___x_1935_; double v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1931_ = lean_io_mono_nanos_now();
v___x_1932_ = lean_float_of_nat(v___y_1923_);
v___x_1933_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1934_ = lean_float_div(v___x_1932_, v___x_1933_);
v___x_1935_ = lean_float_of_nat(v___x_1931_);
v___x_1936_ = lean_float_div(v___x_1935_, v___x_1933_);
v___x_1937_ = lean_box_float(v___x_1934_);
v___x_1938_ = lean_box_float(v___x_1936_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1930_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
lean_inc_ref(v___y_1922_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_1941_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_1927_, v___x_1396_, v___y_1921_, v___y_1926_, v___y_1919_, v___y_1922_, v___x_1940_, v___y_1929_, v___y_1924_, v___y_1920_, v___y_1918_, v___y_1928_, v___y_1917_, v___y_1916_, v___y_1925_);
v___y_1872_ = v___y_1924_;
v___y_1873_ = v___y_1916_;
v___y_1874_ = v___y_1917_;
v___y_1875_ = v___y_1925_;
v___y_1876_ = v___y_1918_;
v___y_1877_ = v___y_1920_;
v___y_1878_ = v___y_1928_;
v___y_1879_ = v___y_1929_;
v___y_1880_ = v___x_1941_;
goto v___jp_1871_;
}
v___jp_1942_:
{
lean_object* v___x_1956_; lean_object* v_a_1957_; uint8_t v___x_1958_; 
v___x_1956_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1951_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
v___x_1958_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1948_, v___x_1397_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_io_mono_nanos_now();
lean_inc(v___y_1951_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1955_);
v___x_1960_ = lean_apply_9(v___y_1946_, v___y_1955_, v___y_1950_, v___y_1947_, v___y_1945_, v___y_1954_, v___y_1944_, v___y_1943_, v___y_1951_, lean_box(0));
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 1);
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
v___y_1916_ = v___y_1943_;
v___y_1917_ = v___y_1944_;
v___y_1918_ = v___y_1945_;
v___y_1919_ = v_a_1957_;
v___y_1920_ = v___y_1947_;
v___y_1921_ = v___y_1948_;
v___y_1922_ = v___y_1949_;
v___y_1923_ = v___x_1959_;
v___y_1924_ = v___y_1950_;
v___y_1925_ = v___y_1951_;
v___y_1926_ = v___y_1952_;
v___y_1927_ = v___y_1953_;
v___y_1928_ = v___y_1954_;
v___y_1929_ = v___y_1955_;
v_a_1930_ = v___x_1966_;
goto v___jp_1915_;
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
v_a_1969_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1960_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1960_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 0);
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
v___y_1916_ = v___y_1943_;
v___y_1917_ = v___y_1944_;
v___y_1918_ = v___y_1945_;
v___y_1919_ = v_a_1957_;
v___y_1920_ = v___y_1947_;
v___y_1921_ = v___y_1948_;
v___y_1922_ = v___y_1949_;
v___y_1923_ = v___x_1959_;
v___y_1924_ = v___y_1950_;
v___y_1925_ = v___y_1951_;
v___y_1926_ = v___y_1952_;
v___y_1927_ = v___y_1953_;
v___y_1928_ = v___y_1954_;
v___y_1929_ = v___y_1955_;
v_a_1930_ = v___x_1974_;
goto v___jp_1915_;
}
}
}
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1951_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1955_);
v___x_1978_ = lean_apply_9(v___y_1946_, v___y_1955_, v___y_1950_, v___y_1947_, v___y_1945_, v___y_1954_, v___y_1944_, v___y_1943_, v___y_1951_, lean_box(0));
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 1);
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
v___y_1892_ = v___y_1943_;
v___y_1893_ = v___y_1944_;
v___y_1894_ = v___y_1945_;
v___y_1895_ = v_a_1957_;
v___y_1896_ = v___x_1977_;
v___y_1897_ = v___y_1947_;
v___y_1898_ = v___y_1948_;
v___y_1899_ = v___y_1949_;
v___y_1900_ = v___y_1950_;
v___y_1901_ = v___y_1951_;
v___y_1902_ = v___y_1952_;
v___y_1903_ = v___y_1953_;
v___y_1904_ = v___y_1954_;
v___y_1905_ = v___y_1955_;
v_a_1906_ = v___x_1984_;
goto v___jp_1891_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1978_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1978_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set_tag(v___x_1989_, 0);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v___y_1892_ = v___y_1943_;
v___y_1893_ = v___y_1944_;
v___y_1894_ = v___y_1945_;
v___y_1895_ = v_a_1957_;
v___y_1896_ = v___x_1977_;
v___y_1897_ = v___y_1947_;
v___y_1898_ = v___y_1948_;
v___y_1899_ = v___y_1949_;
v___y_1900_ = v___y_1950_;
v___y_1901_ = v___y_1951_;
v___y_1902_ = v___y_1952_;
v___y_1903_ = v___y_1953_;
v___y_1904_ = v___y_1954_;
v___y_1905_ = v___y_1955_;
v_a_1906_ = v___x_1992_;
goto v___jp_1891_;
}
}
}
}
}
v___jp_1995_:
{
if (lean_obj_tag(v___y_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2028_; 
v_a_2005_ = lean_ctor_get(v___y_2004_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___y_2004_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2007_ = v___y_2004_;
v_isShared_2008_ = v_isSharedCheck_2028_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___y_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2028_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_unbox(v_a_2005_);
lean_dec(v_a_2005_);
if (v___x_2009_ == 0)
{
lean_del_object(v___x_2007_);
if (v_structures_1532_ == 0)
{
v___y_1849_ = v___y_2003_;
v___y_1850_ = v___y_1996_;
v___y_1851_ = v___y_2001_;
v___y_1852_ = v___y_2000_;
v___y_1853_ = v___y_2002_;
v___y_1854_ = v___y_1998_;
v___y_1855_ = v___y_1997_;
v___y_1856_ = v___y_1999_;
goto v___jp_1848_;
}
else
{
lean_object* v___x_2010_; lean_object* v_options_2011_; uint8_t v_hasTrace_2012_; 
v___x_2010_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_options_2011_ = lean_ctor_get(v___y_1997_, 2);
v_hasTrace_2012_ = lean_ctor_get_uint8(v_options_2011_, sizeof(void*)*1);
if (v_hasTrace_2012_ == 0)
{
lean_object* v_run_x27_2013_; lean_object* v___x_2014_; 
v_run_x27_2013_ = lean_ctor_get(v___x_2010_, 1);
lean_inc_ref(v_run_x27_2013_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2000_);
lean_inc_ref(v___y_2001_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_2003_);
v___x_2014_ = lean_apply_9(v_run_x27_2013_, v___y_2003_, v___y_1996_, v___y_2001_, v___y_2000_, v___y_2002_, v___y_1998_, v___y_1997_, v___y_1999_, lean_box(0));
v___y_1872_ = v___y_1996_;
v___y_1873_ = v___y_1997_;
v___y_1874_ = v___y_1998_;
v___y_1875_ = v___y_1999_;
v___y_1876_ = v___y_2000_;
v___y_1877_ = v___y_2001_;
v___y_1878_ = v___y_2002_;
v___y_1879_ = v___y_2003_;
v___y_1880_ = v___x_2014_;
goto v___jp_1871_;
}
else
{
lean_object* v_run_x27_2015_; lean_object* v_inheritedTraceOptions_2016_; lean_object* v___f_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_run_x27_2015_ = lean_ctor_get(v___x_2010_, 1);
v_inheritedTraceOptions_2016_ = lean_ctor_get(v___y_1997_, 13);
v___f_2017_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6);
v___x_2018_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1395_);
v___x_2019_ = l_Lean_Name_append(v___x_2018_, v_cls_1395_);
v___x_2020_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2016_, v_options_2011_, v___x_2019_);
lean_dec(v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = l_Lean_trace_profiler;
v___x_2022_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2011_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_inc_ref(v_run_x27_2015_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2000_);
lean_inc_ref(v___y_2001_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_2003_);
v___x_2023_ = lean_apply_9(v_run_x27_2015_, v___y_2003_, v___y_1996_, v___y_2001_, v___y_2000_, v___y_2002_, v___y_1998_, v___y_1997_, v___y_1999_, lean_box(0));
v___y_1872_ = v___y_1996_;
v___y_1873_ = v___y_1997_;
v___y_1874_ = v___y_1998_;
v___y_1875_ = v___y_1999_;
v___y_1876_ = v___y_2000_;
v___y_1877_ = v___y_2001_;
v___y_1878_ = v___y_2002_;
v___y_1879_ = v___y_2003_;
v___y_1880_ = v___x_2023_;
goto v___jp_1871_;
}
else
{
lean_inc_ref(v_run_x27_2015_);
v___y_1943_ = v___y_1997_;
v___y_1944_ = v___y_1998_;
v___y_1945_ = v___y_2000_;
v___y_1946_ = v_run_x27_2015_;
v___y_1947_ = v___y_2001_;
v___y_1948_ = v_options_2011_;
v___y_1949_ = v___f_2017_;
v___y_1950_ = v___y_1996_;
v___y_1951_ = v___y_1999_;
v___y_1952_ = v___x_2020_;
v___y_1953_ = v_hasTrace_2012_;
v___y_1954_ = v___y_2002_;
v___y_1955_ = v___y_2003_;
goto v___jp_1942_;
}
}
else
{
lean_inc_ref(v_run_x27_2015_);
v___y_1943_ = v___y_1997_;
v___y_1944_ = v___y_1998_;
v___y_1945_ = v___y_2000_;
v___y_1946_ = v_run_x27_2015_;
v___y_1947_ = v___y_2001_;
v___y_1948_ = v_options_2011_;
v___y_1949_ = v___f_2017_;
v___y_1950_ = v___y_1996_;
v___y_1951_ = v___y_1999_;
v___y_1952_ = v___x_2020_;
v___y_1953_ = v_hasTrace_2012_;
v___y_1954_ = v___y_2002_;
v___y_1955_ = v___y_2003_;
goto v___jp_1942_;
}
}
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
v___x_2024_ = lean_box(v___x_1394_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2024_);
v___x_2026_ = v___x_2007_;
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
else
{
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
return v___y_2004_;
}
}
v___jp_2029_:
{
lean_object* v___x_2045_; double v___x_2046_; double v___x_2047_; double v___x_2048_; double v___x_2049_; double v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2045_ = lean_io_mono_nanos_now();
v___x_2046_ = lean_float_of_nat(v___y_2037_);
v___x_2047_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2048_ = lean_float_div(v___x_2046_, v___x_2047_);
v___x_2049_ = lean_float_of_nat(v___x_2045_);
v___x_2050_ = lean_float_div(v___x_2049_, v___x_2047_);
v___x_2051_ = lean_box_float(v___x_2048_);
v___x_2052_ = lean_box_float(v___x_2050_);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_a_2044_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_inc_ref(v___y_2035_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_2055_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_2041_, v___x_1396_, v___y_2039_, v___y_2040_, v___y_2030_, v___y_2035_, v___x_2054_, v___y_2043_, v___y_2036_, v___y_2034_, v___y_2033_, v___y_2042_, v___y_2032_, v___y_2031_, v___y_2038_);
v___y_1996_ = v___y_2036_;
v___y_1997_ = v___y_2031_;
v___y_1998_ = v___y_2032_;
v___y_1999_ = v___y_2038_;
v___y_2000_ = v___y_2033_;
v___y_2001_ = v___y_2034_;
v___y_2002_ = v___y_2042_;
v___y_2003_ = v___y_2043_;
v___y_2004_ = v___x_2055_;
goto v___jp_1995_;
}
v___jp_2056_:
{
lean_object* v___x_2072_; double v___x_2073_; double v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2072_ = lean_io_get_num_heartbeats();
v___x_2073_ = lean_float_of_nat(v___y_2068_);
v___x_2074_ = lean_float_of_nat(v___x_2072_);
v___x_2075_ = lean_box_float(v___x_2073_);
v___x_2076_ = lean_box_float(v___x_2074_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_a_2071_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
lean_inc_ref(v___y_2062_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_2079_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_2067_, v___x_1396_, v___y_2065_, v___y_2066_, v___y_2057_, v___y_2062_, v___x_2078_, v___y_2070_, v___y_2063_, v___y_2061_, v___y_2060_, v___y_2069_, v___y_2059_, v___y_2058_, v___y_2064_);
v___y_1996_ = v___y_2063_;
v___y_1997_ = v___y_2058_;
v___y_1998_ = v___y_2059_;
v___y_1999_ = v___y_2064_;
v___y_2000_ = v___y_2060_;
v___y_2001_ = v___y_2061_;
v___y_2002_ = v___y_2069_;
v___y_2003_ = v___y_2070_;
v___y_2004_ = v___x_2079_;
goto v___jp_1995_;
}
v___jp_2080_:
{
lean_object* v___x_2094_; lean_object* v_a_2095_; uint8_t v___x_2096_; 
v___x_2094_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2088_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2094_);
v___x_2096_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2089_, v___x_1397_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_io_mono_nanos_now();
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2092_);
lean_inc(v___y_2083_);
lean_inc_ref(v___y_2084_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2093_);
v___x_2098_ = lean_apply_9(v___y_2087_, v___y_2093_, v___y_2086_, v___y_2084_, v___y_2083_, v___y_2092_, v___y_2082_, v___y_2081_, v___y_2088_, lean_box(0));
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 1);
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
v___y_2030_ = v_a_2095_;
v___y_2031_ = v___y_2081_;
v___y_2032_ = v___y_2082_;
v___y_2033_ = v___y_2083_;
v___y_2034_ = v___y_2084_;
v___y_2035_ = v___y_2085_;
v___y_2036_ = v___y_2086_;
v___y_2037_ = v___x_2097_;
v___y_2038_ = v___y_2088_;
v___y_2039_ = v___y_2089_;
v___y_2040_ = v___y_2090_;
v___y_2041_ = v___y_2091_;
v___y_2042_ = v___y_2092_;
v___y_2043_ = v___y_2093_;
v_a_2044_ = v___x_2104_;
goto v___jp_2029_;
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_a_2107_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2098_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2098_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 0);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
v___y_2030_ = v_a_2095_;
v___y_2031_ = v___y_2081_;
v___y_2032_ = v___y_2082_;
v___y_2033_ = v___y_2083_;
v___y_2034_ = v___y_2084_;
v___y_2035_ = v___y_2085_;
v___y_2036_ = v___y_2086_;
v___y_2037_ = v___x_2097_;
v___y_2038_ = v___y_2088_;
v___y_2039_ = v___y_2089_;
v___y_2040_ = v___y_2090_;
v___y_2041_ = v___y_2091_;
v___y_2042_ = v___y_2092_;
v___y_2043_ = v___y_2093_;
v_a_2044_ = v___x_2112_;
goto v___jp_2029_;
}
}
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2092_);
lean_inc(v___y_2083_);
lean_inc_ref(v___y_2084_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2093_);
v___x_2116_ = lean_apply_9(v___y_2087_, v___y_2093_, v___y_2086_, v___y_2084_, v___y_2083_, v___y_2092_, v___y_2082_, v___y_2081_, v___y_2088_, lean_box(0));
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set_tag(v___x_2119_, 1);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
v___y_2057_ = v_a_2095_;
v___y_2058_ = v___y_2081_;
v___y_2059_ = v___y_2082_;
v___y_2060_ = v___y_2083_;
v___y_2061_ = v___y_2084_;
v___y_2062_ = v___y_2085_;
v___y_2063_ = v___y_2086_;
v___y_2064_ = v___y_2088_;
v___y_2065_ = v___y_2089_;
v___y_2066_ = v___y_2090_;
v___y_2067_ = v___y_2091_;
v___y_2068_ = v___x_2115_;
v___y_2069_ = v___y_2092_;
v___y_2070_ = v___y_2093_;
v_a_2071_ = v___x_2122_;
goto v___jp_2056_;
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
v_a_2125_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2116_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2116_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 0);
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
v___y_2057_ = v_a_2095_;
v___y_2058_ = v___y_2081_;
v___y_2059_ = v___y_2082_;
v___y_2060_ = v___y_2083_;
v___y_2061_ = v___y_2084_;
v___y_2062_ = v___y_2085_;
v___y_2063_ = v___y_2086_;
v___y_2064_ = v___y_2088_;
v___y_2065_ = v___y_2089_;
v___y_2066_ = v___y_2090_;
v___y_2067_ = v___y_2091_;
v___y_2068_ = v___x_2115_;
v___y_2069_ = v___y_2092_;
v___y_2070_ = v___y_2093_;
v_a_2071_ = v___x_2130_;
goto v___jp_2056_;
}
}
}
}
}
v___jp_2133_:
{
lean_object* v___x_2142_; lean_object* v_options_2143_; uint8_t v_hasTrace_2144_; 
v___x_2142_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v_options_2143_ = lean_ctor_get(v___y_2140_, 2);
v_hasTrace_2144_ = lean_ctor_get_uint8(v_options_2143_, sizeof(void*)*1);
if (v_hasTrace_2144_ == 0)
{
lean_object* v_run_x27_2145_; lean_object* v___x_2146_; 
v_run_x27_2145_ = lean_ctor_get(v___x_2142_, 1);
lean_inc_ref(v_run_x27_2145_);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
lean_inc_ref(v___y_2136_);
lean_inc(v___y_2135_);
lean_inc_ref(v___y_2134_);
v___x_2146_ = lean_apply_9(v_run_x27_2145_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, lean_box(0));
v___y_1996_ = v___y_2135_;
v___y_1997_ = v___y_2140_;
v___y_1998_ = v___y_2139_;
v___y_1999_ = v___y_2141_;
v___y_2000_ = v___y_2137_;
v___y_2001_ = v___y_2136_;
v___y_2002_ = v___y_2138_;
v___y_2003_ = v___y_2134_;
v___y_2004_ = v___x_2146_;
goto v___jp_1995_;
}
else
{
lean_object* v_run_x27_2147_; lean_object* v_inheritedTraceOptions_2148_; lean_object* v___f_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v_run_x27_2147_ = lean_ctor_get(v___x_2142_, 1);
v_inheritedTraceOptions_2148_ = lean_ctor_get(v___y_2140_, 13);
v___f_2149_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7);
v___x_2150_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1395_);
v___x_2151_ = l_Lean_Name_append(v___x_2150_, v_cls_1395_);
v___x_2152_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2148_, v_options_2143_, v___x_2151_);
lean_dec(v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = l_Lean_trace_profiler;
v___x_2154_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2143_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
lean_inc_ref(v_run_x27_2147_);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
lean_inc_ref(v___y_2136_);
lean_inc(v___y_2135_);
lean_inc_ref(v___y_2134_);
v___x_2155_ = lean_apply_9(v_run_x27_2147_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, lean_box(0));
v___y_1996_ = v___y_2135_;
v___y_1997_ = v___y_2140_;
v___y_1998_ = v___y_2139_;
v___y_1999_ = v___y_2141_;
v___y_2000_ = v___y_2137_;
v___y_2001_ = v___y_2136_;
v___y_2002_ = v___y_2138_;
v___y_2003_ = v___y_2134_;
v___y_2004_ = v___x_2155_;
goto v___jp_1995_;
}
else
{
lean_inc_ref(v_run_x27_2147_);
v___y_2081_ = v___y_2140_;
v___y_2082_ = v___y_2139_;
v___y_2083_ = v___y_2137_;
v___y_2084_ = v___y_2136_;
v___y_2085_ = v___f_2149_;
v___y_2086_ = v___y_2135_;
v___y_2087_ = v_run_x27_2147_;
v___y_2088_ = v___y_2141_;
v___y_2089_ = v_options_2143_;
v___y_2090_ = v___x_2152_;
v___y_2091_ = v_hasTrace_2144_;
v___y_2092_ = v___y_2138_;
v___y_2093_ = v___y_2134_;
goto v___jp_2080_;
}
}
else
{
lean_inc_ref(v_run_x27_2147_);
v___y_2081_ = v___y_2140_;
v___y_2082_ = v___y_2139_;
v___y_2083_ = v___y_2137_;
v___y_2084_ = v___y_2136_;
v___y_2085_ = v___f_2149_;
v___y_2086_ = v___y_2135_;
v___y_2087_ = v_run_x27_2147_;
v___y_2088_ = v___y_2141_;
v___y_2089_ = v_options_2143_;
v___y_2090_ = v___x_2152_;
v___y_2091_ = v_hasTrace_2144_;
v___y_2092_ = v___y_2138_;
v___y_2093_ = v___y_2134_;
goto v___jp_2080_;
}
}
}
v___jp_2156_:
{
if (lean_obj_tag(v___y_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2167_; 
v_a_2158_ = lean_ctor_get(v___y_2157_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___y_2157_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2160_ = v___y_2157_;
v_isShared_2161_ = v_isSharedCheck_2167_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___y_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2167_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_unbox(v_a_2158_);
lean_dec(v_a_2158_);
if (v___x_2162_ == 0)
{
lean_del_object(v___x_2160_);
v___y_2134_ = v___y_1399_;
v___y_2135_ = v___y_1400_;
v___y_2136_ = v___y_1401_;
v___y_2137_ = v___y_1402_;
v___y_2138_ = v___y_1403_;
v___y_2139_ = v___y_1404_;
v___y_2140_ = v___y_1405_;
v___y_2141_ = v___y_1406_;
goto v___jp_2133_;
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
v___x_2163_ = lean_box(v___x_1394_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2163_);
v___x_2165_ = v___x_2160_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_dec_ref(v___x_1396_);
lean_dec(v_cls_1395_);
return v___y_2157_;
}
}
v___jp_2168_:
{
lean_object* v___x_2176_; double v___x_2177_; double v___x_2178_; double v___x_2179_; double v___x_2180_; double v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2176_ = lean_io_mono_nanos_now();
v___x_2177_ = lean_float_of_nat(v___y_2172_);
v___x_2178_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2179_ = lean_float_div(v___x_2177_, v___x_2178_);
v___x_2180_ = lean_float_of_nat(v___x_2176_);
v___x_2181_ = lean_float_div(v___x_2180_, v___x_2178_);
v___x_2182_ = lean_box_float(v___x_2179_);
v___x_2183_ = lean_box_float(v___x_2181_);
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2175_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
lean_inc_ref(v___y_2174_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_2186_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_2173_, v___x_1396_, v___y_2170_, v___y_2171_, v___y_2169_, v___y_2174_, v___x_2185_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
v___y_2157_ = v___x_2186_;
goto v___jp_2156_;
}
v___jp_2187_:
{
lean_object* v___x_2195_; double v___x_2196_; double v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2195_ = lean_io_get_num_heartbeats();
v___x_2196_ = lean_float_of_nat(v___y_2193_);
v___x_2197_ = lean_float_of_nat(v___x_2195_);
v___x_2198_ = lean_box_float(v___x_2196_);
v___x_2199_ = lean_box_float(v___x_2197_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2194_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
lean_inc_ref(v___y_2192_);
lean_inc_ref(v___x_1396_);
lean_inc(v_cls_1395_);
v___x_2202_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1395_, v___y_2191_, v___x_1396_, v___y_2189_, v___y_2190_, v___y_2188_, v___y_2192_, v___x_2201_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
v___y_2157_ = v___x_2202_;
goto v___jp_2156_;
}
v___jp_2203_:
{
lean_object* v___x_2209_; lean_object* v_a_2210_; uint8_t v___x_2211_; 
v___x_2209_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1406_);
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2204_, v___x_1397_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_io_mono_nanos_now();
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_2213_ = lean_apply_9(v___y_2208_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, lean_box(0));
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set_tag(v___x_2216_, 1);
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
v___y_2169_ = v_a_2210_;
v___y_2170_ = v___y_2204_;
v___y_2171_ = v___y_2205_;
v___y_2172_ = v___x_2212_;
v___y_2173_ = v___y_2206_;
v___y_2174_ = v___y_2207_;
v_a_2175_ = v___x_2219_;
goto v___jp_2168_;
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
v_a_2222_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2213_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2213_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 0);
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
v___y_2169_ = v_a_2210_;
v___y_2170_ = v___y_2204_;
v___y_2171_ = v___y_2205_;
v___y_2172_ = v___x_2212_;
v___y_2173_ = v___y_2206_;
v___y_2174_ = v___y_2207_;
v_a_2175_ = v___x_2227_;
goto v___jp_2168_;
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_2231_ = lean_apply_9(v___y_2208_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, lean_box(0));
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
lean_ctor_set_tag(v___x_2234_, 1);
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
v___y_2188_ = v_a_2210_;
v___y_2189_ = v___y_2204_;
v___y_2190_ = v___y_2205_;
v___y_2191_ = v___y_2206_;
v___y_2192_ = v___y_2207_;
v___y_2193_ = v___x_2230_;
v_a_2194_ = v___x_2237_;
goto v___jp_2187_;
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
v_a_2240_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2231_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2231_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 0);
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
v___y_2188_ = v_a_2210_;
v___y_2189_ = v___y_2204_;
v___y_2190_ = v___y_2205_;
v___y_2191_ = v___y_2206_;
v___y_2192_ = v___y_2207_;
v___y_2193_ = v___x_2230_;
v_a_2194_ = v___x_2245_;
goto v___jp_2187_;
}
}
}
}
}
v___jp_2248_:
{
if (v___y_2249_ == 0)
{
v___y_2134_ = v___y_1399_;
v___y_2135_ = v___y_1400_;
v___y_2136_ = v___y_1401_;
v___y_2137_ = v___y_1402_;
v___y_2138_ = v___y_1403_;
v___y_2139_ = v___y_1404_;
v___y_2140_ = v___y_1405_;
v___y_2141_ = v___y_1406_;
goto v___jp_2133_;
}
else
{
lean_object* v___x_2250_; lean_object* v_options_2251_; uint8_t v_hasTrace_2252_; 
v___x_2250_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_options_2251_ = lean_ctor_get(v___y_1405_, 2);
v_hasTrace_2252_ = lean_ctor_get_uint8(v_options_2251_, sizeof(void*)*1);
if (v_hasTrace_2252_ == 0)
{
lean_object* v_run_x27_2253_; lean_object* v___x_2254_; 
v_run_x27_2253_ = lean_ctor_get(v___x_2250_, 1);
lean_inc_ref(v_run_x27_2253_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_2254_ = lean_apply_9(v_run_x27_2253_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, lean_box(0));
v___y_2157_ = v___x_2254_;
goto v___jp_2156_;
}
else
{
lean_object* v_run_x27_2255_; lean_object* v_inheritedTraceOptions_2256_; lean_object* v___f_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v_run_x27_2255_ = lean_ctor_get(v___x_2250_, 1);
v_inheritedTraceOptions_2256_ = lean_ctor_get(v___y_1405_, 13);
v___f_2257_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8);
v___x_2258_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1395_);
v___x_2259_ = l_Lean_Name_append(v___x_2258_, v_cls_1395_);
v___x_2260_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2256_, v_options_2251_, v___x_2259_);
lean_dec(v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = l_Lean_trace_profiler;
v___x_2262_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2251_, v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; 
lean_inc_ref(v_run_x27_2255_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_2263_ = lean_apply_9(v_run_x27_2255_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, lean_box(0));
v___y_2157_ = v___x_2263_;
goto v___jp_2156_;
}
else
{
lean_inc_ref(v_run_x27_2255_);
v___y_2204_ = v_options_2251_;
v___y_2205_ = v___x_2260_;
v___y_2206_ = v_hasTrace_2252_;
v___y_2207_ = v___f_2257_;
v___y_2208_ = v_run_x27_2255_;
goto v___jp_2203_;
}
}
else
{
lean_inc_ref(v_run_x27_2255_);
v___y_2204_ = v_options_2251_;
v___y_2205_ = v___x_2260_;
v___y_2206_ = v_hasTrace_2252_;
v___y_2207_ = v___f_2257_;
v___y_2208_ = v_run_x27_2255_;
goto v___jp_2203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9___boxed(lean_object* v___x_2264_, lean_object* v_cls_2265_, lean_object* v___x_2266_, lean_object* v___x_2267_, lean_object* v_____r_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v___x_479014__boxed_2278_; lean_object* v_res_2279_; 
v___x_479014__boxed_2278_ = lean_unbox(v___x_2264_);
v_res_2279_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9(v___x_479014__boxed_2278_, v_cls_2265_, v___x_2266_, v___x_2267_, v_____r_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v___x_2267_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(lean_object* v_cls_2283_, lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_ref_2290_; lean_object* v___x_2291_; lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2336_; 
v_ref_2290_ = lean_ctor_get(v___y_2287_, 5);
v___x_2291_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3_spec__7(v_msg_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2336_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2336_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v_traceState_2297_; lean_object* v_env_2298_; lean_object* v_nextMacroScope_2299_; lean_object* v_ngen_2300_; lean_object* v_auxDeclNGen_2301_; lean_object* v_cache_2302_; lean_object* v_messages_2303_; lean_object* v_infoState_2304_; lean_object* v_snapshotTasks_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2335_; 
v___x_2296_ = lean_st_ref_take(v___y_2288_);
v_traceState_2297_ = lean_ctor_get(v___x_2296_, 4);
v_env_2298_ = lean_ctor_get(v___x_2296_, 0);
v_nextMacroScope_2299_ = lean_ctor_get(v___x_2296_, 1);
v_ngen_2300_ = lean_ctor_get(v___x_2296_, 2);
v_auxDeclNGen_2301_ = lean_ctor_get(v___x_2296_, 3);
v_cache_2302_ = lean_ctor_get(v___x_2296_, 5);
v_messages_2303_ = lean_ctor_get(v___x_2296_, 6);
v_infoState_2304_ = lean_ctor_get(v___x_2296_, 7);
v_snapshotTasks_2305_ = lean_ctor_get(v___x_2296_, 8);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2307_ = v___x_2296_;
v_isShared_2308_ = v_isSharedCheck_2335_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_snapshotTasks_2305_);
lean_inc(v_infoState_2304_);
lean_inc(v_messages_2303_);
lean_inc(v_cache_2302_);
lean_inc(v_traceState_2297_);
lean_inc(v_auxDeclNGen_2301_);
lean_inc(v_ngen_2300_);
lean_inc(v_nextMacroScope_2299_);
lean_inc(v_env_2298_);
lean_dec(v___x_2296_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2335_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
uint64_t v_tid_2309_; lean_object* v_traces_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2334_; 
v_tid_2309_ = lean_ctor_get_uint64(v_traceState_2297_, sizeof(void*)*1);
v_traces_2310_ = lean_ctor_get(v_traceState_2297_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_traceState_2297_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2312_ = v_traceState_2297_;
v_isShared_2313_ = v_isSharedCheck_2334_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_traces_2310_);
lean_dec(v_traceState_2297_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2334_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; double v___x_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2314_ = lean_box(0);
v___x_2315_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0);
v___x_2316_ = 0;
v___x_2317_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_2318_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2318_, 0, v_cls_2283_);
lean_ctor_set(v___x_2318_, 1, v___x_2314_);
lean_ctor_set(v___x_2318_, 2, v___x_2317_);
lean_ctor_set_float(v___x_2318_, sizeof(void*)*3, v___x_2315_);
lean_ctor_set_float(v___x_2318_, sizeof(void*)*3 + 8, v___x_2315_);
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*3 + 16, v___x_2316_);
v___x_2319_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__1));
v___x_2320_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v_a_2292_);
lean_ctor_set(v___x_2320_, 2, v___x_2319_);
lean_inc(v_ref_2290_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v_ref_2290_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l_Lean_PersistentArray_push___redArg(v_traces_2310_, v___x_2321_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2322_);
v___x_2324_ = v___x_2312_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2322_);
lean_ctor_set_uint64(v_reuseFailAlloc_2333_, sizeof(void*)*1, v_tid_2309_);
v___x_2324_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 4, v___x_2324_);
v___x_2326_ = v___x_2307_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_env_2298_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_nextMacroScope_2299_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_ngen_2300_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_auxDeclNGen_2301_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2332_, 5, v_cache_2302_);
lean_ctor_set(v_reuseFailAlloc_2332_, 6, v_messages_2303_);
lean_ctor_set(v_reuseFailAlloc_2332_, 7, v_infoState_2304_);
lean_ctor_set(v_reuseFailAlloc_2332_, 8, v_snapshotTasks_2305_);
v___x_2326_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = lean_st_ref_set(v___y_2288_, v___x_2326_);
v___x_2328_ = lean_box(0);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2328_);
v___x_2330_ = v___x_2294_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___boxed(lean_object* v_cls_2337_, lean_object* v_msg_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_2337_, v_msg_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
return v_res_2344_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4(void){
_start:
{
lean_object* v_cls_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_cls_2352_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3));
v___x_2353_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
v___x_2354_ = l_Lean_Name_append(v___x_2353_, v_cls_2352_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__5));
v___x_2357_ = l_Lean_stringToMessageData(v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
uint8_t v___y_2372_; uint8_t v___y_2373_; lean_object* v___y_2374_; lean_object* v_options_2389_; lean_object* v_inheritedTraceOptions_2390_; uint8_t v_hasTrace_2391_; lean_object* v_cls_2392_; lean_object* v___y_2394_; lean_object* v___y_2395_; uint8_t v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; uint8_t v___y_2408_; uint8_t v___y_2409_; lean_object* v___y_2410_; lean_object* v_a_2411_; lean_object* v___y_2421_; uint8_t v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; uint8_t v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; uint8_t v___y_2435_; uint8_t v___y_2436_; lean_object* v___y_2437_; lean_object* v_a_2438_; uint8_t v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; uint8_t v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; uint8_t v___y_2464_; uint8_t v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2508_; uint8_t v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; uint8_t v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; uint8_t v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; uint8_t v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; uint8_t v___y_2590_; lean_object* v_a_2591_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; uint8_t v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; uint8_t v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; uint8_t v___y_2617_; lean_object* v_a_2618_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; uint8_t v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; uint8_t v___y_2646_; lean_object* v___y_2688_; uint8_t v_fixedInt_2689_; uint8_t v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; uint8_t v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2737_; lean_object* v___y_2738_; uint8_t v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; uint8_t v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; uint8_t v___y_2753_; lean_object* v_a_2754_; lean_object* v___y_2764_; lean_object* v___y_2765_; uint8_t v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; uint8_t v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v_a_2781_; lean_object* v___y_2794_; uint8_t v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; uint8_t v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2809_; lean_object* v___y_2851_; uint8_t v_fixedInt_2852_; uint8_t v_enums_2853_; uint8_t v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v___y_2888_; uint8_t v___y_2902_; lean_object* v___y_2903_; uint8_t v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; uint8_t v___y_2918_; lean_object* v_a_2919_; uint8_t v___y_2932_; lean_object* v___y_2933_; uint8_t v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; uint8_t v___y_2948_; lean_object* v_a_2949_; uint8_t v___y_2959_; lean_object* v___y_2960_; uint8_t v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; uint8_t v___y_2974_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; uint8_t v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; uint8_t v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; uint8_t v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v_a_3072_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; uint8_t v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; uint8_t v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; uint8_t v___y_3098_; lean_object* v_a_3099_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; uint8_t v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; uint8_t v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; uint8_t v___y_3127_; lean_object* v___y_3169_; uint8_t v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; uint8_t v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3215_; uint8_t v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; uint8_t v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; lean_object* v_a_3231_; lean_object* v___y_3241_; uint8_t v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; lean_object* v___y_3256_; lean_object* v_a_3257_; lean_object* v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; uint8_t v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; uint8_t v___y_3284_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; uint8_t v___y_3334_; uint8_t v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; uint8_t v___y_3371_; lean_object* v_snd_3372_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; uint8_t v___y_3415_; uint8_t v___y_3416_; lean_object* v_g_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; 
v_options_2389_ = lean_ctor_get(v_a_2368_, 2);
v_inheritedTraceOptions_2390_ = lean_ctor_get(v_a_2368_, 13);
v_hasTrace_2391_ = lean_ctor_get_uint8(v_options_2389_, sizeof(void*)*1);
v_cls_2392_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3));
if (v_hasTrace_2391_ == 0)
{
lean_object* v___x_3481_; lean_object* v_goal_3482_; 
v___x_3481_ = lean_st_ref_get(v_a_2363_);
v_goal_3482_ = lean_ctor_get(v___x_3481_, 4);
lean_inc(v_goal_3482_);
lean_dec(v___x_3481_);
v_g_3419_ = v_goal_3482_;
v___y_3420_ = v_a_2362_;
v___y_3421_ = v_a_2363_;
v___y_3422_ = v_a_2364_;
v___y_3423_ = v_a_2365_;
v___y_3424_ = v_a_2366_;
v___y_3425_ = v_a_2367_;
v___y_3426_ = v_a_2368_;
v___y_3427_ = v_a_2369_;
goto v___jp_3418_;
}
else
{
lean_object* v___f_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v_a_3490_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v_a_3502_; lean_object* v___y_3505_; lean_object* v___y_3506_; uint8_t v_a_3507_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v_snd_3522_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v_a_3557_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v_a_3572_; lean_object* v___y_3575_; lean_object* v___y_3576_; uint8_t v_a_3577_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v_snd_3592_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; uint8_t v___y_3622_; 
v___f_3483_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__8));
v___x_3484_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3485_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2390_, v_options_2389_, v___x_3485_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3698_ = l_Lean_trace_profiler;
v___x_3699_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2389_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; lean_object* v_goal_3701_; 
v___x_3700_ = lean_st_ref_get(v_a_2363_);
v_goal_3701_ = lean_ctor_get(v___x_3700_, 4);
lean_inc(v_goal_3701_);
lean_dec(v___x_3700_);
v_g_3419_ = v_goal_3701_;
v___y_3420_ = v_a_2362_;
v___y_3421_ = v_a_2363_;
v___y_3422_ = v_a_2364_;
v___y_3423_ = v_a_2365_;
v___y_3424_ = v_a_2366_;
v___y_3425_ = v_a_2367_;
v___y_3426_ = v_a_2368_;
v___y_3427_ = v_a_2369_;
goto v___jp_3418_;
}
else
{
goto v___jp_3624_;
}
}
else
{
goto v___jp_3624_;
}
v___jp_3487_:
{
lean_object* v___x_3491_; double v___x_3492_; double v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3491_ = lean_io_get_num_heartbeats();
v___x_3492_ = lean_float_of_nat(v___y_3489_);
v___x_3493_ = lean_float_of_nat(v___x_3491_);
v___x_3494_ = lean_box_float(v___x_3492_);
v___x_3495_ = lean_box_float(v___x_3493_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3494_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v_a_3490_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v_hasTrace_2391_, v___x_3484_, v_options_2389_, v___x_3486_, v___y_3488_, v___f_3483_, v___x_3497_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_3498_;
}
v___jp_3499_:
{
lean_object* v___x_3503_; 
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_a_3502_);
v___y_3488_ = v___y_3500_;
v___y_3489_ = v___y_3501_;
v_a_3490_ = v___x_3503_;
goto v___jp_3487_;
}
v___jp_3504_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = lean_box(v_a_3507_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
v___y_3488_ = v___y_3505_;
v___y_3489_ = v___y_3506_;
v_a_3490_ = v___x_3509_;
goto v___jp_3487_;
}
v___jp_3510_:
{
if (lean_obj_tag(v___y_3513_) == 0)
{
lean_object* v_a_3514_; uint8_t v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___y_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___y_3513_, 1);
v___x_3515_ = lean_unbox(v_a_3514_);
lean_dec(v_a_3514_);
v___y_3505_ = v___y_3511_;
v___y_3506_ = v___y_3512_;
v_a_3507_ = v___x_3515_;
goto v___jp_3504_;
}
else
{
lean_object* v_a_3516_; 
v_a_3516_ = lean_ctor_get(v___y_3513_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___y_3513_, 1);
v___y_3500_ = v___y_3511_;
v___y_3501_ = v___y_3512_;
v_a_3502_ = v_a_3516_;
goto v___jp_3499_;
}
}
v___jp_3517_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = lean_st_ref_set(v_a_2363_, v_snd_3522_);
v___x_3524_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3539_; 
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v___x_3524_, 0);
lean_dec(v_unused_3540_);
v___x_3526_ = v___x_3524_;
v_isShared_3527_ = v_isSharedCheck_3539_;
goto v_resetjp_3525_;
}
else
{
lean_dec(v___x_3524_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3539_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
if (v___x_3486_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_del_object(v___x_3526_);
lean_dec(v___y_3521_);
v___x_3528_ = lean_box(0);
lean_inc(v_a_2369_);
lean_inc_ref(v_a_2368_);
lean_inc(v_a_2367_);
lean_inc_ref(v_a_2366_);
lean_inc(v_a_2365_);
lean_inc_ref(v_a_2364_);
lean_inc(v_a_2363_);
lean_inc_ref(v_a_2362_);
v___x_3529_ = lean_apply_10(v___y_3520_, v___x_3528_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, lean_box(0));
v___y_3511_ = v___y_3518_;
v___y_3512_ = v___y_3519_;
v___y_3513_ = v___x_3529_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6);
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 1);
lean_ctor_set(v___x_3526_, 0, v___y_3521_);
v___x_3532_ = v___x_3526_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___y_3521_);
v___x_3532_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3530_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_2392_, v___x_3533_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
lean_inc(v_a_2369_);
lean_inc_ref(v_a_2368_);
lean_inc(v_a_2367_);
lean_inc_ref(v_a_2366_);
lean_inc(v_a_2365_);
lean_inc_ref(v_a_2364_);
lean_inc(v_a_2363_);
lean_inc_ref(v_a_2362_);
v___x_3536_ = lean_apply_10(v___y_3520_, v_a_3535_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, lean_box(0));
v___y_3511_ = v___y_3518_;
v___y_3512_ = v___y_3519_;
v___y_3513_ = v___x_3536_;
goto v___jp_3510_;
}
else
{
lean_object* v_a_3537_; 
lean_dec_ref(v___y_3520_);
v_a_3537_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3534_, 1);
v___y_3500_ = v___y_3518_;
v___y_3501_ = v___y_3519_;
v_a_3502_ = v_a_3537_;
goto v___jp_3499_;
}
}
}
}
}
else
{
lean_object* v_a_3541_; 
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
v_a_3541_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3524_, 1);
v___y_3500_ = v___y_3518_;
v___y_3501_ = v___y_3519_;
v_a_3502_ = v_a_3541_;
goto v___jp_3499_;
}
}
v___jp_3542_:
{
lean_object* v___x_3553_; 
lean_inc(v___y_3551_);
v___x_3553_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3553_, 0, v___y_3545_);
lean_ctor_set(v___x_3553_, 1, v___y_3544_);
lean_ctor_set(v___x_3553_, 2, v___y_3547_);
lean_ctor_set(v___x_3553_, 3, v___y_3548_);
lean_ctor_set(v___x_3553_, 4, v___y_3551_);
lean_ctor_set(v___x_3553_, 5, v___y_3546_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*6, v___y_3552_);
v___y_3518_ = v___y_3543_;
v___y_3519_ = v___y_3549_;
v___y_3520_ = v___y_3550_;
v___y_3521_ = v___y_3551_;
v_snd_3522_ = v___x_3553_;
goto v___jp_3517_;
}
v___jp_3554_:
{
lean_object* v___x_3558_; double v___x_3559_; double v___x_3560_; double v___x_3561_; double v___x_3562_; double v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3558_ = lean_io_mono_nanos_now();
v___x_3559_ = lean_float_of_nat(v___y_3556_);
v___x_3560_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3561_ = lean_float_div(v___x_3559_, v___x_3560_);
v___x_3562_ = lean_float_of_nat(v___x_3558_);
v___x_3563_ = lean_float_div(v___x_3562_, v___x_3560_);
v___x_3564_ = lean_box_float(v___x_3561_);
v___x_3565_ = lean_box_float(v___x_3563_);
v___x_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3567_, 0, v_a_3557_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v_hasTrace_2391_, v___x_3484_, v_options_2389_, v___x_3486_, v___y_3555_, v___f_3483_, v___x_3567_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_3568_;
}
v___jp_3569_:
{
lean_object* v___x_3573_; 
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v_a_3572_);
v___y_3555_ = v___y_3570_;
v___y_3556_ = v___y_3571_;
v_a_3557_ = v___x_3573_;
goto v___jp_3554_;
}
v___jp_3574_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_box(v_a_3577_);
v___x_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
v___y_3555_ = v___y_3575_;
v___y_3556_ = v___y_3576_;
v_a_3557_ = v___x_3579_;
goto v___jp_3554_;
}
v___jp_3580_:
{
if (lean_obj_tag(v___y_3583_) == 0)
{
lean_object* v_a_3584_; uint8_t v___x_3585_; 
v_a_3584_ = lean_ctor_get(v___y_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___y_3583_, 1);
v___x_3585_ = lean_unbox(v_a_3584_);
lean_dec(v_a_3584_);
v___y_3575_ = v___y_3581_;
v___y_3576_ = v___y_3582_;
v_a_3577_ = v___x_3585_;
goto v___jp_3574_;
}
else
{
lean_object* v_a_3586_; 
v_a_3586_ = lean_ctor_get(v___y_3583_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___y_3583_, 1);
v___y_3570_ = v___y_3581_;
v___y_3571_ = v___y_3582_;
v_a_3572_ = v_a_3586_;
goto v___jp_3569_;
}
}
v___jp_3587_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = lean_st_ref_set(v_a_2363_, v_snd_3592_);
v___x_3594_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3609_; 
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; 
v_unused_3610_ = lean_ctor_get(v___x_3594_, 0);
lean_dec(v_unused_3610_);
v___x_3596_ = v___x_3594_;
v_isShared_3597_ = v_isSharedCheck_3609_;
goto v_resetjp_3595_;
}
else
{
lean_dec(v___x_3594_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3609_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
if (v___x_3486_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_del_object(v___x_3596_);
lean_dec(v___y_3590_);
v___x_3598_ = lean_box(0);
lean_inc(v_a_2369_);
lean_inc_ref(v_a_2368_);
lean_inc(v_a_2367_);
lean_inc_ref(v_a_2366_);
lean_inc(v_a_2365_);
lean_inc_ref(v_a_2364_);
lean_inc(v_a_2363_);
lean_inc_ref(v_a_2362_);
v___x_3599_ = lean_apply_10(v___y_3591_, v___x_3598_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, lean_box(0));
v___y_3581_ = v___y_3588_;
v___y_3582_ = v___y_3589_;
v___y_3583_ = v___x_3599_;
goto v___jp_3580_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6);
if (v_isShared_3597_ == 0)
{
lean_ctor_set_tag(v___x_3596_, 1);
lean_ctor_set(v___x_3596_, 0, v___y_3590_);
v___x_3602_ = v___x_3596_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___y_3590_);
v___x_3602_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3600_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_2392_, v___x_3603_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3606_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref_known(v___x_3604_, 1);
lean_inc(v_a_2369_);
lean_inc_ref(v_a_2368_);
lean_inc(v_a_2367_);
lean_inc_ref(v_a_2366_);
lean_inc(v_a_2365_);
lean_inc_ref(v_a_2364_);
lean_inc(v_a_2363_);
lean_inc_ref(v_a_2362_);
v___x_3606_ = lean_apply_10(v___y_3591_, v_a_3605_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, lean_box(0));
v___y_3581_ = v___y_3588_;
v___y_3582_ = v___y_3589_;
v___y_3583_ = v___x_3606_;
goto v___jp_3580_;
}
else
{
lean_object* v_a_3607_; 
lean_dec_ref(v___y_3591_);
v_a_3607_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3604_, 1);
v___y_3570_ = v___y_3588_;
v___y_3571_ = v___y_3589_;
v_a_3572_ = v_a_3607_;
goto v___jp_3569_;
}
}
}
}
}
else
{
lean_object* v_a_3611_; 
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
v_a_3611_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3594_, 1);
v___y_3570_ = v___y_3588_;
v___y_3571_ = v___y_3589_;
v_a_3572_ = v_a_3611_;
goto v___jp_3569_;
}
}
v___jp_3612_:
{
lean_object* v___x_3623_; 
lean_inc(v___y_3615_);
v___x_3623_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3623_, 0, v___y_3617_);
lean_ctor_set(v___x_3623_, 1, v___y_3619_);
lean_ctor_set(v___x_3623_, 2, v___y_3618_);
lean_ctor_set(v___x_3623_, 3, v___y_3620_);
lean_ctor_set(v___x_3623_, 4, v___y_3615_);
lean_ctor_set(v___x_3623_, 5, v___y_3616_);
lean_ctor_set_uint8(v___x_3623_, sizeof(void*)*6, v___y_3622_);
v___y_3588_ = v___y_3613_;
v___y_3589_ = v___y_3614_;
v___y_3590_ = v___y_3615_;
v___y_3591_ = v___y_3621_;
v_snd_3592_ = v___x_3623_;
goto v___jp_3587_;
}
v___jp_3624_:
{
lean_object* v___x_3625_; lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3697_; 
v___x_3625_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_a_2369_);
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3697_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3697_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3631_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2389_, v___x_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v_goal_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3632_ = lean_io_mono_nanos_now();
v___x_3633_ = lean_st_ref_get(v_a_2363_);
v_goal_3634_ = lean_ctor_get(v___x_3633_, 4);
lean_inc(v_goal_3634_);
lean_dec(v___x_3633_);
v___x_3635_ = lean_box(v_hasTrace_2391_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set_tag(v___x_3628_, 1);
lean_ctor_set(v___x_3628_, 0, v___x_3635_);
v___x_3637_ = v___x_3628_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_MVarId_falseOrByContra(v_goal_3634_, v___x_3637_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
lean_dec_ref(v___x_3637_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3638_, 1);
if (lean_obj_tag(v_a_3639_) == 1)
{
lean_object* v_val_3640_; lean_object* v___x_3641_; 
v_val_3640_ = lean_ctor_get(v_a_3639_, 0);
lean_inc(v_val_3640_);
lean_dec_ref_known(v_a_3639_, 1);
v___x_3641_ = l_Lean_Meta_Sym_preprocessMVar(v_val_3640_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3643_; lean_object* v_rewriteSimpCache_3644_; lean_object* v_rewriteDSimpCache_3645_; lean_object* v_acCache_3646_; lean_object* v_typeAnalysis_3647_; lean_object* v_goal_3648_; lean_object* v_hypotheses_3649_; uint8_t v_didChange_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3661_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v___x_3643_ = lean_st_ref_take(v_a_2363_);
v_rewriteSimpCache_3644_ = lean_ctor_get(v___x_3643_, 0);
v_rewriteDSimpCache_3645_ = lean_ctor_get(v___x_3643_, 1);
v_acCache_3646_ = lean_ctor_get(v___x_3643_, 2);
v_typeAnalysis_3647_ = lean_ctor_get(v___x_3643_, 3);
v_goal_3648_ = lean_ctor_get(v___x_3643_, 4);
v_hypotheses_3649_ = lean_ctor_get(v___x_3643_, 5);
v_didChange_3650_ = lean_ctor_get_uint8(v___x_3643_, sizeof(void*)*6);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3652_ = v___x_3643_;
v_isShared_3653_ = v_isSharedCheck_3661_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_hypotheses_3649_);
lean_inc(v_goal_3648_);
lean_inc(v_typeAnalysis_3647_);
lean_inc(v_acCache_3646_);
lean_inc(v_rewriteDSimpCache_3645_);
lean_inc(v_rewriteSimpCache_3644_);
lean_dec(v___x_3643_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3661_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___f_3656_; 
v___x_3654_ = lean_box(v___x_3631_);
v___x_3655_ = lean_box(v_hasTrace_2391_);
v___f_3656_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___boxed), 15, 5);
lean_closure_set(v___f_3656_, 0, v___x_3654_);
lean_closure_set(v___f_3656_, 1, v___x_3655_);
lean_closure_set(v___f_3656_, 2, v_cls_2392_);
lean_closure_set(v___f_3656_, 3, v___x_3484_);
lean_closure_set(v___f_3656_, 4, v___x_3630_);
if (v_didChange_3650_ == 0)
{
uint8_t v___x_3657_; 
lean_del_object(v___x_3652_);
v___x_3657_ = l_Lean_instBEqMVarId_beq(v_a_3642_, v_goal_3648_);
lean_dec(v_goal_3648_);
if (v___x_3657_ == 0)
{
v___y_3613_ = v_a_3626_;
v___y_3614_ = v___x_3632_;
v___y_3615_ = v_a_3642_;
v___y_3616_ = v_hypotheses_3649_;
v___y_3617_ = v_rewriteSimpCache_3644_;
v___y_3618_ = v_acCache_3646_;
v___y_3619_ = v_rewriteDSimpCache_3645_;
v___y_3620_ = v_typeAnalysis_3647_;
v___y_3621_ = v___f_3656_;
v___y_3622_ = v_hasTrace_2391_;
goto v___jp_3612_;
}
else
{
v___y_3613_ = v_a_3626_;
v___y_3614_ = v___x_3632_;
v___y_3615_ = v_a_3642_;
v___y_3616_ = v_hypotheses_3649_;
v___y_3617_ = v_rewriteSimpCache_3644_;
v___y_3618_ = v_acCache_3646_;
v___y_3619_ = v_rewriteDSimpCache_3645_;
v___y_3620_ = v_typeAnalysis_3647_;
v___y_3621_ = v___f_3656_;
v___y_3622_ = v_didChange_3650_;
goto v___jp_3612_;
}
}
else
{
lean_object* v___x_3659_; 
lean_dec(v_goal_3648_);
lean_inc(v_a_3642_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 4, v_a_3642_);
v___x_3659_ = v___x_3652_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_rewriteSimpCache_3644_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_rewriteDSimpCache_3645_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_acCache_3646_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_typeAnalysis_3647_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_a_3642_);
lean_ctor_set(v_reuseFailAlloc_3660_, 5, v_hypotheses_3649_);
lean_ctor_set_uint8(v_reuseFailAlloc_3660_, sizeof(void*)*6, v_didChange_3650_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
v___y_3588_ = v_a_3626_;
v___y_3589_ = v___x_3632_;
v___y_3590_ = v_a_3642_;
v___y_3591_ = v___f_3656_;
v_snd_3592_ = v___x_3659_;
goto v___jp_3587_;
}
}
}
}
else
{
lean_object* v_a_3662_; 
v_a_3662_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3641_, 1);
v___y_3570_ = v_a_3626_;
v___y_3571_ = v___x_3632_;
v_a_3572_ = v_a_3662_;
goto v___jp_3569_;
}
}
else
{
lean_dec(v_a_3639_);
v___y_3575_ = v_a_3626_;
v___y_3576_ = v___x_3632_;
v_a_3577_ = v_hasTrace_2391_;
goto v___jp_3574_;
}
}
else
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3638_, 1);
v___y_3570_ = v_a_3626_;
v___y_3571_ = v___x_3632_;
v_a_3572_ = v_a_3663_;
goto v___jp_3569_;
}
}
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v_goal_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
v___x_3665_ = lean_io_get_num_heartbeats();
v___x_3666_ = lean_st_ref_get(v_a_2363_);
v_goal_3667_ = lean_ctor_get(v___x_3666_, 4);
lean_inc(v_goal_3667_);
lean_dec(v___x_3666_);
v___x_3668_ = lean_box(v___x_3631_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set_tag(v___x_3628_, 1);
lean_ctor_set(v___x_3628_, 0, v___x_3668_);
v___x_3670_ = v___x_3628_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Lean_MVarId_falseOrByContra(v_goal_3667_, v___x_3670_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
lean_dec_ref(v___x_3670_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3671_, 1);
if (lean_obj_tag(v_a_3672_) == 1)
{
lean_object* v_val_3673_; lean_object* v___x_3674_; 
v_val_3673_ = lean_ctor_get(v_a_3672_, 0);
lean_inc(v_val_3673_);
lean_dec_ref_known(v_a_3672_, 1);
v___x_3674_ = l_Lean_Meta_Sym_preprocessMVar(v_val_3673_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; lean_object* v___x_3676_; lean_object* v_rewriteSimpCache_3677_; lean_object* v_rewriteDSimpCache_3678_; lean_object* v_acCache_3679_; lean_object* v_typeAnalysis_3680_; lean_object* v_goal_3681_; lean_object* v_hypotheses_3682_; uint8_t v_didChange_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3693_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_a_3675_);
lean_dec_ref_known(v___x_3674_, 1);
v___x_3676_ = lean_st_ref_take(v_a_2363_);
v_rewriteSimpCache_3677_ = lean_ctor_get(v___x_3676_, 0);
v_rewriteDSimpCache_3678_ = lean_ctor_get(v___x_3676_, 1);
v_acCache_3679_ = lean_ctor_get(v___x_3676_, 2);
v_typeAnalysis_3680_ = lean_ctor_get(v___x_3676_, 3);
v_goal_3681_ = lean_ctor_get(v___x_3676_, 4);
v_hypotheses_3682_ = lean_ctor_get(v___x_3676_, 5);
v_didChange_3683_ = lean_ctor_get_uint8(v___x_3676_, sizeof(void*)*6);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3685_ = v___x_3676_;
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_hypotheses_3682_);
lean_inc(v_goal_3681_);
lean_inc(v_typeAnalysis_3680_);
lean_inc(v_acCache_3679_);
lean_inc(v_rewriteDSimpCache_3678_);
lean_inc(v_rewriteSimpCache_3677_);
lean_dec(v___x_3676_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3687_; lean_object* v___f_3688_; 
v___x_3687_ = lean_box(v___x_3631_);
v___f_3688_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9___boxed), 14, 4);
lean_closure_set(v___f_3688_, 0, v___x_3687_);
lean_closure_set(v___f_3688_, 1, v_cls_2392_);
lean_closure_set(v___f_3688_, 2, v___x_3484_);
lean_closure_set(v___f_3688_, 3, v___x_3630_);
if (v_didChange_3683_ == 0)
{
uint8_t v___x_3689_; 
lean_del_object(v___x_3685_);
v___x_3689_ = l_Lean_instBEqMVarId_beq(v_a_3675_, v_goal_3681_);
lean_dec(v_goal_3681_);
if (v___x_3689_ == 0)
{
v___y_3543_ = v_a_3626_;
v___y_3544_ = v_rewriteDSimpCache_3678_;
v___y_3545_ = v_rewriteSimpCache_3677_;
v___y_3546_ = v_hypotheses_3682_;
v___y_3547_ = v_acCache_3679_;
v___y_3548_ = v_typeAnalysis_3680_;
v___y_3549_ = v___x_3665_;
v___y_3550_ = v___f_3688_;
v___y_3551_ = v_a_3675_;
v___y_3552_ = v___x_3631_;
goto v___jp_3542_;
}
else
{
v___y_3543_ = v_a_3626_;
v___y_3544_ = v_rewriteDSimpCache_3678_;
v___y_3545_ = v_rewriteSimpCache_3677_;
v___y_3546_ = v_hypotheses_3682_;
v___y_3547_ = v_acCache_3679_;
v___y_3548_ = v_typeAnalysis_3680_;
v___y_3549_ = v___x_3665_;
v___y_3550_ = v___f_3688_;
v___y_3551_ = v_a_3675_;
v___y_3552_ = v_didChange_3683_;
goto v___jp_3542_;
}
}
else
{
lean_object* v___x_3691_; 
lean_dec(v_goal_3681_);
lean_inc(v_a_3675_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v_a_3675_);
v___x_3691_ = v___x_3685_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_rewriteSimpCache_3677_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_rewriteDSimpCache_3678_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_acCache_3679_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v_typeAnalysis_3680_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v_a_3675_);
lean_ctor_set(v_reuseFailAlloc_3692_, 5, v_hypotheses_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3692_, sizeof(void*)*6, v_didChange_3683_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
v___y_3518_ = v_a_3626_;
v___y_3519_ = v___x_3665_;
v___y_3520_ = v___f_3688_;
v___y_3521_ = v_a_3675_;
v_snd_3522_ = v___x_3691_;
goto v___jp_3517_;
}
}
}
}
else
{
lean_object* v_a_3694_; 
v_a_3694_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3674_, 1);
v___y_3500_ = v_a_3626_;
v___y_3501_ = v___x_3665_;
v_a_3502_ = v_a_3694_;
goto v___jp_3499_;
}
}
else
{
lean_dec(v_a_3672_);
v___y_3505_ = v_a_3626_;
v___y_3506_ = v___x_3665_;
v_a_3507_ = v___x_3631_;
goto v___jp_3504_;
}
}
else
{
lean_object* v_a_3695_; 
v_a_3695_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3671_, 1);
v___y_3500_ = v_a_3626_;
v___y_3501_ = v___x_3665_;
v_a_3502_ = v_a_3695_;
goto v___jp_3499_;
}
}
}
}
}
}
v___jp_2371_:
{
if (lean_obj_tag(v___y_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2388_; 
v_a_2375_ = lean_ctor_get(v___y_2374_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___y_2374_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2377_ = v___y_2374_;
v_isShared_2378_ = v_isSharedCheck_2388_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___y_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2388_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
uint8_t v___x_2379_; 
v___x_2379_ = lean_unbox(v_a_2375_);
lean_dec(v_a_2375_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2380_ = lean_box(v___y_2372_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2380_);
v___x_2382_ = v___x_2377_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = lean_box(v___y_2373_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2384_);
v___x_2386_ = v___x_2377_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
return v___y_2374_;
}
}
v___jp_2393_:
{
lean_object* v___x_2412_; double v___x_2413_; double v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2412_ = lean_io_get_num_heartbeats();
v___x_2413_ = lean_float_of_nat(v___y_2394_);
v___x_2414_ = lean_float_of_nat(v___x_2412_);
v___x_2415_ = lean_box_float(v___x_2413_);
v___x_2416_ = lean_box_float(v___x_2414_);
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v_a_2411_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
lean_inc_ref(v___y_2407_);
lean_inc_ref(v___y_2398_);
v___x_2419_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_2408_, v___y_2398_, v___y_2403_, v___y_2396_, v___y_2395_, v___y_2407_, v___x_2418_, v___y_2401_, v___y_2400_, v___y_2399_, v___y_2405_, v___y_2406_, v___y_2397_, v___y_2404_, v___y_2410_);
v___y_2372_ = v___y_2402_;
v___y_2373_ = v___y_2409_;
v___y_2374_ = v___x_2419_;
goto v___jp_2371_;
}
v___jp_2420_:
{
lean_object* v___x_2439_; double v___x_2440_; double v___x_2441_; double v___x_2442_; double v___x_2443_; double v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2439_ = lean_io_mono_nanos_now();
v___x_2440_ = lean_float_of_nat(v___y_2423_);
v___x_2441_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2442_ = lean_float_div(v___x_2440_, v___x_2441_);
v___x_2443_ = lean_float_of_nat(v___x_2439_);
v___x_2444_ = lean_float_div(v___x_2443_, v___x_2441_);
v___x_2445_ = lean_box_float(v___x_2442_);
v___x_2446_ = lean_box_float(v___x_2444_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_a_2438_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
lean_inc_ref(v___y_2434_);
lean_inc_ref(v___y_2425_);
v___x_2449_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_2435_, v___y_2425_, v___y_2430_, v___y_2422_, v___y_2421_, v___y_2434_, v___x_2448_, v___y_2428_, v___y_2427_, v___y_2426_, v___y_2432_, v___y_2433_, v___y_2424_, v___y_2431_, v___y_2437_);
v___y_2372_ = v___y_2429_;
v___y_2373_ = v___y_2436_;
v___y_2374_ = v___x_2449_;
goto v___jp_2371_;
}
v___jp_2450_:
{
lean_object* v___x_2467_; lean_object* v_a_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2467_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2466_);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v___x_2467_);
v___x_2469_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2470_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2457_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_io_mono_nanos_now();
lean_inc(v___y_2466_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2461_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2454_);
lean_inc(v___y_2455_);
lean_inc_ref(v___y_2456_);
v___x_2472_ = lean_apply_9(v___y_2462_, v___y_2456_, v___y_2455_, v___y_2454_, v___y_2460_, v___y_2461_, v___y_2452_, v___y_2459_, v___y_2466_, lean_box(0));
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set_tag(v___x_2475_, 1);
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
v___y_2421_ = v_a_2468_;
v___y_2422_ = v___y_2451_;
v___y_2423_ = v___x_2471_;
v___y_2424_ = v___y_2452_;
v___y_2425_ = v___y_2453_;
v___y_2426_ = v___y_2454_;
v___y_2427_ = v___y_2455_;
v___y_2428_ = v___y_2456_;
v___y_2429_ = v___y_2458_;
v___y_2430_ = v___y_2457_;
v___y_2431_ = v___y_2459_;
v___y_2432_ = v___y_2460_;
v___y_2433_ = v___y_2461_;
v___y_2434_ = v___y_2463_;
v___y_2435_ = v___y_2464_;
v___y_2436_ = v___y_2465_;
v___y_2437_ = v___y_2466_;
v_a_2438_ = v___x_2478_;
goto v___jp_2420_;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
v_a_2481_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2472_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2472_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 0);
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
v___y_2421_ = v_a_2468_;
v___y_2422_ = v___y_2451_;
v___y_2423_ = v___x_2471_;
v___y_2424_ = v___y_2452_;
v___y_2425_ = v___y_2453_;
v___y_2426_ = v___y_2454_;
v___y_2427_ = v___y_2455_;
v___y_2428_ = v___y_2456_;
v___y_2429_ = v___y_2458_;
v___y_2430_ = v___y_2457_;
v___y_2431_ = v___y_2459_;
v___y_2432_ = v___y_2460_;
v___y_2433_ = v___y_2461_;
v___y_2434_ = v___y_2463_;
v___y_2435_ = v___y_2464_;
v___y_2436_ = v___y_2465_;
v___y_2437_ = v___y_2466_;
v_a_2438_ = v___x_2486_;
goto v___jp_2420_;
}
}
}
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2466_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2461_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2454_);
lean_inc(v___y_2455_);
lean_inc_ref(v___y_2456_);
v___x_2490_ = lean_apply_9(v___y_2462_, v___y_2456_, v___y_2455_, v___y_2454_, v___y_2460_, v___y_2461_, v___y_2452_, v___y_2459_, v___y_2466_, lean_box(0));
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 1);
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
v___y_2394_ = v___x_2489_;
v___y_2395_ = v_a_2468_;
v___y_2396_ = v___y_2451_;
v___y_2397_ = v___y_2452_;
v___y_2398_ = v___y_2453_;
v___y_2399_ = v___y_2454_;
v___y_2400_ = v___y_2455_;
v___y_2401_ = v___y_2456_;
v___y_2402_ = v___y_2458_;
v___y_2403_ = v___y_2457_;
v___y_2404_ = v___y_2459_;
v___y_2405_ = v___y_2460_;
v___y_2406_ = v___y_2461_;
v___y_2407_ = v___y_2463_;
v___y_2408_ = v___y_2464_;
v___y_2409_ = v___y_2465_;
v___y_2410_ = v___y_2466_;
v_a_2411_ = v___x_2496_;
goto v___jp_2393_;
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
v_a_2499_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2490_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2490_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 0);
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
v___y_2394_ = v___x_2489_;
v___y_2395_ = v_a_2468_;
v___y_2396_ = v___y_2451_;
v___y_2397_ = v___y_2452_;
v___y_2398_ = v___y_2453_;
v___y_2399_ = v___y_2454_;
v___y_2400_ = v___y_2455_;
v___y_2401_ = v___y_2456_;
v___y_2402_ = v___y_2458_;
v___y_2403_ = v___y_2457_;
v___y_2404_ = v___y_2459_;
v___y_2405_ = v___y_2460_;
v___y_2406_ = v___y_2461_;
v___y_2407_ = v___y_2463_;
v___y_2408_ = v___y_2464_;
v___y_2409_ = v___y_2465_;
v___y_2410_ = v___y_2466_;
v_a_2411_ = v___x_2504_;
goto v___jp_2393_;
}
}
}
}
}
v___jp_2507_:
{
lean_object* v___x_2518_; lean_object* v_a_2519_; lean_object* v___x_2520_; 
v___x_2518_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_2510_);
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_2519_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v_a_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; uint8_t v___x_2522_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
v___x_2522_ = lean_unbox(v_a_2521_);
if (v___x_2522_ == 0)
{
uint8_t v_shortCircuit_2523_; 
v_shortCircuit_2523_ = lean_ctor_get_uint8(v___y_2508_, sizeof(void*)*2 + 9);
if (v_shortCircuit_2523_ == 0)
{
lean_dec(v_a_2521_);
return v___x_2520_;
}
else
{
lean_object* v___x_2524_; lean_object* v_options_2525_; uint8_t v_hasTrace_2526_; 
lean_dec_ref_known(v___x_2520_, 1);
v___x_2524_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_options_2525_ = lean_ctor_get(v___y_2516_, 2);
v_hasTrace_2526_ = lean_ctor_get_uint8(v_options_2525_, sizeof(void*)*1);
if (v_hasTrace_2526_ == 0)
{
lean_object* v_run_x27_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_run_x27_2527_ = lean_ctor_get(v___x_2524_, 1);
lean_inc_ref(v_run_x27_2527_);
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
lean_inc_ref(v___y_2512_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
v___x_2528_ = lean_apply_9(v_run_x27_2527_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, lean_box(0));
v___x_2529_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
v___y_2372_ = v___x_2529_;
v___y_2373_ = v___y_2509_;
v___y_2374_ = v___x_2528_;
goto v___jp_2371_;
}
else
{
lean_object* v_run_x27_2530_; lean_object* v_inheritedTraceOptions_2531_; lean_object* v___f_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v_run_x27_2530_ = lean_ctor_get(v___x_2524_, 1);
v_inheritedTraceOptions_2531_ = lean_ctor_get(v___y_2516_, 13);
v___f_2532_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1);
v___x_2533_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_2534_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_2535_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2531_, v_options_2525_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = l_Lean_trace_profiler;
v___x_2537_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2525_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
lean_inc_ref(v_run_x27_2530_);
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
lean_inc(v___y_2513_);
lean_inc_ref(v___y_2512_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
v___x_2538_ = lean_apply_9(v_run_x27_2530_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, lean_box(0));
v___x_2539_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
v___y_2372_ = v___x_2539_;
v___y_2373_ = v___y_2509_;
v___y_2374_ = v___x_2538_;
goto v___jp_2371_;
}
else
{
uint8_t v___x_2540_; 
v___x_2540_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
lean_inc_ref(v_run_x27_2530_);
v___y_2451_ = v___x_2535_;
v___y_2452_ = v___y_2515_;
v___y_2453_ = v___x_2533_;
v___y_2454_ = v___y_2512_;
v___y_2455_ = v___y_2511_;
v___y_2456_ = v___y_2510_;
v___y_2457_ = v_options_2525_;
v___y_2458_ = v___x_2540_;
v___y_2459_ = v___y_2516_;
v___y_2460_ = v___y_2513_;
v___y_2461_ = v___y_2514_;
v___y_2462_ = v_run_x27_2530_;
v___y_2463_ = v___f_2532_;
v___y_2464_ = v_hasTrace_2526_;
v___y_2465_ = v___y_2509_;
v___y_2466_ = v___y_2517_;
goto v___jp_2450_;
}
}
else
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
lean_inc_ref(v_run_x27_2530_);
v___y_2451_ = v___x_2535_;
v___y_2452_ = v___y_2515_;
v___y_2453_ = v___x_2533_;
v___y_2454_ = v___y_2512_;
v___y_2455_ = v___y_2511_;
v___y_2456_ = v___y_2510_;
v___y_2457_ = v_options_2525_;
v___y_2458_ = v___x_2541_;
v___y_2459_ = v___y_2516_;
v___y_2460_ = v___y_2513_;
v___y_2461_ = v___y_2514_;
v___y_2462_ = v_run_x27_2530_;
v___y_2463_ = v___f_2532_;
v___y_2464_ = v_hasTrace_2526_;
v___y_2465_ = v___y_2509_;
v___y_2466_ = v___y_2517_;
goto v___jp_2450_;
}
}
}
}
else
{
lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_a_2521_);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v___x_2520_, 0);
lean_dec(v_unused_2550_);
v___x_2543_ = v___x_2520_;
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
else
{
lean_dec(v___x_2520_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_box(v___y_2509_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
else
{
return v___x_2520_;
}
}
v___jp_2551_:
{
if (lean_obj_tag(v___y_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2572_; 
v_a_2563_ = lean_ctor_get(v___y_2562_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___y_2562_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2565_ = v___y_2562_;
v_isShared_2566_ = v_isSharedCheck_2572_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___y_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2572_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
uint8_t v___x_2567_; 
v___x_2567_ = lean_unbox(v_a_2563_);
lean_dec(v_a_2563_);
if (v___x_2567_ == 0)
{
lean_del_object(v___x_2565_);
v___y_2508_ = v___y_2560_;
v___y_2509_ = v___y_2561_;
v___y_2510_ = v___y_2555_;
v___y_2511_ = v___y_2558_;
v___y_2512_ = v___y_2557_;
v___y_2513_ = v___y_2559_;
v___y_2514_ = v___y_2552_;
v___y_2515_ = v___y_2556_;
v___y_2516_ = v___y_2554_;
v___y_2517_ = v___y_2553_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = lean_box(v___y_2561_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2568_);
v___x_2570_ = v___x_2565_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
return v___y_2562_;
}
}
v___jp_2573_:
{
lean_object* v___x_2592_; double v___x_2593_; double v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2592_ = lean_io_get_num_heartbeats();
v___x_2593_ = lean_float_of_nat(v___y_2579_);
v___x_2594_ = lean_float_of_nat(v___x_2592_);
v___x_2595_ = lean_box_float(v___x_2593_);
v___x_2596_ = lean_box_float(v___x_2594_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v_a_2591_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
lean_inc_ref(v___y_2575_);
lean_inc_ref(v___y_2589_);
v___x_2599_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_2583_, v___y_2589_, v___y_2576_, v___y_2578_, v___y_2588_, v___y_2575_, v___x_2598_, v___y_2586_, v___y_2580_, v___y_2581_, v___y_2587_, v___y_2574_, v___y_2577_, v___y_2585_, v___y_2584_);
v___y_2552_ = v___y_2574_;
v___y_2553_ = v___y_2584_;
v___y_2554_ = v___y_2585_;
v___y_2555_ = v___y_2586_;
v___y_2556_ = v___y_2577_;
v___y_2557_ = v___y_2581_;
v___y_2558_ = v___y_2580_;
v___y_2559_ = v___y_2587_;
v___y_2560_ = v___y_2582_;
v___y_2561_ = v___y_2590_;
v___y_2562_ = v___x_2599_;
goto v___jp_2551_;
}
v___jp_2600_:
{
lean_object* v___x_2619_; double v___x_2620_; double v___x_2621_; double v___x_2622_; double v___x_2623_; double v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2619_ = lean_io_mono_nanos_now();
v___x_2620_ = lean_float_of_nat(v___y_2602_);
v___x_2621_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2622_ = lean_float_div(v___x_2620_, v___x_2621_);
v___x_2623_ = lean_float_of_nat(v___x_2619_);
v___x_2624_ = lean_float_div(v___x_2623_, v___x_2621_);
v___x_2625_ = lean_box_float(v___x_2622_);
v___x_2626_ = lean_box_float(v___x_2624_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v_a_2618_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
lean_inc_ref(v___y_2603_);
lean_inc_ref(v___y_2616_);
v___x_2629_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_2610_, v___y_2616_, v___y_2604_, v___y_2606_, v___y_2615_, v___y_2603_, v___x_2628_, v___y_2613_, v___y_2607_, v___y_2608_, v___y_2614_, v___y_2601_, v___y_2605_, v___y_2612_, v___y_2611_);
v___y_2552_ = v___y_2601_;
v___y_2553_ = v___y_2611_;
v___y_2554_ = v___y_2612_;
v___y_2555_ = v___y_2613_;
v___y_2556_ = v___y_2605_;
v___y_2557_ = v___y_2608_;
v___y_2558_ = v___y_2607_;
v___y_2559_ = v___y_2614_;
v___y_2560_ = v___y_2609_;
v___y_2561_ = v___y_2617_;
v___y_2562_ = v___x_2629_;
goto v___jp_2551_;
}
v___jp_2630_:
{
lean_object* v___x_2647_; lean_object* v_a_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2647_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2642_);
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v___x_2649_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2650_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2634_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_io_mono_nanos_now();
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v___y_2633_);
lean_inc_ref(v___y_2631_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2637_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2640_);
v___x_2652_ = lean_apply_9(v___y_2644_, v___y_2640_, v___y_2636_, v___y_2637_, v___y_2643_, v___y_2631_, v___y_2633_, v___y_2641_, v___y_2642_, lean_box(0));
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 1);
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
v___y_2601_ = v___y_2631_;
v___y_2602_ = v___x_2651_;
v___y_2603_ = v___y_2632_;
v___y_2604_ = v___y_2634_;
v___y_2605_ = v___y_2633_;
v___y_2606_ = v___y_2635_;
v___y_2607_ = v___y_2636_;
v___y_2608_ = v___y_2637_;
v___y_2609_ = v___y_2638_;
v___y_2610_ = v___y_2639_;
v___y_2611_ = v___y_2642_;
v___y_2612_ = v___y_2641_;
v___y_2613_ = v___y_2640_;
v___y_2614_ = v___y_2643_;
v___y_2615_ = v_a_2648_;
v___y_2616_ = v___y_2645_;
v___y_2617_ = v___y_2646_;
v_a_2618_ = v___x_2658_;
goto v___jp_2600_;
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
v_a_2661_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2652_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2652_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 0);
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
v___y_2601_ = v___y_2631_;
v___y_2602_ = v___x_2651_;
v___y_2603_ = v___y_2632_;
v___y_2604_ = v___y_2634_;
v___y_2605_ = v___y_2633_;
v___y_2606_ = v___y_2635_;
v___y_2607_ = v___y_2636_;
v___y_2608_ = v___y_2637_;
v___y_2609_ = v___y_2638_;
v___y_2610_ = v___y_2639_;
v___y_2611_ = v___y_2642_;
v___y_2612_ = v___y_2641_;
v___y_2613_ = v___y_2640_;
v___y_2614_ = v___y_2643_;
v___y_2615_ = v_a_2648_;
v___y_2616_ = v___y_2645_;
v___y_2617_ = v___y_2646_;
v_a_2618_ = v___x_2666_;
goto v___jp_2600_;
}
}
}
}
else
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v___y_2633_);
lean_inc_ref(v___y_2631_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2637_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2640_);
v___x_2670_ = lean_apply_9(v___y_2644_, v___y_2640_, v___y_2636_, v___y_2637_, v___y_2643_, v___y_2631_, v___y_2633_, v___y_2641_, v___y_2642_, lean_box(0));
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set_tag(v___x_2673_, 1);
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
v___y_2574_ = v___y_2631_;
v___y_2575_ = v___y_2632_;
v___y_2576_ = v___y_2634_;
v___y_2577_ = v___y_2633_;
v___y_2578_ = v___y_2635_;
v___y_2579_ = v___x_2669_;
v___y_2580_ = v___y_2636_;
v___y_2581_ = v___y_2637_;
v___y_2582_ = v___y_2638_;
v___y_2583_ = v___y_2639_;
v___y_2584_ = v___y_2642_;
v___y_2585_ = v___y_2641_;
v___y_2586_ = v___y_2640_;
v___y_2587_ = v___y_2643_;
v___y_2588_ = v_a_2648_;
v___y_2589_ = v___y_2645_;
v___y_2590_ = v___y_2646_;
v_a_2591_ = v___x_2676_;
goto v___jp_2573_;
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2670_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2670_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 0);
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
v___y_2574_ = v___y_2631_;
v___y_2575_ = v___y_2632_;
v___y_2576_ = v___y_2634_;
v___y_2577_ = v___y_2633_;
v___y_2578_ = v___y_2635_;
v___y_2579_ = v___x_2669_;
v___y_2580_ = v___y_2636_;
v___y_2581_ = v___y_2637_;
v___y_2582_ = v___y_2638_;
v___y_2583_ = v___y_2639_;
v___y_2584_ = v___y_2642_;
v___y_2585_ = v___y_2641_;
v___y_2586_ = v___y_2640_;
v___y_2587_ = v___y_2643_;
v___y_2588_ = v_a_2648_;
v___y_2589_ = v___y_2645_;
v___y_2590_ = v___y_2646_;
v_a_2591_ = v___x_2684_;
goto v___jp_2573_;
}
}
}
}
}
v___jp_2687_:
{
if (v_fixedInt_2689_ == 0)
{
v___y_2508_ = v___y_2688_;
v___y_2509_ = v___y_2690_;
v___y_2510_ = v___y_2691_;
v___y_2511_ = v___y_2692_;
v___y_2512_ = v___y_2693_;
v___y_2513_ = v___y_2694_;
v___y_2514_ = v___y_2695_;
v___y_2515_ = v___y_2696_;
v___y_2516_ = v___y_2697_;
v___y_2517_ = v___y_2698_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2699_; lean_object* v_options_2700_; uint8_t v_hasTrace_2701_; 
v___x_2699_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_options_2700_ = lean_ctor_get(v___y_2697_, 2);
v_hasTrace_2701_ = lean_ctor_get_uint8(v_options_2700_, sizeof(void*)*1);
if (v_hasTrace_2701_ == 0)
{
lean_object* v_run_x27_2702_; lean_object* v___x_2703_; 
v_run_x27_2702_ = lean_ctor_get(v___x_2699_, 1);
lean_inc_ref(v_run_x27_2702_);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
v___x_2703_ = lean_apply_9(v_run_x27_2702_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, lean_box(0));
v___y_2552_ = v___y_2695_;
v___y_2553_ = v___y_2698_;
v___y_2554_ = v___y_2697_;
v___y_2555_ = v___y_2691_;
v___y_2556_ = v___y_2696_;
v___y_2557_ = v___y_2693_;
v___y_2558_ = v___y_2692_;
v___y_2559_ = v___y_2694_;
v___y_2560_ = v___y_2688_;
v___y_2561_ = v___y_2690_;
v___y_2562_ = v___x_2703_;
goto v___jp_2551_;
}
else
{
lean_object* v_run_x27_2704_; lean_object* v_inheritedTraceOptions_2705_; lean_object* v___f_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v_run_x27_2704_ = lean_ctor_get(v___x_2699_, 1);
v_inheritedTraceOptions_2705_ = lean_ctor_get(v___y_2697_, 13);
v___f_2706_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4);
v___x_2707_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_2708_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_2709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2705_, v_options_2700_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2710_ = l_Lean_trace_profiler;
v___x_2711_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2700_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; 
lean_inc_ref(v_run_x27_2704_);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
v___x_2712_ = lean_apply_9(v_run_x27_2704_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, lean_box(0));
v___y_2552_ = v___y_2695_;
v___y_2553_ = v___y_2698_;
v___y_2554_ = v___y_2697_;
v___y_2555_ = v___y_2691_;
v___y_2556_ = v___y_2696_;
v___y_2557_ = v___y_2693_;
v___y_2558_ = v___y_2692_;
v___y_2559_ = v___y_2694_;
v___y_2560_ = v___y_2688_;
v___y_2561_ = v___y_2690_;
v___y_2562_ = v___x_2712_;
goto v___jp_2551_;
}
else
{
lean_inc_ref(v_run_x27_2704_);
v___y_2631_ = v___y_2695_;
v___y_2632_ = v___f_2706_;
v___y_2633_ = v___y_2696_;
v___y_2634_ = v_options_2700_;
v___y_2635_ = v___x_2709_;
v___y_2636_ = v___y_2692_;
v___y_2637_ = v___y_2693_;
v___y_2638_ = v___y_2688_;
v___y_2639_ = v_hasTrace_2701_;
v___y_2640_ = v___y_2691_;
v___y_2641_ = v___y_2697_;
v___y_2642_ = v___y_2698_;
v___y_2643_ = v___y_2694_;
v___y_2644_ = v_run_x27_2704_;
v___y_2645_ = v___x_2707_;
v___y_2646_ = v___y_2690_;
goto v___jp_2630_;
}
}
else
{
lean_inc_ref(v_run_x27_2704_);
v___y_2631_ = v___y_2695_;
v___y_2632_ = v___f_2706_;
v___y_2633_ = v___y_2696_;
v___y_2634_ = v_options_2700_;
v___y_2635_ = v___x_2709_;
v___y_2636_ = v___y_2692_;
v___y_2637_ = v___y_2693_;
v___y_2638_ = v___y_2688_;
v___y_2639_ = v_hasTrace_2701_;
v___y_2640_ = v___y_2691_;
v___y_2641_ = v___y_2697_;
v___y_2642_ = v___y_2698_;
v___y_2643_ = v___y_2694_;
v___y_2644_ = v_run_x27_2704_;
v___y_2645_ = v___x_2707_;
v___y_2646_ = v___y_2690_;
goto v___jp_2630_;
}
}
}
}
v___jp_2713_:
{
if (lean_obj_tag(v___y_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2735_; 
v_a_2725_ = lean_ctor_get(v___y_2724_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___y_2724_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2727_ = v___y_2724_;
v_isShared_2728_ = v_isSharedCheck_2735_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___y_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2735_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_unbox(v_a_2725_);
lean_dec(v_a_2725_);
if (v___x_2729_ == 0)
{
uint8_t v_fixedInt_2730_; 
lean_del_object(v___x_2727_);
v_fixedInt_2730_ = lean_ctor_get_uint8(v___y_2721_, sizeof(void*)*2 + 6);
v___y_2688_ = v___y_2721_;
v_fixedInt_2689_ = v_fixedInt_2730_;
v___y_2690_ = v___y_2723_;
v___y_2691_ = v___y_2716_;
v___y_2692_ = v___y_2717_;
v___y_2693_ = v___y_2720_;
v___y_2694_ = v___y_2719_;
v___y_2695_ = v___y_2715_;
v___y_2696_ = v___y_2722_;
v___y_2697_ = v___y_2718_;
v___y_2698_ = v___y_2714_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = lean_box(v___y_2723_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2731_);
v___x_2733_ = v___x_2727_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
return v___y_2724_;
}
}
v___jp_2736_:
{
lean_object* v___x_2755_; double v___x_2756_; double v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2755_ = lean_io_get_num_heartbeats();
v___x_2756_ = lean_float_of_nat(v___y_2742_);
v___x_2757_ = lean_float_of_nat(v___x_2755_);
v___x_2758_ = lean_box_float(v___x_2756_);
v___x_2759_ = lean_box_float(v___x_2757_);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v_a_2754_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
lean_inc_ref(v___y_2747_);
lean_inc_ref(v___y_2745_);
v___x_2762_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_2748_, v___y_2745_, v___y_2751_, v___y_2739_, v___y_2737_, v___y_2747_, v___x_2761_, v___y_2738_, v___y_2746_, v___y_2750_, v___y_2749_, v___y_2744_, v___y_2752_, v___y_2740_, v___y_2743_);
v___y_2714_ = v___y_2743_;
v___y_2715_ = v___y_2744_;
v___y_2716_ = v___y_2738_;
v___y_2717_ = v___y_2746_;
v___y_2718_ = v___y_2740_;
v___y_2719_ = v___y_2749_;
v___y_2720_ = v___y_2750_;
v___y_2721_ = v___y_2741_;
v___y_2722_ = v___y_2752_;
v___y_2723_ = v___y_2753_;
v___y_2724_ = v___x_2762_;
goto v___jp_2713_;
}
v___jp_2763_:
{
lean_object* v___x_2782_; double v___x_2783_; double v___x_2784_; double v___x_2785_; double v___x_2786_; double v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2782_ = lean_io_mono_nanos_now();
v___x_2783_ = lean_float_of_nat(v___y_2774_);
v___x_2784_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2785_ = lean_float_div(v___x_2783_, v___x_2784_);
v___x_2786_ = lean_float_of_nat(v___x_2782_);
v___x_2787_ = lean_float_div(v___x_2786_, v___x_2784_);
v___x_2788_ = lean_box_float(v___x_2785_);
v___x_2789_ = lean_box_float(v___x_2787_);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v_a_2781_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
lean_inc_ref(v___y_2773_);
lean_inc_ref(v___y_2771_);
v___x_2792_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_2775_, v___y_2771_, v___y_2778_, v___y_2766_, v___y_2764_, v___y_2773_, v___x_2791_, v___y_2765_, v___y_2772_, v___y_2777_, v___y_2776_, v___y_2770_, v___y_2779_, v___y_2767_, v___y_2769_);
v___y_2714_ = v___y_2769_;
v___y_2715_ = v___y_2770_;
v___y_2716_ = v___y_2765_;
v___y_2717_ = v___y_2772_;
v___y_2718_ = v___y_2767_;
v___y_2719_ = v___y_2776_;
v___y_2720_ = v___y_2777_;
v___y_2721_ = v___y_2768_;
v___y_2722_ = v___y_2779_;
v___y_2723_ = v___y_2780_;
v___y_2724_ = v___x_2792_;
goto v___jp_2713_;
}
v___jp_2793_:
{
lean_object* v___x_2810_; lean_object* v_a_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2810_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2800_);
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2810_);
v___x_2812_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2813_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2807_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_io_mono_nanos_now();
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2808_);
lean_inc_ref(v___y_2799_);
lean_inc(v___y_2805_);
lean_inc_ref(v___y_2806_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2794_);
v___x_2815_ = lean_apply_9(v___y_2797_, v___y_2794_, v___y_2802_, v___y_2806_, v___y_2805_, v___y_2799_, v___y_2808_, v___y_2796_, v___y_2800_, lean_box(0));
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set_tag(v___x_2818_, 1);
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
v___y_2764_ = v_a_2811_;
v___y_2765_ = v___y_2794_;
v___y_2766_ = v___y_2795_;
v___y_2767_ = v___y_2796_;
v___y_2768_ = v___y_2798_;
v___y_2769_ = v___y_2800_;
v___y_2770_ = v___y_2799_;
v___y_2771_ = v___y_2801_;
v___y_2772_ = v___y_2802_;
v___y_2773_ = v___y_2803_;
v___y_2774_ = v___x_2814_;
v___y_2775_ = v___y_2804_;
v___y_2776_ = v___y_2805_;
v___y_2777_ = v___y_2806_;
v___y_2778_ = v___y_2807_;
v___y_2779_ = v___y_2808_;
v___y_2780_ = v___y_2809_;
v_a_2781_ = v___x_2821_;
goto v___jp_2763_;
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
v_a_2824_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2815_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2815_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
lean_ctor_set_tag(v___x_2826_, 0);
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
v___y_2764_ = v_a_2811_;
v___y_2765_ = v___y_2794_;
v___y_2766_ = v___y_2795_;
v___y_2767_ = v___y_2796_;
v___y_2768_ = v___y_2798_;
v___y_2769_ = v___y_2800_;
v___y_2770_ = v___y_2799_;
v___y_2771_ = v___y_2801_;
v___y_2772_ = v___y_2802_;
v___y_2773_ = v___y_2803_;
v___y_2774_ = v___x_2814_;
v___y_2775_ = v___y_2804_;
v___y_2776_ = v___y_2805_;
v___y_2777_ = v___y_2806_;
v___y_2778_ = v___y_2807_;
v___y_2779_ = v___y_2808_;
v___y_2780_ = v___y_2809_;
v_a_2781_ = v___x_2829_;
goto v___jp_2763_;
}
}
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2808_);
lean_inc_ref(v___y_2799_);
lean_inc(v___y_2805_);
lean_inc_ref(v___y_2806_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2794_);
v___x_2833_ = lean_apply_9(v___y_2797_, v___y_2794_, v___y_2802_, v___y_2806_, v___y_2805_, v___y_2799_, v___y_2808_, v___y_2796_, v___y_2800_, lean_box(0));
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set_tag(v___x_2836_, 1);
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
v___y_2737_ = v_a_2811_;
v___y_2738_ = v___y_2794_;
v___y_2739_ = v___y_2795_;
v___y_2740_ = v___y_2796_;
v___y_2741_ = v___y_2798_;
v___y_2742_ = v___x_2832_;
v___y_2743_ = v___y_2800_;
v___y_2744_ = v___y_2799_;
v___y_2745_ = v___y_2801_;
v___y_2746_ = v___y_2802_;
v___y_2747_ = v___y_2803_;
v___y_2748_ = v___y_2804_;
v___y_2749_ = v___y_2805_;
v___y_2750_ = v___y_2806_;
v___y_2751_ = v___y_2807_;
v___y_2752_ = v___y_2808_;
v___y_2753_ = v___y_2809_;
v_a_2754_ = v___x_2839_;
goto v___jp_2736_;
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v_a_2842_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2833_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2833_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 0);
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
v___y_2737_ = v_a_2811_;
v___y_2738_ = v___y_2794_;
v___y_2739_ = v___y_2795_;
v___y_2740_ = v___y_2796_;
v___y_2741_ = v___y_2798_;
v___y_2742_ = v___x_2832_;
v___y_2743_ = v___y_2800_;
v___y_2744_ = v___y_2799_;
v___y_2745_ = v___y_2801_;
v___y_2746_ = v___y_2802_;
v___y_2747_ = v___y_2803_;
v___y_2748_ = v___y_2804_;
v___y_2749_ = v___y_2805_;
v___y_2750_ = v___y_2806_;
v___y_2751_ = v___y_2807_;
v___y_2752_ = v___y_2808_;
v___y_2753_ = v___y_2809_;
v_a_2754_ = v___x_2847_;
goto v___jp_2736_;
}
}
}
}
}
v___jp_2850_:
{
if (v_enums_2853_ == 0)
{
v___y_2688_ = v___y_2851_;
v_fixedInt_2689_ = v_fixedInt_2852_;
v___y_2690_ = v___y_2854_;
v___y_2691_ = v___y_2855_;
v___y_2692_ = v___y_2856_;
v___y_2693_ = v___y_2857_;
v___y_2694_ = v___y_2858_;
v___y_2695_ = v___y_2859_;
v___y_2696_ = v___y_2860_;
v___y_2697_ = v___y_2861_;
v___y_2698_ = v___y_2862_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2863_; lean_object* v_options_2864_; uint8_t v_hasTrace_2865_; 
v___x_2863_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_options_2864_ = lean_ctor_get(v___y_2861_, 2);
v_hasTrace_2865_ = lean_ctor_get_uint8(v_options_2864_, sizeof(void*)*1);
if (v_hasTrace_2865_ == 0)
{
lean_object* v_run_x27_2866_; lean_object* v___x_2867_; 
v_run_x27_2866_ = lean_ctor_get(v___x_2863_, 1);
lean_inc_ref(v_run_x27_2866_);
lean_inc(v___y_2862_);
lean_inc_ref(v___y_2861_);
lean_inc(v___y_2860_);
lean_inc_ref(v___y_2859_);
lean_inc(v___y_2858_);
lean_inc_ref(v___y_2857_);
lean_inc(v___y_2856_);
lean_inc_ref(v___y_2855_);
v___x_2867_ = lean_apply_9(v_run_x27_2866_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, lean_box(0));
v___y_2714_ = v___y_2862_;
v___y_2715_ = v___y_2859_;
v___y_2716_ = v___y_2855_;
v___y_2717_ = v___y_2856_;
v___y_2718_ = v___y_2861_;
v___y_2719_ = v___y_2858_;
v___y_2720_ = v___y_2857_;
v___y_2721_ = v___y_2851_;
v___y_2722_ = v___y_2860_;
v___y_2723_ = v___y_2854_;
v___y_2724_ = v___x_2867_;
goto v___jp_2713_;
}
else
{
lean_object* v_run_x27_2868_; lean_object* v_inheritedTraceOptions_2869_; lean_object* v___f_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v_run_x27_2868_ = lean_ctor_get(v___x_2863_, 1);
v_inheritedTraceOptions_2869_ = lean_ctor_get(v___y_2861_, 13);
v___f_2870_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5);
v___x_2871_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_2872_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_2873_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2869_, v_options_2864_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2874_ = l_Lean_trace_profiler;
v___x_2875_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2864_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; 
lean_inc_ref(v_run_x27_2868_);
lean_inc(v___y_2862_);
lean_inc_ref(v___y_2861_);
lean_inc(v___y_2860_);
lean_inc_ref(v___y_2859_);
lean_inc(v___y_2858_);
lean_inc_ref(v___y_2857_);
lean_inc(v___y_2856_);
lean_inc_ref(v___y_2855_);
v___x_2876_ = lean_apply_9(v_run_x27_2868_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, lean_box(0));
v___y_2714_ = v___y_2862_;
v___y_2715_ = v___y_2859_;
v___y_2716_ = v___y_2855_;
v___y_2717_ = v___y_2856_;
v___y_2718_ = v___y_2861_;
v___y_2719_ = v___y_2858_;
v___y_2720_ = v___y_2857_;
v___y_2721_ = v___y_2851_;
v___y_2722_ = v___y_2860_;
v___y_2723_ = v___y_2854_;
v___y_2724_ = v___x_2876_;
goto v___jp_2713_;
}
else
{
lean_inc_ref(v_run_x27_2868_);
v___y_2794_ = v___y_2855_;
v___y_2795_ = v___x_2873_;
v___y_2796_ = v___y_2861_;
v___y_2797_ = v_run_x27_2868_;
v___y_2798_ = v___y_2851_;
v___y_2799_ = v___y_2859_;
v___y_2800_ = v___y_2862_;
v___y_2801_ = v___x_2871_;
v___y_2802_ = v___y_2856_;
v___y_2803_ = v___f_2870_;
v___y_2804_ = v_hasTrace_2865_;
v___y_2805_ = v___y_2858_;
v___y_2806_ = v___y_2857_;
v___y_2807_ = v_options_2864_;
v___y_2808_ = v___y_2860_;
v___y_2809_ = v___y_2854_;
goto v___jp_2793_;
}
}
else
{
lean_inc_ref(v_run_x27_2868_);
v___y_2794_ = v___y_2855_;
v___y_2795_ = v___x_2873_;
v___y_2796_ = v___y_2861_;
v___y_2797_ = v_run_x27_2868_;
v___y_2798_ = v___y_2851_;
v___y_2799_ = v___y_2859_;
v___y_2800_ = v___y_2862_;
v___y_2801_ = v___x_2871_;
v___y_2802_ = v___y_2856_;
v___y_2803_ = v___f_2870_;
v___y_2804_ = v_hasTrace_2865_;
v___y_2805_ = v___y_2858_;
v___y_2806_ = v___y_2857_;
v___y_2807_ = v_options_2864_;
v___y_2808_ = v___y_2860_;
v___y_2809_ = v___y_2854_;
goto v___jp_2793_;
}
}
}
}
v___jp_2877_:
{
if (lean_obj_tag(v___y_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2900_; 
v_a_2889_ = lean_ctor_get(v___y_2888_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___y_2888_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2891_ = v___y_2888_;
v_isShared_2892_ = v_isSharedCheck_2900_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___y_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2900_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_unbox(v_a_2889_);
lean_dec(v_a_2889_);
if (v___x_2893_ == 0)
{
uint8_t v_fixedInt_2894_; uint8_t v_enums_2895_; 
lean_del_object(v___x_2891_);
v_fixedInt_2894_ = lean_ctor_get_uint8(v___y_2884_, sizeof(void*)*2 + 6);
v_enums_2895_ = lean_ctor_get_uint8(v___y_2884_, sizeof(void*)*2 + 7);
v___y_2851_ = v___y_2884_;
v_fixedInt_2852_ = v_fixedInt_2894_;
v_enums_2853_ = v_enums_2895_;
v___y_2854_ = v___y_2887_;
v___y_2855_ = v___y_2882_;
v___y_2856_ = v___y_2886_;
v___y_2857_ = v___y_2883_;
v___y_2858_ = v___y_2881_;
v___y_2859_ = v___y_2885_;
v___y_2860_ = v___y_2880_;
v___y_2861_ = v___y_2879_;
v___y_2862_ = v___y_2878_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2896_ = lean_box(v___y_2887_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2896_);
v___x_2898_ = v___x_2891_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
return v___y_2888_;
}
}
v___jp_2901_:
{
lean_object* v___x_2920_; double v___x_2921_; double v___x_2922_; double v___x_2923_; double v___x_2924_; double v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2920_ = lean_io_mono_nanos_now();
v___x_2921_ = lean_float_of_nat(v___y_2911_);
v___x_2922_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2923_ = lean_float_div(v___x_2921_, v___x_2922_);
v___x_2924_ = lean_float_of_nat(v___x_2920_);
v___x_2925_ = lean_float_div(v___x_2924_, v___x_2922_);
v___x_2926_ = lean_box_float(v___x_2923_);
v___x_2927_ = lean_box_float(v___x_2925_);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v_a_2919_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
lean_inc_ref(v___y_2912_);
lean_inc_ref(v___y_2906_);
v___x_2930_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_2904_, v___y_2906_, v___y_2908_, v___y_2902_, v___y_2914_, v___y_2912_, v___x_2929_, v___y_2915_, v___y_2909_, v___y_2916_, v___y_2905_, v___y_2917_, v___y_2913_, v___y_2903_, v___y_2910_);
v___y_2878_ = v___y_2910_;
v___y_2879_ = v___y_2903_;
v___y_2880_ = v___y_2913_;
v___y_2881_ = v___y_2905_;
v___y_2882_ = v___y_2915_;
v___y_2883_ = v___y_2916_;
v___y_2884_ = v___y_2907_;
v___y_2885_ = v___y_2917_;
v___y_2886_ = v___y_2909_;
v___y_2887_ = v___y_2918_;
v___y_2888_ = v___x_2930_;
goto v___jp_2877_;
}
v___jp_2931_:
{
lean_object* v___x_2950_; double v___x_2951_; double v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2950_ = lean_io_get_num_heartbeats();
v___x_2951_ = lean_float_of_nat(v___y_2937_);
v___x_2952_ = lean_float_of_nat(v___x_2950_);
v___x_2953_ = lean_box_float(v___x_2951_);
v___x_2954_ = lean_box_float(v___x_2952_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v_a_2949_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
lean_inc_ref(v___y_2942_);
lean_inc_ref(v___y_2936_);
v___x_2957_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_2934_, v___y_2936_, v___y_2939_, v___y_2932_, v___y_2944_, v___y_2942_, v___x_2956_, v___y_2945_, v___y_2940_, v___y_2946_, v___y_2935_, v___y_2947_, v___y_2943_, v___y_2933_, v___y_2941_);
v___y_2878_ = v___y_2941_;
v___y_2879_ = v___y_2933_;
v___y_2880_ = v___y_2943_;
v___y_2881_ = v___y_2935_;
v___y_2882_ = v___y_2945_;
v___y_2883_ = v___y_2946_;
v___y_2884_ = v___y_2938_;
v___y_2885_ = v___y_2947_;
v___y_2886_ = v___y_2940_;
v___y_2887_ = v___y_2948_;
v___y_2888_ = v___x_2957_;
goto v___jp_2877_;
}
v___jp_2958_:
{
lean_object* v___x_2975_; lean_object* v_a_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2975_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2968_);
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2978_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2966_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_io_mono_nanos_now();
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2973_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2971_);
v___x_2980_ = lean_apply_9(v___y_2963_, v___y_2971_, v___y_2967_, v___y_2972_, v___y_2962_, v___y_2973_, v___y_2970_, v___y_2960_, v___y_2968_, lean_box(0));
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2980_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 1);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
v___y_2902_ = v___y_2959_;
v___y_2903_ = v___y_2960_;
v___y_2904_ = v___y_2961_;
v___y_2905_ = v___y_2962_;
v___y_2906_ = v___y_2964_;
v___y_2907_ = v___y_2965_;
v___y_2908_ = v___y_2966_;
v___y_2909_ = v___y_2967_;
v___y_2910_ = v___y_2968_;
v___y_2911_ = v___x_2979_;
v___y_2912_ = v___y_2969_;
v___y_2913_ = v___y_2970_;
v___y_2914_ = v_a_2976_;
v___y_2915_ = v___y_2971_;
v___y_2916_ = v___y_2972_;
v___y_2917_ = v___y_2973_;
v___y_2918_ = v___y_2974_;
v_a_2919_ = v___x_2986_;
goto v___jp_2901_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_a_2989_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2980_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2980_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 0);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
v___y_2902_ = v___y_2959_;
v___y_2903_ = v___y_2960_;
v___y_2904_ = v___y_2961_;
v___y_2905_ = v___y_2962_;
v___y_2906_ = v___y_2964_;
v___y_2907_ = v___y_2965_;
v___y_2908_ = v___y_2966_;
v___y_2909_ = v___y_2967_;
v___y_2910_ = v___y_2968_;
v___y_2911_ = v___x_2979_;
v___y_2912_ = v___y_2969_;
v___y_2913_ = v___y_2970_;
v___y_2914_ = v_a_2976_;
v___y_2915_ = v___y_2971_;
v___y_2916_ = v___y_2972_;
v___y_2917_ = v___y_2973_;
v___y_2918_ = v___y_2974_;
v_a_2919_ = v___x_2994_;
goto v___jp_2901_;
}
}
}
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2973_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2972_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2971_);
v___x_2998_ = lean_apply_9(v___y_2963_, v___y_2971_, v___y_2967_, v___y_2972_, v___y_2962_, v___y_2973_, v___y_2970_, v___y_2960_, v___y_2968_, lean_box(0));
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 1);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
v___y_2932_ = v___y_2959_;
v___y_2933_ = v___y_2960_;
v___y_2934_ = v___y_2961_;
v___y_2935_ = v___y_2962_;
v___y_2936_ = v___y_2964_;
v___y_2937_ = v___x_2997_;
v___y_2938_ = v___y_2965_;
v___y_2939_ = v___y_2966_;
v___y_2940_ = v___y_2967_;
v___y_2941_ = v___y_2968_;
v___y_2942_ = v___y_2969_;
v___y_2943_ = v___y_2970_;
v___y_2944_ = v_a_2976_;
v___y_2945_ = v___y_2971_;
v___y_2946_ = v___y_2972_;
v___y_2947_ = v___y_2973_;
v___y_2948_ = v___y_2974_;
v_a_2949_ = v___x_3004_;
goto v___jp_2931_;
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
v_a_3007_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2998_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2998_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set_tag(v___x_3009_, 0);
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
v___y_2932_ = v___y_2959_;
v___y_2933_ = v___y_2960_;
v___y_2934_ = v___y_2961_;
v___y_2935_ = v___y_2962_;
v___y_2936_ = v___y_2964_;
v___y_2937_ = v___x_2997_;
v___y_2938_ = v___y_2965_;
v___y_2939_ = v___y_2966_;
v___y_2940_ = v___y_2967_;
v___y_2941_ = v___y_2968_;
v___y_2942_ = v___y_2969_;
v___y_2943_ = v___y_2970_;
v___y_2944_ = v_a_2976_;
v___y_2945_ = v___y_2971_;
v___y_2946_ = v___y_2972_;
v___y_2947_ = v___y_2973_;
v___y_2948_ = v___y_2974_;
v_a_2949_ = v___x_3012_;
goto v___jp_2931_;
}
}
}
}
}
v___jp_3015_:
{
if (lean_obj_tag(v___y_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3053_; 
v_a_3027_ = lean_ctor_get(v___y_3026_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___y_3026_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3029_ = v___y_3026_;
v_isShared_3030_ = v_isSharedCheck_3053_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___y_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3053_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_unbox(v_a_3027_);
lean_dec(v_a_3027_);
if (v___x_3031_ == 0)
{
uint8_t v_structures_3032_; 
lean_del_object(v___x_3029_);
v_structures_3032_ = lean_ctor_get_uint8(v___y_3022_, sizeof(void*)*2 + 5);
if (v_structures_3032_ == 0)
{
uint8_t v_fixedInt_3033_; uint8_t v_enums_3034_; 
v_fixedInt_3033_ = lean_ctor_get_uint8(v___y_3022_, sizeof(void*)*2 + 6);
v_enums_3034_ = lean_ctor_get_uint8(v___y_3022_, sizeof(void*)*2 + 7);
v___y_2851_ = v___y_3022_;
v_fixedInt_2852_ = v_fixedInt_3033_;
v_enums_2853_ = v_enums_3034_;
v___y_2854_ = v___y_3025_;
v___y_2855_ = v___y_3020_;
v___y_2856_ = v___y_3024_;
v___y_2857_ = v___y_3021_;
v___y_2858_ = v___y_3019_;
v___y_2859_ = v___y_3023_;
v___y_2860_ = v___y_3018_;
v___y_2861_ = v___y_3017_;
v___y_2862_ = v___y_3016_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_3035_; lean_object* v_options_3036_; uint8_t v_hasTrace_3037_; 
v___x_3035_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_options_3036_ = lean_ctor_get(v___y_3017_, 2);
v_hasTrace_3037_ = lean_ctor_get_uint8(v_options_3036_, sizeof(void*)*1);
if (v_hasTrace_3037_ == 0)
{
lean_object* v_run_x27_3038_; lean_object* v___x_3039_; 
v_run_x27_3038_ = lean_ctor_get(v___x_3035_, 1);
lean_inc_ref(v_run_x27_3038_);
lean_inc(v___y_3016_);
lean_inc_ref(v___y_3017_);
lean_inc(v___y_3018_);
lean_inc_ref(v___y_3023_);
lean_inc(v___y_3019_);
lean_inc_ref(v___y_3021_);
lean_inc(v___y_3024_);
lean_inc_ref(v___y_3020_);
v___x_3039_ = lean_apply_9(v_run_x27_3038_, v___y_3020_, v___y_3024_, v___y_3021_, v___y_3019_, v___y_3023_, v___y_3018_, v___y_3017_, v___y_3016_, lean_box(0));
v___y_2878_ = v___y_3016_;
v___y_2879_ = v___y_3017_;
v___y_2880_ = v___y_3018_;
v___y_2881_ = v___y_3019_;
v___y_2882_ = v___y_3020_;
v___y_2883_ = v___y_3021_;
v___y_2884_ = v___y_3022_;
v___y_2885_ = v___y_3023_;
v___y_2886_ = v___y_3024_;
v___y_2887_ = v___y_3025_;
v___y_2888_ = v___x_3039_;
goto v___jp_2877_;
}
else
{
lean_object* v_run_x27_3040_; lean_object* v_inheritedTraceOptions_3041_; lean_object* v___f_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v_run_x27_3040_ = lean_ctor_get(v___x_3035_, 1);
v_inheritedTraceOptions_3041_ = lean_ctor_get(v___y_3017_, 13);
v___f_3042_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6);
v___x_3043_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3044_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3045_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3041_, v_options_3036_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = l_Lean_trace_profiler;
v___x_3047_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_3036_, v___x_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; 
lean_inc_ref(v_run_x27_3040_);
lean_inc(v___y_3016_);
lean_inc_ref(v___y_3017_);
lean_inc(v___y_3018_);
lean_inc_ref(v___y_3023_);
lean_inc(v___y_3019_);
lean_inc_ref(v___y_3021_);
lean_inc(v___y_3024_);
lean_inc_ref(v___y_3020_);
v___x_3048_ = lean_apply_9(v_run_x27_3040_, v___y_3020_, v___y_3024_, v___y_3021_, v___y_3019_, v___y_3023_, v___y_3018_, v___y_3017_, v___y_3016_, lean_box(0));
v___y_2878_ = v___y_3016_;
v___y_2879_ = v___y_3017_;
v___y_2880_ = v___y_3018_;
v___y_2881_ = v___y_3019_;
v___y_2882_ = v___y_3020_;
v___y_2883_ = v___y_3021_;
v___y_2884_ = v___y_3022_;
v___y_2885_ = v___y_3023_;
v___y_2886_ = v___y_3024_;
v___y_2887_ = v___y_3025_;
v___y_2888_ = v___x_3048_;
goto v___jp_2877_;
}
else
{
lean_inc_ref(v_run_x27_3040_);
v___y_2959_ = v___x_3045_;
v___y_2960_ = v___y_3017_;
v___y_2961_ = v_hasTrace_3037_;
v___y_2962_ = v___y_3019_;
v___y_2963_ = v_run_x27_3040_;
v___y_2964_ = v___x_3043_;
v___y_2965_ = v___y_3022_;
v___y_2966_ = v_options_3036_;
v___y_2967_ = v___y_3024_;
v___y_2968_ = v___y_3016_;
v___y_2969_ = v___f_3042_;
v___y_2970_ = v___y_3018_;
v___y_2971_ = v___y_3020_;
v___y_2972_ = v___y_3021_;
v___y_2973_ = v___y_3023_;
v___y_2974_ = v___y_3025_;
goto v___jp_2958_;
}
}
else
{
lean_inc_ref(v_run_x27_3040_);
v___y_2959_ = v___x_3045_;
v___y_2960_ = v___y_3017_;
v___y_2961_ = v_hasTrace_3037_;
v___y_2962_ = v___y_3019_;
v___y_2963_ = v_run_x27_3040_;
v___y_2964_ = v___x_3043_;
v___y_2965_ = v___y_3022_;
v___y_2966_ = v_options_3036_;
v___y_2967_ = v___y_3024_;
v___y_2968_ = v___y_3016_;
v___y_2969_ = v___f_3042_;
v___y_2970_ = v___y_3018_;
v___y_2971_ = v___y_3020_;
v___y_2972_ = v___y_3021_;
v___y_2973_ = v___y_3023_;
v___y_2974_ = v___y_3025_;
goto v___jp_2958_;
}
}
}
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = lean_box(v___y_3025_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3049_);
v___x_3051_ = v___x_3029_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
return v___y_3026_;
}
}
v___jp_3054_:
{
lean_object* v___x_3073_; double v___x_3074_; double v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3073_ = lean_io_get_num_heartbeats();
v___x_3074_ = lean_float_of_nat(v___y_3055_);
v___x_3075_ = lean_float_of_nat(v___x_3073_);
v___x_3076_ = lean_box_float(v___x_3074_);
v___x_3077_ = lean_box_float(v___x_3075_);
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v_a_3072_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
lean_inc_ref(v___y_3063_);
lean_inc_ref(v___y_3057_);
v___x_3080_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_3066_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3061_, v___y_3063_, v___x_3079_, v___y_3068_, v___y_3064_, v___y_3069_, v___y_3060_, v___y_3070_, v___y_3067_, v___y_3056_, v___y_3065_);
v___y_3016_ = v___y_3065_;
v___y_3017_ = v___y_3056_;
v___y_3018_ = v___y_3067_;
v___y_3019_ = v___y_3060_;
v___y_3020_ = v___y_3068_;
v___y_3021_ = v___y_3069_;
v___y_3022_ = v___y_3062_;
v___y_3023_ = v___y_3070_;
v___y_3024_ = v___y_3064_;
v___y_3025_ = v___y_3071_;
v___y_3026_ = v___x_3080_;
goto v___jp_3015_;
}
v___jp_3081_:
{
lean_object* v___x_3100_; double v___x_3101_; double v___x_3102_; double v___x_3103_; double v___x_3104_; double v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3100_ = lean_io_mono_nanos_now();
v___x_3101_ = lean_float_of_nat(v___y_3083_);
v___x_3102_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3103_ = lean_float_div(v___x_3101_, v___x_3102_);
v___x_3104_ = lean_float_of_nat(v___x_3100_);
v___x_3105_ = lean_float_div(v___x_3104_, v___x_3102_);
v___x_3106_ = lean_box_float(v___x_3103_);
v___x_3107_ = lean_box_float(v___x_3105_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v_a_3099_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
lean_inc_ref(v___y_3090_);
lean_inc_ref(v___y_3084_);
v___x_3110_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_3093_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3088_, v___y_3090_, v___x_3109_, v___y_3095_, v___y_3091_, v___y_3096_, v___y_3087_, v___y_3097_, v___y_3094_, v___y_3082_, v___y_3092_);
v___y_3016_ = v___y_3092_;
v___y_3017_ = v___y_3082_;
v___y_3018_ = v___y_3094_;
v___y_3019_ = v___y_3087_;
v___y_3020_ = v___y_3095_;
v___y_3021_ = v___y_3096_;
v___y_3022_ = v___y_3089_;
v___y_3023_ = v___y_3097_;
v___y_3024_ = v___y_3091_;
v___y_3025_ = v___y_3098_;
v___y_3026_ = v___x_3110_;
goto v___jp_3015_;
}
v___jp_3111_:
{
lean_object* v___x_3128_; lean_object* v_a_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3128_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_3120_);
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref(v___x_3128_);
v___x_3130_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3131_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3113_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_io_mono_nanos_now();
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3112_);
lean_inc(v___y_3122_);
lean_inc_ref(v___y_3126_);
lean_inc(v___y_3116_);
lean_inc_ref(v___y_3125_);
lean_inc(v___y_3119_);
lean_inc_ref(v___y_3124_);
v___x_3133_ = lean_apply_9(v___y_3123_, v___y_3124_, v___y_3119_, v___y_3125_, v___y_3116_, v___y_3126_, v___y_3122_, v___y_3112_, v___y_3120_, lean_box(0));
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
lean_ctor_set_tag(v___x_3136_, 1);
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
v___y_3082_ = v___y_3112_;
v___y_3083_ = v___x_3132_;
v___y_3084_ = v___y_3114_;
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3115_;
v___y_3087_ = v___y_3116_;
v___y_3088_ = v_a_3129_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3120_;
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v___y_3124_;
v___y_3096_ = v___y_3125_;
v___y_3097_ = v___y_3126_;
v___y_3098_ = v___y_3127_;
v_a_3099_ = v___x_3139_;
goto v___jp_3081_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
v_a_3142_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3133_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3133_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
lean_ctor_set_tag(v___x_3144_, 0);
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
v___y_3082_ = v___y_3112_;
v___y_3083_ = v___x_3132_;
v___y_3084_ = v___y_3114_;
v___y_3085_ = v___y_3113_;
v___y_3086_ = v___y_3115_;
v___y_3087_ = v___y_3116_;
v___y_3088_ = v_a_3129_;
v___y_3089_ = v___y_3117_;
v___y_3090_ = v___y_3118_;
v___y_3091_ = v___y_3119_;
v___y_3092_ = v___y_3120_;
v___y_3093_ = v___y_3121_;
v___y_3094_ = v___y_3122_;
v___y_3095_ = v___y_3124_;
v___y_3096_ = v___y_3125_;
v___y_3097_ = v___y_3126_;
v___y_3098_ = v___y_3127_;
v_a_3099_ = v___x_3147_;
goto v___jp_3081_;
}
}
}
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3112_);
lean_inc(v___y_3122_);
lean_inc_ref(v___y_3126_);
lean_inc(v___y_3116_);
lean_inc_ref(v___y_3125_);
lean_inc(v___y_3119_);
lean_inc_ref(v___y_3124_);
v___x_3151_ = lean_apply_9(v___y_3123_, v___y_3124_, v___y_3119_, v___y_3125_, v___y_3116_, v___y_3126_, v___y_3122_, v___y_3112_, v___y_3120_, lean_box(0));
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 1);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
v___y_3055_ = v___x_3150_;
v___y_3056_ = v___y_3112_;
v___y_3057_ = v___y_3114_;
v___y_3058_ = v___y_3113_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3116_;
v___y_3061_ = v_a_3129_;
v___y_3062_ = v___y_3117_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3119_;
v___y_3065_ = v___y_3120_;
v___y_3066_ = v___y_3121_;
v___y_3067_ = v___y_3122_;
v___y_3068_ = v___y_3124_;
v___y_3069_ = v___y_3125_;
v___y_3070_ = v___y_3126_;
v___y_3071_ = v___y_3127_;
v_a_3072_ = v___x_3157_;
goto v___jp_3054_;
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3160_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3151_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3151_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 0);
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
v___y_3055_ = v___x_3150_;
v___y_3056_ = v___y_3112_;
v___y_3057_ = v___y_3114_;
v___y_3058_ = v___y_3113_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3116_;
v___y_3061_ = v_a_3129_;
v___y_3062_ = v___y_3117_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3119_;
v___y_3065_ = v___y_3120_;
v___y_3066_ = v___y_3121_;
v___y_3067_ = v___y_3122_;
v___y_3068_ = v___y_3124_;
v___y_3069_ = v___y_3125_;
v___y_3070_ = v___y_3126_;
v___y_3071_ = v___y_3127_;
v_a_3072_ = v___x_3165_;
goto v___jp_3054_;
}
}
}
}
}
v___jp_3168_:
{
lean_object* v___x_3179_; lean_object* v_options_3180_; uint8_t v_hasTrace_3181_; 
v___x_3179_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v_options_3180_ = lean_ctor_get(v___y_3177_, 2);
v_hasTrace_3181_ = lean_ctor_get_uint8(v_options_3180_, sizeof(void*)*1);
if (v_hasTrace_3181_ == 0)
{
lean_object* v_run_x27_3182_; lean_object* v___x_3183_; 
v_run_x27_3182_ = lean_ctor_get(v___x_3179_, 1);
lean_inc_ref(v_run_x27_3182_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
lean_inc(v___y_3172_);
lean_inc_ref(v___y_3171_);
v___x_3183_ = lean_apply_9(v_run_x27_3182_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, lean_box(0));
v___y_3016_ = v___y_3178_;
v___y_3017_ = v___y_3177_;
v___y_3018_ = v___y_3176_;
v___y_3019_ = v___y_3174_;
v___y_3020_ = v___y_3171_;
v___y_3021_ = v___y_3173_;
v___y_3022_ = v___y_3169_;
v___y_3023_ = v___y_3175_;
v___y_3024_ = v___y_3172_;
v___y_3025_ = v___y_3170_;
v___y_3026_ = v___x_3183_;
goto v___jp_3015_;
}
else
{
lean_object* v_run_x27_3184_; lean_object* v_inheritedTraceOptions_3185_; lean_object* v___f_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v_run_x27_3184_ = lean_ctor_get(v___x_3179_, 1);
v_inheritedTraceOptions_3185_ = lean_ctor_get(v___y_3177_, 13);
v___f_3186_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7);
v___x_3187_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3188_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3185_, v_options_3180_, v___x_3188_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = l_Lean_trace_profiler;
v___x_3191_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_3180_, v___x_3190_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; 
lean_inc_ref(v_run_x27_3184_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
lean_inc(v___y_3172_);
lean_inc_ref(v___y_3171_);
v___x_3192_ = lean_apply_9(v_run_x27_3184_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, lean_box(0));
v___y_3016_ = v___y_3178_;
v___y_3017_ = v___y_3177_;
v___y_3018_ = v___y_3176_;
v___y_3019_ = v___y_3174_;
v___y_3020_ = v___y_3171_;
v___y_3021_ = v___y_3173_;
v___y_3022_ = v___y_3169_;
v___y_3023_ = v___y_3175_;
v___y_3024_ = v___y_3172_;
v___y_3025_ = v___y_3170_;
v___y_3026_ = v___x_3192_;
goto v___jp_3015_;
}
else
{
lean_inc_ref(v_run_x27_3184_);
v___y_3112_ = v___y_3177_;
v___y_3113_ = v_options_3180_;
v___y_3114_ = v___x_3187_;
v___y_3115_ = v___x_3189_;
v___y_3116_ = v___y_3174_;
v___y_3117_ = v___y_3169_;
v___y_3118_ = v___f_3186_;
v___y_3119_ = v___y_3172_;
v___y_3120_ = v___y_3178_;
v___y_3121_ = v_hasTrace_3181_;
v___y_3122_ = v___y_3176_;
v___y_3123_ = v_run_x27_3184_;
v___y_3124_ = v___y_3171_;
v___y_3125_ = v___y_3173_;
v___y_3126_ = v___y_3175_;
v___y_3127_ = v___y_3170_;
goto v___jp_3111_;
}
}
else
{
lean_inc_ref(v_run_x27_3184_);
v___y_3112_ = v___y_3177_;
v___y_3113_ = v_options_3180_;
v___y_3114_ = v___x_3187_;
v___y_3115_ = v___x_3189_;
v___y_3116_ = v___y_3174_;
v___y_3117_ = v___y_3169_;
v___y_3118_ = v___f_3186_;
v___y_3119_ = v___y_3172_;
v___y_3120_ = v___y_3178_;
v___y_3121_ = v_hasTrace_3181_;
v___y_3122_ = v___y_3176_;
v___y_3123_ = v_run_x27_3184_;
v___y_3124_ = v___y_3171_;
v___y_3125_ = v___y_3173_;
v___y_3126_ = v___y_3175_;
v___y_3127_ = v___y_3170_;
goto v___jp_3111_;
}
}
}
v___jp_3193_:
{
if (lean_obj_tag(v___y_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3213_; 
v_a_3204_ = lean_ctor_get(v___y_3203_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___y_3203_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3206_ = v___y_3203_;
v_isShared_3207_ = v_isSharedCheck_3213_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___y_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3213_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
uint8_t v___x_3208_; 
v___x_3208_ = lean_unbox(v_a_3204_);
lean_dec(v_a_3204_);
if (v___x_3208_ == 0)
{
lean_del_object(v___x_3206_);
v___y_3169_ = v___y_3201_;
v___y_3170_ = v___y_3202_;
v___y_3171_ = v___y_3201_;
v___y_3172_ = v___y_3197_;
v___y_3173_ = v___y_3195_;
v___y_3174_ = v___y_3198_;
v___y_3175_ = v___y_3199_;
v___y_3176_ = v___y_3196_;
v___y_3177_ = v___y_3194_;
v___y_3178_ = v___y_3200_;
goto v___jp_3168_;
}
else
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3209_ = lean_box(v___y_3202_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3209_);
v___x_3211_ = v___x_3206_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
return v___y_3203_;
}
}
v___jp_3214_:
{
lean_object* v___x_3232_; double v___x_3233_; double v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3232_ = lean_io_get_num_heartbeats();
v___x_3233_ = lean_float_of_nat(v___y_3228_);
v___x_3234_ = lean_float_of_nat(v___x_3232_);
v___x_3235_ = lean_box_float(v___x_3233_);
v___x_3236_ = lean_box_float(v___x_3234_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3235_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_a_3231_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
lean_inc_ref(v___y_3223_);
lean_inc_ref(v___y_3230_);
v___x_3239_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_3219_, v___y_3230_, v___y_3215_, v___y_3216_, v___y_3222_, v___y_3223_, v___x_3238_, v___y_3221_, v___y_3218_, v___y_3224_, v___y_3226_, v___y_3220_, v___y_3225_, v___y_3217_, v___y_3227_);
v___y_3194_ = v___y_3217_;
v___y_3195_ = v___y_3224_;
v___y_3196_ = v___y_3225_;
v___y_3197_ = v___y_3218_;
v___y_3198_ = v___y_3226_;
v___y_3199_ = v___y_3220_;
v___y_3200_ = v___y_3227_;
v___y_3201_ = v___y_3221_;
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___x_3239_;
goto v___jp_3193_;
}
v___jp_3240_:
{
lean_object* v___x_3258_; double v___x_3259_; double v___x_3260_; double v___x_3261_; double v___x_3262_; double v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3258_ = lean_io_mono_nanos_now();
v___x_3259_ = lean_float_of_nat(v___y_3247_);
v___x_3260_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3261_ = lean_float_div(v___x_3259_, v___x_3260_);
v___x_3262_ = lean_float_of_nat(v___x_3258_);
v___x_3263_ = lean_float_div(v___x_3262_, v___x_3260_);
v___x_3264_ = lean_box_float(v___x_3261_);
v___x_3265_ = lean_box_float(v___x_3263_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v_a_3257_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
lean_inc_ref(v___y_3250_);
lean_inc_ref(v___y_3256_);
v___x_3268_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2392_, v___y_3245_, v___y_3256_, v___y_3241_, v___y_3242_, v___y_3249_, v___y_3250_, v___x_3267_, v___y_3248_, v___y_3244_, v___y_3251_, v___y_3253_, v___y_3246_, v___y_3252_, v___y_3243_, v___y_3254_);
v___y_3194_ = v___y_3243_;
v___y_3195_ = v___y_3251_;
v___y_3196_ = v___y_3252_;
v___y_3197_ = v___y_3244_;
v___y_3198_ = v___y_3253_;
v___y_3199_ = v___y_3246_;
v___y_3200_ = v___y_3254_;
v___y_3201_ = v___y_3248_;
v___y_3202_ = v___y_3255_;
v___y_3203_ = v___x_3268_;
goto v___jp_3193_;
}
v___jp_3269_:
{
lean_object* v___x_3285_; lean_object* v_a_3286_; lean_object* v___x_3287_; uint8_t v___x_3288_; 
v___x_3285_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_3282_);
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3288_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3270_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_io_mono_nanos_now();
lean_inc(v___y_3282_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3280_);
lean_inc_ref(v___y_3275_);
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3279_);
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3277_);
v___x_3290_ = lean_apply_9(v___y_3273_, v___y_3277_, v___y_3274_, v___y_3279_, v___y_3281_, v___y_3275_, v___y_3280_, v___y_3272_, v___y_3282_, lean_box(0));
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 1);
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
v___y_3241_ = v___y_3270_;
v___y_3242_ = v___y_3271_;
v___y_3243_ = v___y_3272_;
v___y_3244_ = v___y_3274_;
v___y_3245_ = v___y_3276_;
v___y_3246_ = v___y_3275_;
v___y_3247_ = v___x_3289_;
v___y_3248_ = v___y_3277_;
v___y_3249_ = v_a_3286_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___y_3281_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3284_;
v___y_3256_ = v___y_3283_;
v_a_3257_ = v___x_3296_;
goto v___jp_3240_;
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
v_a_3299_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3290_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3290_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set_tag(v___x_3301_, 0);
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
v___y_3241_ = v___y_3270_;
v___y_3242_ = v___y_3271_;
v___y_3243_ = v___y_3272_;
v___y_3244_ = v___y_3274_;
v___y_3245_ = v___y_3276_;
v___y_3246_ = v___y_3275_;
v___y_3247_ = v___x_3289_;
v___y_3248_ = v___y_3277_;
v___y_3249_ = v_a_3286_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___y_3281_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3284_;
v___y_3256_ = v___y_3283_;
v_a_3257_ = v___x_3304_;
goto v___jp_3240_;
}
}
}
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3282_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3280_);
lean_inc_ref(v___y_3275_);
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3279_);
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3277_);
v___x_3308_ = lean_apply_9(v___y_3273_, v___y_3277_, v___y_3274_, v___y_3279_, v___y_3281_, v___y_3275_, v___y_3280_, v___y_3272_, v___y_3282_, lean_box(0));
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set_tag(v___x_3311_, 1);
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
v___y_3215_ = v___y_3270_;
v___y_3216_ = v___y_3271_;
v___y_3217_ = v___y_3272_;
v___y_3218_ = v___y_3274_;
v___y_3219_ = v___y_3276_;
v___y_3220_ = v___y_3275_;
v___y_3221_ = v___y_3277_;
v___y_3222_ = v_a_3286_;
v___y_3223_ = v___y_3278_;
v___y_3224_ = v___y_3279_;
v___y_3225_ = v___y_3280_;
v___y_3226_ = v___y_3281_;
v___y_3227_ = v___y_3282_;
v___y_3228_ = v___x_3307_;
v___y_3229_ = v___y_3284_;
v___y_3230_ = v___y_3283_;
v_a_3231_ = v___x_3314_;
goto v___jp_3214_;
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_a_3317_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3308_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3308_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
lean_ctor_set_tag(v___x_3319_, 0);
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
v___y_3215_ = v___y_3270_;
v___y_3216_ = v___y_3271_;
v___y_3217_ = v___y_3272_;
v___y_3218_ = v___y_3274_;
v___y_3219_ = v___y_3276_;
v___y_3220_ = v___y_3275_;
v___y_3221_ = v___y_3277_;
v___y_3222_ = v_a_3286_;
v___y_3223_ = v___y_3278_;
v___y_3224_ = v___y_3279_;
v___y_3225_ = v___y_3280_;
v___y_3226_ = v___y_3281_;
v___y_3227_ = v___y_3282_;
v___y_3228_ = v___x_3307_;
v___y_3229_ = v___y_3284_;
v___y_3230_ = v___y_3283_;
v_a_3231_ = v___x_3322_;
goto v___jp_3214_;
}
}
}
}
}
v___jp_3325_:
{
lean_object* v___x_3335_; lean_object* v_options_3336_; uint8_t v_hasTrace_3337_; 
v___x_3335_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_options_3336_ = lean_ctor_get(v___y_3327_, 2);
v_hasTrace_3337_ = lean_ctor_get_uint8(v_options_3336_, sizeof(void*)*1);
if (v_hasTrace_3337_ == 0)
{
lean_object* v_run_x27_3338_; lean_object* v___x_3339_; 
v_run_x27_3338_ = lean_ctor_get(v___x_3335_, 1);
lean_inc_ref(v_run_x27_3338_);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3327_);
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3331_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3326_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3333_);
v___x_3339_ = lean_apply_9(v_run_x27_3338_, v___y_3333_, v___y_3329_, v___y_3326_, v___y_3330_, v___y_3331_, v___y_3328_, v___y_3327_, v___y_3332_, lean_box(0));
v___y_3194_ = v___y_3327_;
v___y_3195_ = v___y_3326_;
v___y_3196_ = v___y_3328_;
v___y_3197_ = v___y_3329_;
v___y_3198_ = v___y_3330_;
v___y_3199_ = v___y_3331_;
v___y_3200_ = v___y_3332_;
v___y_3201_ = v___y_3333_;
v___y_3202_ = v___y_3334_;
v___y_3203_ = v___x_3339_;
goto v___jp_3193_;
}
else
{
lean_object* v_run_x27_3340_; lean_object* v_inheritedTraceOptions_3341_; lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_run_x27_3340_ = lean_ctor_get(v___x_3335_, 1);
v_inheritedTraceOptions_3341_ = lean_ctor_get(v___y_3327_, 13);
v___f_3342_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8);
v___x_3343_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3344_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3345_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3341_, v_options_3336_, v___x_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3346_ = l_Lean_trace_profiler;
v___x_3347_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_3336_, v___x_3346_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; 
lean_inc_ref(v_run_x27_3340_);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3327_);
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3331_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3326_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3333_);
v___x_3348_ = lean_apply_9(v_run_x27_3340_, v___y_3333_, v___y_3329_, v___y_3326_, v___y_3330_, v___y_3331_, v___y_3328_, v___y_3327_, v___y_3332_, lean_box(0));
v___y_3194_ = v___y_3327_;
v___y_3195_ = v___y_3326_;
v___y_3196_ = v___y_3328_;
v___y_3197_ = v___y_3329_;
v___y_3198_ = v___y_3330_;
v___y_3199_ = v___y_3331_;
v___y_3200_ = v___y_3332_;
v___y_3201_ = v___y_3333_;
v___y_3202_ = v___y_3334_;
v___y_3203_ = v___x_3348_;
goto v___jp_3193_;
}
else
{
lean_inc_ref(v_run_x27_3340_);
v___y_3270_ = v_options_3336_;
v___y_3271_ = v___x_3345_;
v___y_3272_ = v___y_3327_;
v___y_3273_ = v_run_x27_3340_;
v___y_3274_ = v___y_3329_;
v___y_3275_ = v___y_3331_;
v___y_3276_ = v_hasTrace_3337_;
v___y_3277_ = v___y_3333_;
v___y_3278_ = v___f_3342_;
v___y_3279_ = v___y_3326_;
v___y_3280_ = v___y_3328_;
v___y_3281_ = v___y_3330_;
v___y_3282_ = v___y_3332_;
v___y_3283_ = v___x_3343_;
v___y_3284_ = v___y_3334_;
goto v___jp_3269_;
}
}
else
{
lean_inc_ref(v_run_x27_3340_);
v___y_3270_ = v_options_3336_;
v___y_3271_ = v___x_3345_;
v___y_3272_ = v___y_3327_;
v___y_3273_ = v_run_x27_3340_;
v___y_3274_ = v___y_3329_;
v___y_3275_ = v___y_3331_;
v___y_3276_ = v_hasTrace_3337_;
v___y_3277_ = v___y_3333_;
v___y_3278_ = v___f_3342_;
v___y_3279_ = v___y_3326_;
v___y_3280_ = v___y_3328_;
v___y_3281_ = v___y_3330_;
v___y_3282_ = v___y_3332_;
v___y_3283_ = v___x_3343_;
v___y_3284_ = v___y_3334_;
goto v___jp_3269_;
}
}
}
v___jp_3349_:
{
uint8_t v_structures_3359_; 
v_structures_3359_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*2 + 5);
if (v_structures_3359_ == 0)
{
uint8_t v_enums_3360_; 
v_enums_3360_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*2 + 7);
if (v_enums_3360_ == 0)
{
v___y_3169_ = v___y_3351_;
v___y_3170_ = v___y_3350_;
v___y_3171_ = v___y_3351_;
v___y_3172_ = v___y_3352_;
v___y_3173_ = v___y_3353_;
v___y_3174_ = v___y_3354_;
v___y_3175_ = v___y_3355_;
v___y_3176_ = v___y_3356_;
v___y_3177_ = v___y_3357_;
v___y_3178_ = v___y_3358_;
goto v___jp_3168_;
}
else
{
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3357_;
v___y_3328_ = v___y_3356_;
v___y_3329_ = v___y_3352_;
v___y_3330_ = v___y_3354_;
v___y_3331_ = v___y_3355_;
v___y_3332_ = v___y_3358_;
v___y_3333_ = v___y_3351_;
v___y_3334_ = v___y_3350_;
goto v___jp_3325_;
}
}
else
{
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3357_;
v___y_3328_ = v___y_3356_;
v___y_3329_ = v___y_3352_;
v___y_3330_ = v___y_3354_;
v___y_3331_ = v___y_3355_;
v___y_3332_ = v___y_3358_;
v___y_3333_ = v___y_3351_;
v___y_3334_ = v___y_3350_;
goto v___jp_3325_;
}
}
v___jp_3361_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = lean_st_ref_set(v___y_3368_, v_snd_3372_);
v___x_3374_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(v___y_3362_, v___y_3368_, v___y_3367_, v___y_3365_, v___y_3366_, v___y_3363_, v___y_3364_, v___y_3370_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_options_3375_; uint8_t v_hasTrace_3376_; 
lean_dec_ref_known(v___x_3374_, 1);
v_options_3375_ = lean_ctor_get(v___y_3364_, 2);
v_hasTrace_3376_ = lean_ctor_get_uint8(v_options_3375_, sizeof(void*)*1);
if (v_hasTrace_3376_ == 0)
{
lean_dec(v___y_3369_);
v___y_3350_ = v___y_3371_;
v___y_3351_ = v___y_3362_;
v___y_3352_ = v___y_3368_;
v___y_3353_ = v___y_3367_;
v___y_3354_ = v___y_3365_;
v___y_3355_ = v___y_3366_;
v___y_3356_ = v___y_3363_;
v___y_3357_ = v___y_3364_;
v___y_3358_ = v___y_3370_;
goto v___jp_3349_;
}
else
{
lean_object* v_inheritedTraceOptions_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v_inheritedTraceOptions_3377_ = lean_ctor_get(v___y_3364_, 13);
v___x_3378_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3379_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3377_, v_options_3375_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_dec(v___y_3369_);
v___y_3350_ = v___y_3371_;
v___y_3351_ = v___y_3362_;
v___y_3352_ = v___y_3368_;
v___y_3353_ = v___y_3367_;
v___y_3354_ = v___y_3365_;
v___y_3355_ = v___y_3366_;
v___y_3356_ = v___y_3363_;
v___y_3357_ = v___y_3364_;
v___y_3358_ = v___y_3370_;
goto v___jp_3349_;
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3380_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6);
v___x_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___y_3369_);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_2392_, v___x_3382_, v___y_3366_, v___y_3363_, v___y_3364_, v___y_3370_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_dec_ref_known(v___x_3383_, 1);
v___y_3350_ = v___y_3371_;
v___y_3351_ = v___y_3362_;
v___y_3352_ = v___y_3368_;
v___y_3353_ = v___y_3367_;
v___y_3354_ = v___y_3365_;
v___y_3355_ = v___y_3366_;
v___y_3356_ = v___y_3363_;
v___y_3357_ = v___y_3364_;
v___y_3358_ = v___y_3370_;
goto v___jp_3349_;
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v___y_3369_);
v_a_3392_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3374_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3374_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
v___jp_3400_:
{
lean_object* v___x_3417_; 
lean_inc(v___y_3414_);
v___x_3417_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3417_, 0, v___y_3410_);
lean_ctor_set(v___x_3417_, 1, v___y_3405_);
lean_ctor_set(v___x_3417_, 2, v___y_3408_);
lean_ctor_set(v___x_3417_, 3, v___y_3404_);
lean_ctor_set(v___x_3417_, 4, v___y_3414_);
lean_ctor_set(v___x_3417_, 5, v___y_3409_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*6, v___y_3416_);
v___y_3362_ = v___y_3401_;
v___y_3363_ = v___y_3402_;
v___y_3364_ = v___y_3403_;
v___y_3365_ = v___y_3411_;
v___y_3366_ = v___y_3406_;
v___y_3367_ = v___y_3413_;
v___y_3368_ = v___y_3412_;
v___y_3369_ = v___y_3414_;
v___y_3370_ = v___y_3407_;
v___y_3371_ = v___y_3415_;
v_snd_3372_ = v___x_3417_;
goto v___jp_3361_;
}
v___jp_3418_:
{
uint8_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = 1;
v___x_3429_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__7));
v___x_3430_ = l_Lean_MVarId_falseOrByContra(v_g_3419_, v___x_3429_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3472_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3472_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3472_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
if (lean_obj_tag(v_a_3431_) == 1)
{
lean_object* v_val_3435_; lean_object* v___x_3436_; 
lean_del_object(v___x_3433_);
v_val_3435_ = lean_ctor_get(v_a_3431_, 0);
lean_inc(v_val_3435_);
lean_dec_ref_known(v_a_3431_, 1);
v___x_3436_ = l_Lean_Meta_Sym_preprocessMVar(v_val_3435_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; uint8_t v_didChange_3439_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
v___x_3438_ = lean_st_ref_take(v___y_3421_);
v_didChange_3439_ = lean_ctor_get_uint8(v___x_3438_, sizeof(void*)*6);
if (v_didChange_3439_ == 0)
{
lean_object* v_rewriteSimpCache_3440_; lean_object* v_rewriteDSimpCache_3441_; lean_object* v_acCache_3442_; lean_object* v_typeAnalysis_3443_; lean_object* v_goal_3444_; lean_object* v_hypotheses_3445_; uint8_t v___x_3446_; 
v_rewriteSimpCache_3440_ = lean_ctor_get(v___x_3438_, 0);
lean_inc_ref(v_rewriteSimpCache_3440_);
v_rewriteDSimpCache_3441_ = lean_ctor_get(v___x_3438_, 1);
lean_inc_ref(v_rewriteDSimpCache_3441_);
v_acCache_3442_ = lean_ctor_get(v___x_3438_, 2);
lean_inc_ref(v_acCache_3442_);
v_typeAnalysis_3443_ = lean_ctor_get(v___x_3438_, 3);
lean_inc_ref(v_typeAnalysis_3443_);
v_goal_3444_ = lean_ctor_get(v___x_3438_, 4);
lean_inc(v_goal_3444_);
v_hypotheses_3445_ = lean_ctor_get(v___x_3438_, 5);
lean_inc_ref(v_hypotheses_3445_);
lean_dec(v___x_3438_);
v___x_3446_ = l_Lean_instBEqMVarId_beq(v_a_3437_, v_goal_3444_);
lean_dec(v_goal_3444_);
if (v___x_3446_ == 0)
{
v___y_3401_ = v___y_3420_;
v___y_3402_ = v___y_3425_;
v___y_3403_ = v___y_3426_;
v___y_3404_ = v_typeAnalysis_3443_;
v___y_3405_ = v_rewriteDSimpCache_3441_;
v___y_3406_ = v___y_3424_;
v___y_3407_ = v___y_3427_;
v___y_3408_ = v_acCache_3442_;
v___y_3409_ = v_hypotheses_3445_;
v___y_3410_ = v_rewriteSimpCache_3440_;
v___y_3411_ = v___y_3423_;
v___y_3412_ = v___y_3421_;
v___y_3413_ = v___y_3422_;
v___y_3414_ = v_a_3437_;
v___y_3415_ = v___x_3428_;
v___y_3416_ = v___x_3428_;
goto v___jp_3400_;
}
else
{
v___y_3401_ = v___y_3420_;
v___y_3402_ = v___y_3425_;
v___y_3403_ = v___y_3426_;
v___y_3404_ = v_typeAnalysis_3443_;
v___y_3405_ = v_rewriteDSimpCache_3441_;
v___y_3406_ = v___y_3424_;
v___y_3407_ = v___y_3427_;
v___y_3408_ = v_acCache_3442_;
v___y_3409_ = v_hypotheses_3445_;
v___y_3410_ = v_rewriteSimpCache_3440_;
v___y_3411_ = v___y_3423_;
v___y_3412_ = v___y_3421_;
v___y_3413_ = v___y_3422_;
v___y_3414_ = v_a_3437_;
v___y_3415_ = v___x_3428_;
v___y_3416_ = v_didChange_3439_;
goto v___jp_3400_;
}
}
else
{
lean_object* v_rewriteSimpCache_3447_; lean_object* v_rewriteDSimpCache_3448_; lean_object* v_acCache_3449_; lean_object* v_typeAnalysis_3450_; lean_object* v_hypotheses_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
v_rewriteSimpCache_3447_ = lean_ctor_get(v___x_3438_, 0);
v_rewriteDSimpCache_3448_ = lean_ctor_get(v___x_3438_, 1);
v_acCache_3449_ = lean_ctor_get(v___x_3438_, 2);
v_typeAnalysis_3450_ = lean_ctor_get(v___x_3438_, 3);
v_hypotheses_3451_ = lean_ctor_get(v___x_3438_, 5);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v___x_3438_, 4);
lean_dec(v_unused_3459_);
v___x_3453_ = v___x_3438_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_hypotheses_3451_);
lean_inc(v_typeAnalysis_3450_);
lean_inc(v_acCache_3449_);
lean_inc(v_rewriteDSimpCache_3448_);
lean_inc(v_rewriteSimpCache_3447_);
lean_dec(v___x_3438_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
lean_inc(v_a_3437_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 4, v_a_3437_);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_rewriteSimpCache_3447_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_rewriteDSimpCache_3448_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_acCache_3449_);
lean_ctor_set(v_reuseFailAlloc_3457_, 3, v_typeAnalysis_3450_);
lean_ctor_set(v_reuseFailAlloc_3457_, 4, v_a_3437_);
lean_ctor_set(v_reuseFailAlloc_3457_, 5, v_hypotheses_3451_);
lean_ctor_set_uint8(v_reuseFailAlloc_3457_, sizeof(void*)*6, v_didChange_3439_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
v___y_3362_ = v___y_3420_;
v___y_3363_ = v___y_3425_;
v___y_3364_ = v___y_3426_;
v___y_3365_ = v___y_3423_;
v___y_3366_ = v___y_3424_;
v___y_3367_ = v___y_3422_;
v___y_3368_ = v___y_3421_;
v___y_3369_ = v_a_3437_;
v___y_3370_ = v___y_3427_;
v___y_3371_ = v___x_3428_;
v_snd_3372_ = v___x_3456_;
goto v___jp_3361_;
}
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
v_a_3460_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3436_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3436_);
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
else
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
lean_dec(v_a_3431_);
v___x_3468_ = lean_box(v___x_3428_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3468_);
v___x_3470_ = v___x_3433_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
v_a_3473_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3430_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3430_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
lean_dec(v_a_3709_);
lean_dec_ref(v_a_3708_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_a_3704_);
lean_dec(v_a_3703_);
lean_dec_ref(v_a_3702_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(lean_object* v_00_u03b1_3712_, lean_object* v_x_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_3713_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3724_, lean_object* v_x_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(v_00_u03b1_3724_, v_x_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3(lean_object* v_cls_3736_, lean_object* v_msg_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_3736_, v_msg_3737_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___boxed(lean_object* v_cls_3748_, lean_object* v_msg_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3(v_cls_3748_, v_msg_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(lean_object* v_oldTraces_3760_, lean_object* v_data_3761_, lean_object* v_ref_3762_, lean_object* v_msg_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(v_oldTraces_3760_, v_data_3761_, v_ref_3762_, v_msg_3763_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___boxed(lean_object* v_oldTraces_3774_, lean_object* v_data_3775_, lean_object* v_ref_3776_, lean_object* v_msg_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(v_oldTraces_3774_, v_data_3775_, v_ref_3776_, v_msg_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3787_;
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
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
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
