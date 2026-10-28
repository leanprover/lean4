// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic public import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow public import Lean.Meta.Tactic.BVDecide.Normalize.Simproc public import Lean.Meta.Tactic.BVDecide.Normalize.Rewrite public import Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten public import Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint public import Lean.Meta.Tactic.BVDecide.Normalize.AC public import Lean.Meta.Tactic.BVDecide.Normalize.Structures public import Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec public import Lean.Meta.Tactic.BVDecide.Normalize.Enums public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis public import Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit public import Lean.Meta.Tactic.BVDecide.Normalize.Reduction public import Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps import Lean.Meta.Sym.Util import Lean.Meta.Sym.Intro import Lean.Meta.Sym.Grind import Lean.Meta.Tactic.Grind.BVDecide.Types
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_embeddedConstraintPass;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_andFlatteningPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass;
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Meta_Grind_BVDecide_bvExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_BVDecide_getCaches___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__4___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__3_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Running preprocessing pipeline"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Preprocessing goal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_config_18_; uint8_t v_acNf_19_; uint8_t v_andFlattening_20_; uint8_t v_embeddedConstraintSubst_21_; lean_object* v_passPipeline_23_; lean_object* v_passPipeline_29_; lean_object* v_passPipeline_32_; 
v_config_18_ = lean_ctor_get(v_a_16_, 0);
v_acNf_19_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*3 + 2);
v_andFlattening_20_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_21_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*3 + 4);
v_passPipeline_32_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__2);
if (v_acNf_19_ == 0)
{
v_passPipeline_29_ = v_passPipeline_32_;
goto v___jp_28_;
}
else
{
lean_object* v___x_33_; 
v___x_33_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__4);
v_passPipeline_29_ = v___x_33_;
goto v___jp_28_;
}
v___jp_22_:
{
if (v_embeddedConstraintSubst_21_ == 0)
{
lean_object* v___x_24_; 
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v_passPipeline_23_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__0);
v___x_26_ = l_List_appendTR___redArg(v_passPipeline_23_, v___x_25_);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
v___jp_28_:
{
if (v_embeddedConstraintSubst_21_ == 0)
{
lean_inc(v_passPipeline_29_);
v_passPipeline_23_ = v_passPipeline_29_;
goto v___jp_22_;
}
else
{
if (v_andFlattening_20_ == 0)
{
lean_inc(v_passPipeline_29_);
v_passPipeline_23_ = v_passPipeline_29_;
goto v___jp_22_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___closed__1);
lean_inc(v_passPipeline_29_);
v___x_31_ = l_List_appendTR___redArg(v_passPipeline_29_, v___x_30_);
v_passPipeline_23_ = v___x_31_;
goto v___jp_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg___boxed(lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_34_);
lean_dec_ref(v_a_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v_a_37_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___boxed(lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline(v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0(lean_object* v_x_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
lean_inc(v___y_68_);
lean_inc_ref(v___y_67_);
lean_inc(v___y_66_);
lean_inc_ref(v___y_65_);
lean_inc(v___y_64_);
v___x_74_ = lean_apply_10(v_x_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, lean_box(0));
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0___boxed(lean_object* v_x_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0(v_x_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(lean_object* v_mvarId_87_, lean_object* v_x_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___f_99_; lean_object* v___x_100_; 
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
lean_inc(v___y_89_);
v___f_99_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_99_, 0, v_x_88_);
lean_closure_set(v___f_99_, 1, v___y_89_);
lean_closure_set(v___f_99_, 2, v___y_90_);
lean_closure_set(v___f_99_, 3, v___y_91_);
lean_closure_set(v___f_99_, 4, v___y_92_);
lean_closure_set(v___f_99_, 5, v___y_93_);
v___x_100_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_87_, v___f_99_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
return v___x_100_;
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg___boxed(lean_object* v_mvarId_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(v_mvarId_109_, v_x_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0(lean_object* v_00_u03b1_122_, lean_object* v_mvarId_123_, lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(v_mvarId_123_, v_x_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___boxed(lean_object* v_00_u03b1_136_, lean_object* v_mvarId_137_, lean_object* v_x_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0(v_00_u03b1_136_, v_mvarId_137_, v_x_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0(lean_object* v_caches_150_, lean_object* v_x_151_){
_start:
{
lean_inc_ref(v_caches_150_);
return v_caches_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0___boxed(lean_object* v_caches_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0(v_caches_152_, v_x_153_);
lean_dec_ref(v_x_153_);
lean_dec_ref(v_caches_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1(lean_object* v_goal_155_, lean_object* v___f_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_st_mk_ref(v_goal_155_);
v___x_168_ = l_Lean_Meta_Grind_BVDecide_bvExt;
v___x_169_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_168_, v___f_156_, v___x_167_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_179_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_179_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_179_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = lean_st_ref_get(v___x_167_);
lean_dec(v___x_167_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_a_170_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v___x_167_);
v_a_180_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_169_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_169_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1___boxed(lean_object* v_goal_188_, lean_object* v___f_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1(v_goal_188_, v___f_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2(lean_object* v_goal_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_st_mk_ref(v_goal_201_);
v___x_213_ = l_Lean_Meta_Grind_BVDecide_getCaches___redArg(v___x_212_, v___y_209_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_223_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_223_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_223_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_218_ = lean_st_ref_get(v___x_212_);
lean_dec(v___x_212_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_a_214_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_219_);
v___x_221_ = v___x_216_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec(v___x_212_);
v_a_224_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_213_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_213_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2___boxed(lean_object* v_goal_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2(v_goal_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(lean_object* v_x_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___x_328_; lean_object* v_target_329_; 
v___x_328_ = lean_st_ref_get(v_a_246_);
v_target_329_ = lean_ctor_get(v___x_328_, 2);
lean_inc_ref(v_target_329_);
lean_dec(v___x_328_);
if (lean_obj_tag(v_target_329_) == 1)
{
lean_object* v_goal_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_379_; 
v_goal_330_ = lean_ctor_get(v_target_329_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_target_329_);
if (v_isSharedCheck_379_ == 0)
{
v___x_332_ = v_target_329_;
v_isShared_333_ = v_isSharedCheck_379_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_goal_330_);
lean_dec(v_target_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_379_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_mvarId_334_; lean_object* v___f_335_; lean_object* v___x_336_; 
v_mvarId_334_ = lean_ctor_get(v_goal_330_, 1);
lean_inc(v_mvarId_334_);
v___f_335_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__2___boxed), 11, 1);
lean_closure_set(v___f_335_, 0, v_goal_330_);
v___x_336_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(v_mvarId_334_, v___f_335_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_341_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v_fst_338_ = lean_ctor_get(v_a_337_, 0);
lean_inc(v_fst_338_);
v_snd_339_ = lean_ctor_get(v_a_337_, 1);
lean_inc(v_snd_339_);
lean_dec(v_a_337_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v_snd_339_);
v___x_341_ = v___x_332_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_snd_339_);
v___x_341_ = v_reuseFailAlloc_370_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_342_; lean_object* v_caches_343_; lean_object* v_typeAnalysis_344_; lean_object* v_hypotheses_345_; uint8_t v_didChange_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_368_; 
v___x_342_ = lean_st_ref_take(v_a_246_);
v_caches_343_ = lean_ctor_get(v___x_342_, 0);
v_typeAnalysis_344_ = lean_ctor_get(v___x_342_, 1);
v_hypotheses_345_ = lean_ctor_get(v___x_342_, 3);
v_didChange_346_ = lean_ctor_get_uint8(v___x_342_, sizeof(void*)*4);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v___x_342_, 2);
lean_dec(v_unused_369_);
v___x_348_ = v___x_342_;
v_isShared_349_ = v_isSharedCheck_368_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_hypotheses_345_);
lean_inc(v_typeAnalysis_344_);
lean_inc(v_caches_343_);
lean_dec(v___x_342_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_368_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 2, v___x_341_);
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_caches_343_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_typeAnalysis_344_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_hypotheses_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_367_, sizeof(void*)*4, v_didChange_346_);
v___x_351_ = v_reuseFailAlloc_367_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_typeAnalysis_354_; lean_object* v_target_355_; lean_object* v_hypotheses_356_; uint8_t v_didChange_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v___x_352_ = lean_st_ref_put(v_a_246_, v___x_351_);
v___x_353_ = lean_st_ref_take(v_a_246_);
v_typeAnalysis_354_ = lean_ctor_get(v___x_353_, 1);
v_target_355_ = lean_ctor_get(v___x_353_, 2);
v_hypotheses_356_ = lean_ctor_get(v___x_353_, 3);
v_didChange_357_ = lean_ctor_get_uint8(v___x_353_, sizeof(void*)*4);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_353_, 0);
lean_dec(v_unused_366_);
v___x_359_ = v___x_353_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_hypotheses_356_);
lean_inc(v_target_355_);
lean_inc(v_typeAnalysis_354_);
lean_dec(v___x_353_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v_fst_338_);
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_fst_338_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_typeAnalysis_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_target_355_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_hypotheses_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_364_, sizeof(void*)*4, v_didChange_357_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_st_ref_put(v_a_246_, v___x_362_);
v___y_258_ = v_a_245_;
v___y_259_ = v_a_246_;
v___y_260_ = v_a_247_;
v___y_261_ = v_a_248_;
v___y_262_ = v_a_249_;
v___y_263_ = v_a_250_;
v___y_264_ = v_a_251_;
v___y_265_ = v_a_252_;
v___y_266_ = v_a_253_;
v___y_267_ = v_a_254_;
v___y_268_ = v_a_255_;
goto v___jp_257_;
}
}
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_del_object(v___x_332_);
lean_dec_ref(v_x_244_);
v_a_371_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_336_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_336_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
else
{
lean_dec_ref(v_target_329_);
v___y_258_ = v_a_245_;
v___y_259_ = v_a_246_;
v___y_260_ = v_a_247_;
v___y_261_ = v_a_248_;
v___y_262_ = v_a_249_;
v___y_263_ = v_a_250_;
v___y_264_ = v_a_251_;
v___y_265_ = v_a_252_;
v___y_266_ = v_a_253_;
v___y_267_ = v_a_254_;
v___y_268_ = v_a_255_;
goto v___jp_257_;
}
v___jp_257_:
{
lean_object* v___x_269_; 
lean_inc(v___y_268_);
lean_inc_ref(v___y_267_);
lean_inc(v___y_266_);
lean_inc_ref(v___y_265_);
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
lean_inc(v___y_260_);
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
v___x_269_ = lean_apply_12(v_x_244_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, lean_box(0));
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v_mode_271_; uint8_t v___x_272_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
v_mode_271_ = lean_ctor_get(v___y_258_, 1);
v___x_272_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Mode_isPush(v_mode_271_);
if (v___x_272_ == 0)
{
lean_dec(v_a_270_);
return v___x_269_;
}
else
{
lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_326_; 
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v___x_269_, 0);
lean_dec(v_unused_327_);
v___x_274_ = v___x_269_;
v_isShared_275_ = v_isSharedCheck_326_;
goto v_resetjp_273_;
}
else
{
lean_dec(v___x_269_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_326_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v_caches_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v_target_280_; 
v___x_276_ = lean_st_ref_get(v___y_259_);
v_caches_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc_ref(v_caches_277_);
lean_dec(v___x_276_);
v___f_278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_278_, 0, v_caches_277_);
v___x_279_ = lean_st_ref_get(v___y_259_);
v_target_280_ = lean_ctor_get(v___x_279_, 2);
lean_inc_ref(v_target_280_);
lean_dec(v___x_279_);
if (lean_obj_tag(v_target_280_) == 1)
{
lean_object* v_goal_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_322_; 
lean_del_object(v___x_274_);
v_goal_281_ = lean_ctor_get(v_target_280_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v_target_280_);
if (v_isSharedCheck_322_ == 0)
{
v___x_283_ = v_target_280_;
v_isShared_284_ = v_isSharedCheck_322_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_goal_281_);
lean_dec(v_target_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_322_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_mvarId_285_; lean_object* v___f_286_; lean_object* v___x_287_; 
v_mvarId_285_ = lean_ctor_get(v_goal_281_, 1);
lean_inc(v_mvarId_285_);
v___f_286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___lam__1___boxed), 12, 2);
lean_closure_set(v___f_286_, 0, v_goal_281_);
lean_closure_set(v___f_286_, 1, v___f_278_);
v___x_287_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches_spec__0___redArg(v_mvarId_285_, v___f_286_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_313_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_313_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_313_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_313_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_snd_292_; lean_object* v___x_294_; 
v_snd_292_ = lean_ctor_get(v_a_288_, 1);
lean_inc(v_snd_292_);
lean_dec(v_a_288_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_snd_292_);
v___x_294_ = v___x_283_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_snd_292_);
v___x_294_ = v_reuseFailAlloc_312_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v_caches_296_; lean_object* v_typeAnalysis_297_; lean_object* v_hypotheses_298_; uint8_t v_didChange_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_310_; 
v___x_295_ = lean_st_ref_take(v___y_259_);
v_caches_296_ = lean_ctor_get(v___x_295_, 0);
v_typeAnalysis_297_ = lean_ctor_get(v___x_295_, 1);
v_hypotheses_298_ = lean_ctor_get(v___x_295_, 3);
v_didChange_299_ = lean_ctor_get_uint8(v___x_295_, sizeof(void*)*4);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v___x_295_, 2);
lean_dec(v_unused_311_);
v___x_301_ = v___x_295_;
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_hypotheses_298_);
lean_inc(v_typeAnalysis_297_);
lean_inc(v_caches_296_);
lean_dec(v___x_295_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 2, v___x_294_);
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_caches_296_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_typeAnalysis_297_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_hypotheses_298_);
lean_ctor_set_uint8(v_reuseFailAlloc_309_, sizeof(void*)*4, v_didChange_299_);
v___x_304_ = v_reuseFailAlloc_309_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_305_ = lean_st_ref_put(v___y_259_, v___x_304_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_a_270_);
v___x_307_ = v___x_290_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_270_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_del_object(v___x_283_);
lean_dec(v_a_270_);
v_a_314_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_287_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_287_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
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
else
{
lean_object* v___x_324_; 
lean_dec_ref(v_target_280_);
lean_dec_ref(v___f_278_);
if (v_isShared_275_ == 0)
{
v___x_324_ = v___x_274_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_270_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
else
{
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg___boxed(lean_object* v_x_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(v_x_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches(lean_object* v_00_u03b1_394_, lean_object* v_x_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(v_x_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___boxed(lean_object* v_00_u03b1_409_, lean_object* v_x_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches(v_00_u03b1_409_, v_x_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_423_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_unsigned_to_nat(32u);
v___x_425_ = lean_mk_empty_array_with_capacity(v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_427_ = ((size_t)5ULL);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_unsigned_to_nat(32u);
v___x_430_ = lean_mk_empty_array_with_capacity(v___x_429_);
v___x_431_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__0);
v___x_432_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_428_);
lean_ctor_set(v___x_432_, 3, v___x_428_);
lean_ctor_set_usize(v___x_432_, 4, v___x_427_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; lean_object* v_traceState_436_; lean_object* v_traces_437_; lean_object* v___x_438_; lean_object* v_traceState_439_; lean_object* v_env_440_; lean_object* v_nextMacroScope_441_; lean_object* v_ngen_442_; lean_object* v_auxDeclNGen_443_; lean_object* v_cache_444_; lean_object* v_recordedDeps_445_; lean_object* v_messages_446_; lean_object* v_infoState_447_; lean_object* v_snapshotTasks_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_467_; 
v___x_435_ = lean_st_ref_get(v___y_433_);
v_traceState_436_ = lean_ctor_get(v___x_435_, 4);
lean_inc_ref(v_traceState_436_);
lean_dec(v___x_435_);
v_traces_437_ = lean_ctor_get(v_traceState_436_, 0);
lean_inc_ref(v_traces_437_);
lean_dec_ref(v_traceState_436_);
v___x_438_ = lean_st_ref_take(v___y_433_);
v_traceState_439_ = lean_ctor_get(v___x_438_, 4);
v_env_440_ = lean_ctor_get(v___x_438_, 0);
v_nextMacroScope_441_ = lean_ctor_get(v___x_438_, 1);
v_ngen_442_ = lean_ctor_get(v___x_438_, 2);
v_auxDeclNGen_443_ = lean_ctor_get(v___x_438_, 3);
v_cache_444_ = lean_ctor_get(v___x_438_, 5);
v_recordedDeps_445_ = lean_ctor_get(v___x_438_, 6);
v_messages_446_ = lean_ctor_get(v___x_438_, 7);
v_infoState_447_ = lean_ctor_get(v___x_438_, 8);
v_snapshotTasks_448_ = lean_ctor_get(v___x_438_, 9);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_467_ == 0)
{
v___x_450_ = v___x_438_;
v_isShared_451_ = v_isSharedCheck_467_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_snapshotTasks_448_);
lean_inc(v_infoState_447_);
lean_inc(v_messages_446_);
lean_inc(v_recordedDeps_445_);
lean_inc(v_cache_444_);
lean_inc(v_traceState_439_);
lean_inc(v_auxDeclNGen_443_);
lean_inc(v_ngen_442_);
lean_inc(v_nextMacroScope_441_);
lean_inc(v_env_440_);
lean_dec(v___x_438_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_467_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint64_t v_tid_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_465_; 
v_tid_452_ = lean_ctor_get_uint64(v_traceState_439_, sizeof(void*)*1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_traceState_439_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_traceState_439_, 0);
lean_dec(v_unused_466_);
v___x_454_ = v_traceState_439_;
v_isShared_455_ = v_isSharedCheck_465_;
goto v_resetjp_453_;
}
else
{
lean_dec(v_traceState_439_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_465_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___closed__1);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_456_);
lean_ctor_set_uint64(v_reuseFailAlloc_464_, sizeof(void*)*1, v_tid_452_);
v___x_458_ = v_reuseFailAlloc_464_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 4, v___x_458_);
v___x_460_ = v___x_450_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_env_440_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_nextMacroScope_441_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_ngen_442_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_auxDeclNGen_443_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_cache_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_recordedDeps_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_messages_446_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_infoState_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_snapshotTasks_448_);
v___x_460_ = v_reuseFailAlloc_463_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_st_ref_put(v___y_433_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_traces_437_);
return v___x_462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg___boxed(lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v___y_468_);
lean_dec(v___y_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v___y_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___boxed(lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0(v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_496_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(lean_object* v_opts_497_, lean_object* v_opt_498_){
_start:
{
lean_object* v_name_499_; lean_object* v_defValue_500_; lean_object* v_map_501_; lean_object* v___x_502_; 
v_name_499_ = lean_ctor_get(v_opt_498_, 0);
v_defValue_500_ = lean_ctor_get(v_opt_498_, 1);
v_map_501_ = lean_ctor_get(v_opts_497_, 0);
v___x_502_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_501_, v_name_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
uint8_t v___x_503_; 
v___x_503_ = lean_unbox(v_defValue_500_);
return v___x_503_;
}
else
{
lean_object* v_val_504_; 
v_val_504_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v___x_502_, 1);
if (lean_obj_tag(v_val_504_) == 1)
{
uint8_t v_v_505_; 
v_v_505_ = lean_ctor_get_uint8(v_val_504_, 0);
lean_dec_ref_known(v_val_504_, 0);
return v_v_505_;
}
else
{
uint8_t v___x_506_; 
lean_dec(v_val_504_);
v___x_506_ = lean_unbox(v_defValue_500_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1___boxed(lean_object* v_opts_507_, lean_object* v_opt_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_opts_507_, v_opt_508_);
lean_dec_ref(v_opt_508_);
lean_dec_ref(v_opts_507_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__0));
v___x_513_ = l_Lean_stringToMessageData(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0(lean_object* v_name_514_, lean_object* v_x_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___closed__1);
v___x_529_ = l_Lean_MessageData_ofName(v_name_514_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed(lean_object* v_name_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0(v_name_532_, v_x_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec_ref(v_x_533_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3_spec__7(lean_object* v_msgData_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; lean_object* v_env_554_; uint8_t v___x_555_; lean_object* v_env_556_; lean_object* v___x_557_; lean_object* v_toCold_558_; lean_object* v_mctx_559_; lean_object* v_lctx_560_; lean_object* v_options_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_553_ = lean_st_ref_get(v___y_551_);
v_env_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc_ref(v_env_554_);
lean_dec(v___x_553_);
v___x_555_ = 0;
v_env_556_ = l_Lean_Environment_setRecordingDeps(v_env_554_, v___x_555_);
v___x_557_ = lean_st_ref_get(v___y_549_);
v_toCold_558_ = lean_ctor_get(v___y_550_, 0);
v_mctx_559_ = lean_ctor_get(v___x_557_, 0);
lean_inc_ref(v_mctx_559_);
lean_dec(v___x_557_);
v_lctx_560_ = lean_ctor_get(v___y_548_, 2);
v_options_561_ = lean_ctor_get(v_toCold_558_, 2);
lean_inc_ref(v_options_561_);
lean_inc_ref(v_lctx_560_);
v___x_562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_562_, 0, v_env_556_);
lean_ctor_set(v___x_562_, 1, v_mctx_559_);
lean_ctor_set(v___x_562_, 2, v_lctx_560_);
lean_ctor_set(v___x_562_, 3, v_options_561_);
v___x_563_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_msgData_547_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3_spec__7___boxed(lean_object* v_msgData_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3_spec__7(v_msgData_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_571_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_572_; double v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_float_of_nat(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg(lean_object* v_cls_577_, lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_ref_584_; lean_object* v___x_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_631_; 
v_ref_584_ = lean_ctor_get(v___y_581_, 2);
v___x_585_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3_spec__7(v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_631_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_631_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_631_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v_traceState_591_; lean_object* v_env_592_; lean_object* v_nextMacroScope_593_; lean_object* v_ngen_594_; lean_object* v_auxDeclNGen_595_; lean_object* v_cache_596_; lean_object* v_recordedDeps_597_; lean_object* v_messages_598_; lean_object* v_infoState_599_; lean_object* v_snapshotTasks_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_630_; 
v___x_590_ = lean_st_ref_take(v___y_582_);
v_traceState_591_ = lean_ctor_get(v___x_590_, 4);
v_env_592_ = lean_ctor_get(v___x_590_, 0);
v_nextMacroScope_593_ = lean_ctor_get(v___x_590_, 1);
v_ngen_594_ = lean_ctor_get(v___x_590_, 2);
v_auxDeclNGen_595_ = lean_ctor_get(v___x_590_, 3);
v_cache_596_ = lean_ctor_get(v___x_590_, 5);
v_recordedDeps_597_ = lean_ctor_get(v___x_590_, 6);
v_messages_598_ = lean_ctor_get(v___x_590_, 7);
v_infoState_599_ = lean_ctor_get(v___x_590_, 8);
v_snapshotTasks_600_ = lean_ctor_get(v___x_590_, 9);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_630_ == 0)
{
v___x_602_ = v___x_590_;
v_isShared_603_ = v_isSharedCheck_630_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snapshotTasks_600_);
lean_inc(v_infoState_599_);
lean_inc(v_messages_598_);
lean_inc(v_recordedDeps_597_);
lean_inc(v_cache_596_);
lean_inc(v_traceState_591_);
lean_inc(v_auxDeclNGen_595_);
lean_inc(v_ngen_594_);
lean_inc(v_nextMacroScope_593_);
lean_inc(v_env_592_);
lean_dec(v___x_590_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_630_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
uint64_t v_tid_604_; lean_object* v_traces_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_629_; 
v_tid_604_ = lean_ctor_get_uint64(v_traceState_591_, sizeof(void*)*1);
v_traces_605_ = lean_ctor_get(v_traceState_591_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_traceState_591_);
if (v_isSharedCheck_629_ == 0)
{
v___x_607_ = v_traceState_591_;
v_isShared_608_ = v_isSharedCheck_629_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_traces_605_);
lean_dec(v_traceState_591_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_629_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; double v___x_611_; uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_609_ = lean_box(0);
v___x_610_ = lean_box(0);
v___x_611_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0);
v___x_612_ = 0;
v___x_613_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1));
v___x_614_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_614_, 0, v_cls_577_);
lean_ctor_set(v___x_614_, 1, v___x_610_);
lean_ctor_set(v___x_614_, 2, v___x_613_);
lean_ctor_set_float(v___x_614_, sizeof(void*)*3, v___x_611_);
lean_ctor_set_float(v___x_614_, sizeof(void*)*3 + 8, v___x_611_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*3 + 16, v___x_612_);
v___x_615_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__2));
v___x_616_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v_a_586_);
lean_ctor_set(v___x_616_, 2, v___x_615_);
lean_inc(v_ref_584_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v_ref_584_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_PersistentArray_push___redArg(v_traces_605_, v___x_617_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_618_);
v___x_620_ = v___x_607_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_618_);
lean_ctor_set_uint64(v_reuseFailAlloc_628_, sizeof(void*)*1, v_tid_604_);
v___x_620_ = v_reuseFailAlloc_628_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 4, v___x_620_);
v___x_622_ = v___x_602_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_env_592_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_nextMacroScope_593_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_ngen_594_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_auxDeclNGen_595_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v_cache_596_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_recordedDeps_597_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_messages_598_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v_infoState_599_);
lean_ctor_set(v_reuseFailAlloc_627_, 9, v_snapshotTasks_600_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_st_ref_put(v___y_582_, v___x_622_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_609_);
v___x_625_ = v___x_588_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_609_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___boxed(lean_object* v_cls_632_, lean_object* v_msg_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg(v_cls_632_, v_msg_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__5(lean_object* v_opts_640_, lean_object* v_opt_641_){
_start:
{
lean_object* v_name_642_; lean_object* v_defValue_643_; lean_object* v_map_644_; lean_object* v___x_645_; 
v_name_642_ = lean_ctor_get(v_opt_641_, 0);
v_defValue_643_ = lean_ctor_get(v_opt_641_, 1);
v_map_644_ = lean_ctor_get(v_opts_640_, 0);
v___x_645_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_644_, v_name_642_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_inc(v_defValue_643_);
return v_defValue_643_;
}
else
{
lean_object* v_val_646_; 
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v___x_645_, 1);
if (lean_obj_tag(v_val_646_) == 3)
{
lean_object* v_v_647_; 
v_v_647_ = lean_ctor_get(v_val_646_, 0);
lean_inc(v_v_647_);
lean_dec_ref_known(v_val_646_, 1);
return v_v_647_;
}
else
{
lean_dec(v_val_646_);
lean_inc(v_defValue_643_);
return v_defValue_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__5___boxed(lean_object* v_opts_648_, lean_object* v_opt_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__5(v_opts_648_, v_opt_649_);
lean_dec_ref(v_opt_649_);
lean_dec_ref(v_opts_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2_spec__3(size_t v_sz_651_, size_t v_i_652_, lean_object* v_bs_653_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = lean_usize_dec_lt(v_i_652_, v_sz_651_);
if (v___x_654_ == 0)
{
return v_bs_653_;
}
else
{
lean_object* v_v_655_; lean_object* v_msg_656_; lean_object* v___x_657_; lean_object* v_bs_x27_658_; size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
v_v_655_ = lean_array_uget_borrowed(v_bs_653_, v_i_652_);
v_msg_656_ = lean_ctor_get(v_v_655_, 1);
lean_inc_ref(v_msg_656_);
v___x_657_ = lean_unsigned_to_nat(0u);
v_bs_x27_658_ = lean_array_uset(v_bs_653_, v_i_652_, v___x_657_);
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_add(v_i_652_, v___x_659_);
v___x_661_ = lean_array_uset(v_bs_x27_658_, v_i_652_, v_msg_656_);
v_i_652_ = v___x_660_;
v_bs_653_ = v___x_661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_663_, lean_object* v_i_664_, lean_object* v_bs_665_){
_start:
{
size_t v_sz_boxed_666_; size_t v_i_boxed_667_; lean_object* v_res_668_; 
v_sz_boxed_666_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v_i_boxed_667_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_res_668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2_spec__3(v_sz_boxed_666_, v_i_boxed_667_, v_bs_665_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___redArg(lean_object* v_oldTraces_669_, lean_object* v_data_670_, lean_object* v_ref_671_, lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_toCold_678_; lean_object* v_currRecDepth_679_; lean_object* v_ref_680_; uint16_t v_optionFlags_681_; uint8_t v_suppressElabErrors_682_; uint8_t v_checkDeprecated_683_; uint8_t v_isRecordingDeps_684_; lean_object* v_ref_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_traceState_688_; lean_object* v_traces_689_; lean_object* v___x_690_; size_t v_sz_691_; size_t v___x_692_; lean_object* v___x_693_; lean_object* v_msg_694_; lean_object* v___x_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_734_; 
v_toCold_678_ = lean_ctor_get(v___y_675_, 0);
v_currRecDepth_679_ = lean_ctor_get(v___y_675_, 1);
v_ref_680_ = lean_ctor_get(v___y_675_, 2);
v_optionFlags_681_ = lean_ctor_get_uint16(v___y_675_, sizeof(void*)*3);
v_suppressElabErrors_682_ = lean_ctor_get_uint8(v___y_675_, sizeof(void*)*3 + 2);
v_checkDeprecated_683_ = lean_ctor_get_uint8(v___y_675_, sizeof(void*)*3 + 3);
v_isRecordingDeps_684_ = lean_ctor_get_uint8(v___y_675_, sizeof(void*)*3 + 4);
v_ref_685_ = l_Lean_replaceRef(v_ref_671_, v_ref_680_);
lean_inc(v_currRecDepth_679_);
lean_inc_ref(v_toCold_678_);
v___x_686_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_686_, 0, v_toCold_678_);
lean_ctor_set(v___x_686_, 1, v_currRecDepth_679_);
lean_ctor_set(v___x_686_, 2, v_ref_685_);
lean_ctor_set_uint16(v___x_686_, sizeof(void*)*3, v_optionFlags_681_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*3 + 2, v_suppressElabErrors_682_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*3 + 3, v_checkDeprecated_683_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*3 + 4, v_isRecordingDeps_684_);
v___x_687_ = lean_st_ref_get(v___y_676_);
v_traceState_688_ = lean_ctor_get(v___x_687_, 4);
lean_inc_ref(v_traceState_688_);
lean_dec(v___x_687_);
v_traces_689_ = lean_ctor_get(v_traceState_688_, 0);
lean_inc_ref(v_traces_689_);
lean_dec_ref(v_traceState_688_);
v___x_690_ = l_Lean_PersistentArray_toArray___redArg(v_traces_689_);
lean_dec_ref(v_traces_689_);
v_sz_691_ = lean_array_size(v___x_690_);
v___x_692_ = ((size_t)0ULL);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2_spec__3(v_sz_691_, v___x_692_, v___x_690_);
v_msg_694_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_694_, 0, v_data_670_);
lean_ctor_set(v_msg_694_, 1, v_msg_672_);
lean_ctor_set(v_msg_694_, 2, v___x_693_);
v___x_695_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3_spec__7(v_msg_694_, v___y_673_, v___y_674_, v___x_686_, v___y_676_);
lean_dec_ref_known(v___x_686_, 3);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_734_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_734_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_734_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v_traceState_701_; lean_object* v_env_702_; lean_object* v_nextMacroScope_703_; lean_object* v_ngen_704_; lean_object* v_auxDeclNGen_705_; lean_object* v_cache_706_; lean_object* v_recordedDeps_707_; lean_object* v_messages_708_; lean_object* v_infoState_709_; lean_object* v_snapshotTasks_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_733_; 
v___x_700_ = lean_st_ref_take(v___y_676_);
v_traceState_701_ = lean_ctor_get(v___x_700_, 4);
v_env_702_ = lean_ctor_get(v___x_700_, 0);
v_nextMacroScope_703_ = lean_ctor_get(v___x_700_, 1);
v_ngen_704_ = lean_ctor_get(v___x_700_, 2);
v_auxDeclNGen_705_ = lean_ctor_get(v___x_700_, 3);
v_cache_706_ = lean_ctor_get(v___x_700_, 5);
v_recordedDeps_707_ = lean_ctor_get(v___x_700_, 6);
v_messages_708_ = lean_ctor_get(v___x_700_, 7);
v_infoState_709_ = lean_ctor_get(v___x_700_, 8);
v_snapshotTasks_710_ = lean_ctor_get(v___x_700_, 9);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_733_ == 0)
{
v___x_712_ = v___x_700_;
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snapshotTasks_710_);
lean_inc(v_infoState_709_);
lean_inc(v_messages_708_);
lean_inc(v_recordedDeps_707_);
lean_inc(v_cache_706_);
lean_inc(v_traceState_701_);
lean_inc(v_auxDeclNGen_705_);
lean_inc(v_ngen_704_);
lean_inc(v_nextMacroScope_703_);
lean_inc(v_env_702_);
lean_dec(v___x_700_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint64_t v_tid_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_731_; 
v_tid_714_ = lean_ctor_get_uint64(v_traceState_701_, sizeof(void*)*1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_traceState_701_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_traceState_701_, 0);
lean_dec(v_unused_732_);
v___x_716_ = v_traceState_701_;
v_isShared_717_ = v_isSharedCheck_731_;
goto v_resetjp_715_;
}
else
{
lean_dec(v_traceState_701_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_731_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_718_ = lean_box(0);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v_ref_671_);
lean_ctor_set(v___x_719_, 1, v_a_696_);
v___x_720_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_669_, v___x_719_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_720_);
v___x_722_ = v___x_716_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_720_);
lean_ctor_set_uint64(v_reuseFailAlloc_730_, sizeof(void*)*1, v_tid_714_);
v___x_722_ = v_reuseFailAlloc_730_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 4, v___x_722_);
v___x_724_ = v___x_712_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_env_702_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_nextMacroScope_703_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_ngen_704_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_auxDeclNGen_705_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_729_, 5, v_cache_706_);
lean_ctor_set(v_reuseFailAlloc_729_, 6, v_recordedDeps_707_);
lean_ctor_set(v_reuseFailAlloc_729_, 7, v_messages_708_);
lean_ctor_set(v_reuseFailAlloc_729_, 8, v_infoState_709_);
lean_ctor_set(v_reuseFailAlloc_729_, 9, v_snapshotTasks_710_);
v___x_724_ = v_reuseFailAlloc_729_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_st_ref_put(v___y_676_, v___x_724_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_718_);
v___x_727_ = v___x_698_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_718_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_735_, lean_object* v_data_736_, lean_object* v_ref_737_, lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___redArg(v_oldTraces_735_, v_data_736_, v_ref_737_, v_msg_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___redArg(lean_object* v_x_745_){
_start:
{
if (lean_obj_tag(v_x_745_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v_x_745_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_745_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v_x_745_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v_x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 1);
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_755_ = lean_ctor_get(v_x_745_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_x_745_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v_x_745_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v_x_745_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 0);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___redArg___boxed(lean_object* v_x_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___redArg(v_x_763_);
return v_res_765_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__4(lean_object* v_e_766_){
_start:
{
if (lean_obj_tag(v_e_766_) == 0)
{
uint8_t v___x_767_; 
v___x_767_ = 2;
return v___x_767_;
}
else
{
lean_object* v_a_768_; uint8_t v___x_769_; 
v_a_768_ = lean_ctor_get(v_e_766_, 0);
v___x_769_ = lean_unbox(v_a_768_);
if (v___x_769_ == 0)
{
uint8_t v___x_770_; 
v___x_770_ = 1;
return v___x_770_;
}
else
{
uint8_t v___x_771_; 
v___x_771_ = 0;
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__4___boxed(lean_object* v_e_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__4(v_e_772_);
lean_dec_ref(v_e_772_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__1(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__0));
v___x_777_ = l_Lean_stringToMessageData(v___x_776_);
return v___x_777_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__2(void){
_start:
{
lean_object* v___x_778_; double v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(1000u);
v___x_779_ = lean_float_of_nat(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(lean_object* v_cls_780_, uint8_t v_collapsed_781_, lean_object* v_tag_782_, lean_object* v_opts_783_, uint8_t v_clsEnabled_784_, lean_object* v_oldTraces_785_, lean_object* v_msg_786_, lean_object* v_resStartStop_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v_data_805_; lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___y_821_; lean_object* v_a_822_; uint8_t v___y_837_; double v___y_869_; 
v_fst_800_ = lean_ctor_get(v_resStartStop_787_, 0);
lean_inc(v_fst_800_);
v_snd_801_ = lean_ctor_get(v_resStartStop_787_, 1);
lean_inc(v_snd_801_);
lean_dec_ref(v_resStartStop_787_);
v_fst_816_ = lean_ctor_get(v_snd_801_, 0);
lean_inc(v_fst_816_);
v_snd_817_ = lean_ctor_get(v_snd_801_, 1);
lean_inc(v_snd_817_);
lean_dec(v_snd_801_);
v___x_818_ = l_Lean_trace_profiler;
v___x_819_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_opts_783_, v___x_818_);
if (v___x_819_ == 0)
{
v___y_837_ = v___x_819_;
goto v___jp_836_;
}
else
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = l_Lean_trace_profiler_useHeartbeats;
v___x_875_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_opts_783_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; double v___x_878_; double v___x_879_; double v___x_880_; 
v___x_876_ = l_Lean_trace_profiler_threshold;
v___x_877_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__5(v_opts_783_, v___x_876_);
v___x_878_ = lean_float_of_nat(v___x_877_);
v___x_879_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__2);
v___x_880_ = lean_float_div(v___x_878_, v___x_879_);
v___y_869_ = v___x_880_;
goto v___jp_868_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; double v___x_883_; 
v___x_881_ = l_Lean_trace_profiler_threshold;
v___x_882_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__5(v_opts_783_, v___x_881_);
v___x_883_ = lean_float_of_nat(v___x_882_);
v___y_869_ = v___x_883_;
goto v___jp_868_;
}
}
v___jp_802_:
{
lean_object* v___x_806_; 
lean_inc(v___y_804_);
v___x_806_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___redArg(v_oldTraces_785_, v_data_805_, v___y_804_, v___y_803_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_807_; 
lean_dec_ref_known(v___x_806_, 1);
v___x_807_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___redArg(v_fst_800_);
return v___x_807_;
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_fst_800_);
v_a_808_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_806_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_806_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
v___jp_820_:
{
uint8_t v_result_823_; lean_object* v___x_824_; lean_object* v___x_825_; double v___x_826_; lean_object* v_data_827_; 
v_result_823_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__4(v_fst_800_);
v___x_824_ = lean_box(v_result_823_);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
v___x_826_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_782_);
lean_inc_ref(v___x_825_);
lean_inc(v_cls_780_);
v_data_827_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_827_, 0, v_cls_780_);
lean_ctor_set(v_data_827_, 1, v___x_825_);
lean_ctor_set(v_data_827_, 2, v_tag_782_);
lean_ctor_set_float(v_data_827_, sizeof(void*)*3, v___x_826_);
lean_ctor_set_float(v_data_827_, sizeof(void*)*3 + 8, v___x_826_);
lean_ctor_set_uint8(v_data_827_, sizeof(void*)*3 + 16, v_collapsed_781_);
if (v___x_819_ == 0)
{
lean_dec_ref_known(v___x_825_, 1);
lean_dec(v_snd_817_);
lean_dec(v_fst_816_);
lean_dec_ref(v_tag_782_);
lean_dec(v_cls_780_);
v___y_803_ = v_a_822_;
v___y_804_ = v___y_821_;
v_data_805_ = v_data_827_;
goto v___jp_802_;
}
else
{
lean_object* v_data_828_; double v___x_829_; double v___x_830_; 
lean_dec_ref_known(v_data_827_, 3);
v_data_828_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_828_, 0, v_cls_780_);
lean_ctor_set(v_data_828_, 1, v___x_825_);
lean_ctor_set(v_data_828_, 2, v_tag_782_);
v___x_829_ = lean_unbox_float(v_fst_816_);
lean_dec(v_fst_816_);
lean_ctor_set_float(v_data_828_, sizeof(void*)*3, v___x_829_);
v___x_830_ = lean_unbox_float(v_snd_817_);
lean_dec(v_snd_817_);
lean_ctor_set_float(v_data_828_, sizeof(void*)*3 + 8, v___x_830_);
lean_ctor_set_uint8(v_data_828_, sizeof(void*)*3 + 16, v_collapsed_781_);
v___y_803_ = v_a_822_;
v___y_804_ = v___y_821_;
v_data_805_ = v_data_828_;
goto v___jp_802_;
}
}
v___jp_831_:
{
lean_object* v_ref_832_; lean_object* v___x_833_; 
v_ref_832_ = lean_ctor_get(v___y_797_, 2);
lean_inc(v___y_798_);
lean_inc_ref(v___y_797_);
lean_inc(v___y_796_);
lean_inc_ref(v___y_795_);
lean_inc(v___y_794_);
lean_inc_ref(v___y_793_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v_fst_800_);
v___x_833_ = lean_apply_13(v_msg_786_, v_fst_800_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, lean_box(0));
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___y_821_ = v_ref_832_;
v_a_822_ = v_a_834_;
goto v___jp_820_;
}
else
{
lean_object* v___x_835_; 
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___closed__1);
v___y_821_ = v_ref_832_;
v_a_822_ = v___x_835_;
goto v___jp_820_;
}
}
v___jp_836_:
{
if (v_clsEnabled_784_ == 0)
{
if (v___y_837_ == 0)
{
lean_object* v___x_838_; lean_object* v_traceState_839_; lean_object* v_env_840_; lean_object* v_nextMacroScope_841_; lean_object* v_ngen_842_; lean_object* v_auxDeclNGen_843_; lean_object* v_cache_844_; lean_object* v_recordedDeps_845_; lean_object* v_messages_846_; lean_object* v_infoState_847_; lean_object* v_snapshotTasks_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_snd_817_);
lean_dec(v_fst_816_);
lean_dec_ref(v_msg_786_);
lean_dec_ref(v_tag_782_);
lean_dec(v_cls_780_);
v___x_838_ = lean_st_ref_take(v___y_798_);
v_traceState_839_ = lean_ctor_get(v___x_838_, 4);
v_env_840_ = lean_ctor_get(v___x_838_, 0);
v_nextMacroScope_841_ = lean_ctor_get(v___x_838_, 1);
v_ngen_842_ = lean_ctor_get(v___x_838_, 2);
v_auxDeclNGen_843_ = lean_ctor_get(v___x_838_, 3);
v_cache_844_ = lean_ctor_get(v___x_838_, 5);
v_recordedDeps_845_ = lean_ctor_get(v___x_838_, 6);
v_messages_846_ = lean_ctor_get(v___x_838_, 7);
v_infoState_847_ = lean_ctor_get(v___x_838_, 8);
v_snapshotTasks_848_ = lean_ctor_get(v___x_838_, 9);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_867_ == 0)
{
v___x_850_ = v___x_838_;
v_isShared_851_ = v_isSharedCheck_867_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snapshotTasks_848_);
lean_inc(v_infoState_847_);
lean_inc(v_messages_846_);
lean_inc(v_recordedDeps_845_);
lean_inc(v_cache_844_);
lean_inc(v_traceState_839_);
lean_inc(v_auxDeclNGen_843_);
lean_inc(v_ngen_842_);
lean_inc(v_nextMacroScope_841_);
lean_inc(v_env_840_);
lean_dec(v___x_838_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_867_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint64_t v_tid_852_; lean_object* v_traces_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_866_; 
v_tid_852_ = lean_ctor_get_uint64(v_traceState_839_, sizeof(void*)*1);
v_traces_853_ = lean_ctor_get(v_traceState_839_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_traceState_839_);
if (v_isSharedCheck_866_ == 0)
{
v___x_855_ = v_traceState_839_;
v_isShared_856_ = v_isSharedCheck_866_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_traces_853_);
lean_dec(v_traceState_839_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_866_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_785_, v_traces_853_);
lean_dec_ref(v_traces_853_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_857_);
lean_ctor_set_uint64(v_reuseFailAlloc_865_, sizeof(void*)*1, v_tid_852_);
v___x_859_ = v_reuseFailAlloc_865_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 4, v___x_859_);
v___x_861_ = v___x_850_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_env_840_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_nextMacroScope_841_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_ngen_842_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v_auxDeclNGen_843_);
lean_ctor_set(v_reuseFailAlloc_864_, 4, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_864_, 5, v_cache_844_);
lean_ctor_set(v_reuseFailAlloc_864_, 6, v_recordedDeps_845_);
lean_ctor_set(v_reuseFailAlloc_864_, 7, v_messages_846_);
lean_ctor_set(v_reuseFailAlloc_864_, 8, v_infoState_847_);
lean_ctor_set(v_reuseFailAlloc_864_, 9, v_snapshotTasks_848_);
v___x_861_ = v_reuseFailAlloc_864_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_st_ref_put(v___y_798_, v___x_861_);
v___x_863_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___redArg(v_fst_800_);
return v___x_863_;
}
}
}
}
}
else
{
goto v___jp_831_;
}
}
else
{
goto v___jp_831_;
}
}
v___jp_868_:
{
double v___x_870_; double v___x_871_; double v___x_872_; uint8_t v___x_873_; 
v___x_870_ = lean_unbox_float(v_snd_817_);
v___x_871_ = lean_unbox_float(v_fst_816_);
v___x_872_ = lean_float_sub(v___x_870_, v___x_871_);
v___x_873_ = lean_float_decLt(v___y_869_, v___x_872_);
v___y_837_ = v___x_873_;
goto v___jp_836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2___boxed(lean_object** _args){
lean_object* v_cls_884_ = _args[0];
lean_object* v_collapsed_885_ = _args[1];
lean_object* v_tag_886_ = _args[2];
lean_object* v_opts_887_ = _args[3];
lean_object* v_clsEnabled_888_ = _args[4];
lean_object* v_oldTraces_889_ = _args[5];
lean_object* v_msg_890_ = _args[6];
lean_object* v_resStartStop_891_ = _args[7];
lean_object* v___y_892_ = _args[8];
lean_object* v___y_893_ = _args[9];
lean_object* v___y_894_ = _args[10];
lean_object* v___y_895_ = _args[11];
lean_object* v___y_896_ = _args[12];
lean_object* v___y_897_ = _args[13];
lean_object* v___y_898_ = _args[14];
lean_object* v___y_899_ = _args[15];
lean_object* v___y_900_ = _args[16];
lean_object* v___y_901_ = _args[17];
lean_object* v___y_902_ = _args[18];
lean_object* v___y_903_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_904_; uint8_t v_clsEnabled_boxed_905_; lean_object* v_res_906_; 
v_collapsed_boxed_904_ = lean_unbox(v_collapsed_885_);
v_clsEnabled_boxed_905_ = lean_unbox(v_clsEnabled_888_);
v_res_906_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v_cls_884_, v_collapsed_boxed_904_, v_tag_886_, v_opts_887_, v_clsEnabled_boxed_905_, v_oldTraces_889_, v_msg_890_, v_resStartStop_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v_opts_887_);
return v_res_906_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0(void){
_start:
{
lean_object* v___x_907_; double v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(1000000000u);
v___x_908_ = lean_float_of_nat(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__6));
v___x_921_ = l_Lean_Name_append(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__9(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__8));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline(lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v___y_938_; uint8_t v___y_939_; lean_object* v___y_940_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; uint8_t v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; uint8_t v___y_966_; uint8_t v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; uint8_t v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v_a_977_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; uint8_t v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; uint8_t v___y_996_; uint8_t v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; uint8_t v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v_a_1008_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; uint8_t v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; uint8_t v___y_1029_; uint8_t v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1082_; uint8_t v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; uint8_t v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; uint8_t v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v_a_1178_; lean_object* v___y_1188_; lean_object* v___y_1189_; uint8_t v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; uint8_t v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; uint8_t v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v_a_1209_; uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; uint8_t v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; uint8_t v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1283_; uint8_t v_fixedInt_1284_; uint8_t v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; uint8_t v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v_a_1362_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; uint8_t v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v_a_1393_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; uint8_t v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1467_; uint8_t v_fixedInt_1468_; uint8_t v_enums_1469_; uint8_t v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1527_; uint8_t v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; uint8_t v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v_a_1548_; lean_object* v___y_1561_; uint8_t v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v_a_1582_; uint8_t v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; uint8_t v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; uint8_t v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; uint8_t v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v_a_1718_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; uint8_t v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; uint8_t v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v_a_1748_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; uint8_t v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; uint8_t v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; uint8_t v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; uint8_t v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; uint8_t v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v_a_1897_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; uint8_t v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; uint8_t v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v_a_1928_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; uint8_t v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; uint8_t v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; uint8_t v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v_toCold_2046_; lean_object* v_options_2047_; uint8_t v_hasTrace_2048_; 
v_toCold_2046_ = lean_ctor_get(v_a_934_, 0);
v_options_2047_ = lean_ctor_get(v_toCold_2046_, 2);
v_hasTrace_2048_ = lean_ctor_get_uint8(v_options_2047_, sizeof(void*)*1);
if (v_hasTrace_2048_ == 0)
{
v___y_2032_ = v_a_925_;
v___y_2033_ = v_a_926_;
v___y_2034_ = v_a_927_;
v___y_2035_ = v_a_928_;
v___y_2036_ = v_a_929_;
v___y_2037_ = v_a_930_;
v___y_2038_ = v_a_931_;
v___y_2039_ = v_a_932_;
v___y_2040_ = v_a_933_;
v___y_2041_ = v_a_934_;
v___y_2042_ = v_a_935_;
goto v___jp_2031_;
}
else
{
lean_object* v_inheritedTraceOptions_2049_; lean_object* v_cls_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v_inheritedTraceOptions_2049_ = lean_ctor_get(v_toCold_2046_, 11);
v_cls_2050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_2051_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7);
v___x_2052_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2049_, v_options_2047_, v___x_2051_);
if (v___x_2052_ == 0)
{
v___y_2032_ = v_a_925_;
v___y_2033_ = v_a_926_;
v___y_2034_ = v_a_927_;
v___y_2035_ = v_a_928_;
v___y_2036_ = v_a_929_;
v___y_2037_ = v_a_930_;
v___y_2038_ = v_a_931_;
v___y_2039_ = v_a_932_;
v___y_2040_ = v_a_933_;
v___y_2041_ = v_a_934_;
v___y_2042_ = v_a_935_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__9);
v___x_2054_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg(v_cls_2050_, v___x_2053_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_dec_ref_known(v___x_2054_, 1);
v___y_2032_ = v_a_925_;
v___y_2033_ = v_a_926_;
v___y_2034_ = v_a_927_;
v___y_2035_ = v_a_928_;
v___y_2036_ = v_a_929_;
v___y_2037_ = v_a_930_;
v___y_2038_ = v_a_931_;
v___y_2039_ = v_a_932_;
v___y_2040_ = v_a_933_;
v___y_2041_ = v_a_934_;
v___y_2042_ = v_a_935_;
goto v___jp_2031_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
v___jp_937_:
{
if (lean_obj_tag(v___y_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_954_; 
v_a_941_ = lean_ctor_get(v___y_940_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___y_940_);
if (v_isSharedCheck_954_ == 0)
{
v___x_943_ = v___y_940_;
v_isShared_944_ = v_isSharedCheck_954_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___y_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_954_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v___x_945_; 
v___x_945_ = lean_unbox(v_a_941_);
lean_dec(v_a_941_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = lean_box(v___y_939_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_box(v___y_938_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_950_);
v___x_952_ = v___x_943_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
return v___y_940_;
}
}
v___jp_955_:
{
lean_object* v___x_978_; double v___x_979_; double v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_978_ = lean_io_get_num_heartbeats();
v___x_979_ = lean_float_of_nat(v___y_959_);
v___x_980_ = lean_float_of_nat(v___x_978_);
v___x_981_ = lean_box_float(v___x_979_);
v___x_982_ = lean_box_float(v___x_980_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_a_977_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
v___x_985_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_972_, v___y_971_, v___y_973_, v___y_975_, v___y_963_, v___y_962_, v___y_976_, v___x_984_, v___y_969_, v___y_970_, v___y_960_, v___y_964_, v___y_957_, v___y_965_, v___y_958_, v___y_974_, v___y_961_, v___y_968_, v___y_956_);
v___y_938_ = v___y_967_;
v___y_939_ = v___y_966_;
v___y_940_ = v___x_985_;
goto v___jp_937_;
}
v___jp_986_:
{
lean_object* v___x_1009_; double v___x_1010_; double v___x_1011_; double v___x_1012_; double v___x_1013_; double v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1009_ = lean_io_mono_nanos_now();
v___x_1010_ = lean_float_of_nat(v___y_1003_);
v___x_1011_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0);
v___x_1012_ = lean_float_div(v___x_1010_, v___x_1011_);
v___x_1013_ = lean_float_of_nat(v___x_1009_);
v___x_1014_ = lean_float_div(v___x_1013_, v___x_1011_);
v___x_1015_ = lean_box_float(v___x_1012_);
v___x_1016_ = lean_box_float(v___x_1014_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_a_1008_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc_ref(v___y_1004_);
lean_inc(v___y_1002_);
v___x_1019_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1002_, v___y_1001_, v___y_1004_, v___y_1006_, v___y_993_, v___y_992_, v___y_1007_, v___x_1018_, v___y_999_, v___y_1000_, v___y_990_, v___y_994_, v___y_988_, v___y_995_, v___y_989_, v___y_1005_, v___y_991_, v___y_998_, v___y_987_);
v___y_938_ = v___y_997_;
v___y_939_ = v___y_996_;
v___y_940_ = v___x_1019_;
goto v___jp_937_;
}
v___jp_1020_:
{
lean_object* v___x_1041_; lean_object* v_a_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1041_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v___y_1021_);
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1044_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v___y_1039_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_io_mono_nanos_now();
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1023_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
v___x_1046_ = lean_apply_12(v___y_1034_, v___y_1032_, v___y_1033_, v___y_1023_, v___y_1027_, v___y_1022_, v___y_1028_, v___y_1024_, v___y_1038_, v___y_1025_, v___y_1031_, v___y_1021_, lean_box(0));
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
v___y_987_ = v___y_1021_;
v___y_988_ = v___y_1022_;
v___y_989_ = v___y_1024_;
v___y_990_ = v___y_1023_;
v___y_991_ = v___y_1025_;
v___y_992_ = v_a_1042_;
v___y_993_ = v___y_1026_;
v___y_994_ = v___y_1027_;
v___y_995_ = v___y_1028_;
v___y_996_ = v___y_1030_;
v___y_997_ = v___y_1029_;
v___y_998_ = v___y_1031_;
v___y_999_ = v___y_1032_;
v___y_1000_ = v___y_1033_;
v___y_1001_ = v___y_1035_;
v___y_1002_ = v___y_1036_;
v___y_1003_ = v___x_1045_;
v___y_1004_ = v___y_1037_;
v___y_1005_ = v___y_1038_;
v___y_1006_ = v___y_1039_;
v___y_1007_ = v___y_1040_;
v_a_1008_ = v___x_1052_;
goto v___jp_986_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1046_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1046_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 0);
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
v___y_987_ = v___y_1021_;
v___y_988_ = v___y_1022_;
v___y_989_ = v___y_1024_;
v___y_990_ = v___y_1023_;
v___y_991_ = v___y_1025_;
v___y_992_ = v_a_1042_;
v___y_993_ = v___y_1026_;
v___y_994_ = v___y_1027_;
v___y_995_ = v___y_1028_;
v___y_996_ = v___y_1030_;
v___y_997_ = v___y_1029_;
v___y_998_ = v___y_1031_;
v___y_999_ = v___y_1032_;
v___y_1000_ = v___y_1033_;
v___y_1001_ = v___y_1035_;
v___y_1002_ = v___y_1036_;
v___y_1003_ = v___x_1045_;
v___y_1004_ = v___y_1037_;
v___y_1005_ = v___y_1038_;
v___y_1006_ = v___y_1039_;
v___y_1007_ = v___y_1040_;
v_a_1008_ = v___x_1060_;
goto v___jp_986_;
}
}
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1023_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
v___x_1064_ = lean_apply_12(v___y_1034_, v___y_1032_, v___y_1033_, v___y_1023_, v___y_1027_, v___y_1022_, v___y_1028_, v___y_1024_, v___y_1038_, v___y_1025_, v___y_1031_, v___y_1021_, lean_box(0));
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 1);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
v___y_958_ = v___y_1024_;
v___y_959_ = v___x_1063_;
v___y_960_ = v___y_1023_;
v___y_961_ = v___y_1025_;
v___y_962_ = v_a_1042_;
v___y_963_ = v___y_1026_;
v___y_964_ = v___y_1027_;
v___y_965_ = v___y_1028_;
v___y_966_ = v___y_1030_;
v___y_967_ = v___y_1029_;
v___y_968_ = v___y_1031_;
v___y_969_ = v___y_1032_;
v___y_970_ = v___y_1033_;
v___y_971_ = v___y_1035_;
v___y_972_ = v___y_1036_;
v___y_973_ = v___y_1037_;
v___y_974_ = v___y_1038_;
v___y_975_ = v___y_1039_;
v___y_976_ = v___y_1040_;
v_a_977_ = v___x_1070_;
goto v___jp_955_;
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_a_1073_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1064_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1064_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 0);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
v___y_956_ = v___y_1021_;
v___y_957_ = v___y_1022_;
v___y_958_ = v___y_1024_;
v___y_959_ = v___x_1063_;
v___y_960_ = v___y_1023_;
v___y_961_ = v___y_1025_;
v___y_962_ = v_a_1042_;
v___y_963_ = v___y_1026_;
v___y_964_ = v___y_1027_;
v___y_965_ = v___y_1028_;
v___y_966_ = v___y_1030_;
v___y_967_ = v___y_1029_;
v___y_968_ = v___y_1031_;
v___y_969_ = v___y_1032_;
v___y_970_ = v___y_1033_;
v___y_971_ = v___y_1035_;
v___y_972_ = v___y_1036_;
v___y_973_ = v___y_1037_;
v___y_974_ = v___y_1038_;
v___y_975_ = v___y_1039_;
v___y_976_ = v___y_1040_;
v_a_977_ = v___x_1078_;
goto v___jp_955_;
}
}
}
}
}
v___jp_1081_:
{
lean_object* v___x_1095_; lean_object* v_a_1096_; lean_object* v___x_1097_; 
v___x_1095_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_1084_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_1096_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v_a_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; uint8_t v___x_1099_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v___x_1099_ = lean_unbox(v_a_1098_);
if (v___x_1099_ == 0)
{
uint8_t v_shortCircuit_1100_; 
v_shortCircuit_1100_ = lean_ctor_get_uint8(v___y_1082_, sizeof(void*)*3 + 9);
if (v_shortCircuit_1100_ == 0)
{
return v___x_1097_;
}
else
{
lean_object* v___x_1101_; lean_object* v_toCold_1102_; lean_object* v_options_1103_; uint8_t v_hasTrace_1104_; 
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1101_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_toCold_1102_ = lean_ctor_get(v___y_1093_, 0);
v_options_1103_ = lean_ctor_get(v_toCold_1102_, 2);
v_hasTrace_1104_ = lean_ctor_get_uint8(v_options_1103_, sizeof(void*)*1);
if (v_hasTrace_1104_ == 0)
{
lean_object* v_run_x27_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_run_x27_1105_ = lean_ctor_get(v___x_1101_, 1);
lean_inc_ref(v_run_x27_1105_);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
lean_inc(v___y_1090_);
lean_inc_ref(v___y_1089_);
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
v___x_1106_ = lean_apply_12(v_run_x27_1105_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, lean_box(0));
v___x_1107_ = lean_unbox(v_a_1098_);
lean_dec(v_a_1098_);
v___y_938_ = v___y_1083_;
v___y_939_ = v___x_1107_;
v___y_940_ = v___x_1106_;
goto v___jp_937_;
}
else
{
lean_object* v_name_1108_; lean_object* v_run_x27_1109_; lean_object* v_inheritedTraceOptions_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_name_1108_ = lean_ctor_get(v___x_1101_, 0);
v_run_x27_1109_ = lean_ctor_get(v___x_1101_, 1);
v_inheritedTraceOptions_1110_ = lean_ctor_get(v_toCold_1102_, 11);
lean_inc(v_name_1108_);
v___f_1111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1111_, 0, v_name_1108_);
v___x_1112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_1113_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1));
v___x_1114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7);
v___x_1115_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1110_, v_options_1103_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = l_Lean_trace_profiler;
v___x_1117_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_options_1103_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
lean_dec_ref(v___f_1111_);
lean_inc_ref(v_run_x27_1109_);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
lean_inc(v___y_1090_);
lean_inc_ref(v___y_1089_);
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
v___x_1118_ = lean_apply_12(v_run_x27_1109_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, lean_box(0));
v___x_1119_ = lean_unbox(v_a_1098_);
lean_dec(v_a_1098_);
v___y_938_ = v___y_1083_;
v___y_939_ = v___x_1119_;
v___y_940_ = v___x_1118_;
goto v___jp_937_;
}
else
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_unbox(v_a_1098_);
lean_dec(v_a_1098_);
lean_inc_ref(v_run_x27_1109_);
v___y_1021_ = v___y_1094_;
v___y_1022_ = v___y_1088_;
v___y_1023_ = v___y_1086_;
v___y_1024_ = v___y_1090_;
v___y_1025_ = v___y_1092_;
v___y_1026_ = v___x_1115_;
v___y_1027_ = v___y_1087_;
v___y_1028_ = v___y_1089_;
v___y_1029_ = v___y_1083_;
v___y_1030_ = v___x_1120_;
v___y_1031_ = v___y_1093_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v_run_x27_1109_;
v___y_1035_ = v_hasTrace_1104_;
v___y_1036_ = v___x_1112_;
v___y_1037_ = v___x_1113_;
v___y_1038_ = v___y_1091_;
v___y_1039_ = v_options_1103_;
v___y_1040_ = v___f_1111_;
goto v___jp_1020_;
}
}
else
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_unbox(v_a_1098_);
lean_dec(v_a_1098_);
lean_inc_ref(v_run_x27_1109_);
v___y_1021_ = v___y_1094_;
v___y_1022_ = v___y_1088_;
v___y_1023_ = v___y_1086_;
v___y_1024_ = v___y_1090_;
v___y_1025_ = v___y_1092_;
v___y_1026_ = v___x_1115_;
v___y_1027_ = v___y_1087_;
v___y_1028_ = v___y_1089_;
v___y_1029_ = v___y_1083_;
v___y_1030_ = v___x_1121_;
v___y_1031_ = v___y_1093_;
v___y_1032_ = v___y_1084_;
v___y_1033_ = v___y_1085_;
v___y_1034_ = v_run_x27_1109_;
v___y_1035_ = v_hasTrace_1104_;
v___y_1036_ = v___x_1112_;
v___y_1037_ = v___x_1113_;
v___y_1038_ = v___y_1091_;
v___y_1039_ = v_options_1103_;
v___y_1040_ = v___f_1111_;
goto v___jp_1020_;
}
}
}
}
else
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v___x_1097_, 0);
lean_dec(v_unused_1130_);
v___x_1123_ = v___x_1097_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v___x_1097_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_box(v___y_1083_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
return v___x_1097_;
}
}
v___jp_1131_:
{
if (lean_obj_tag(v___y_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1155_; 
v_a_1146_ = lean_ctor_get(v___y_1145_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___y_1145_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1148_ = v___y_1145_;
v_isShared_1149_ = v_isSharedCheck_1155_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___y_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1155_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_unbox(v_a_1146_);
lean_dec(v_a_1146_);
if (v___x_1150_ == 0)
{
lean_del_object(v___x_1148_);
v___y_1082_ = v___y_1139_;
v___y_1083_ = v___y_1141_;
v___y_1084_ = v___y_1136_;
v___y_1085_ = v___y_1134_;
v___y_1086_ = v___y_1137_;
v___y_1087_ = v___y_1142_;
v___y_1088_ = v___y_1135_;
v___y_1089_ = v___y_1144_;
v___y_1090_ = v___y_1132_;
v___y_1091_ = v___y_1143_;
v___y_1092_ = v___y_1138_;
v___y_1093_ = v___y_1140_;
v___y_1094_ = v___y_1133_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_box(v___y_1141_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1151_);
v___x_1153_ = v___x_1148_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
return v___y_1145_;
}
}
v___jp_1156_:
{
lean_object* v___x_1179_; double v___x_1180_; double v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1179_ = lean_io_get_num_heartbeats();
v___x_1180_ = lean_float_of_nat(v___y_1158_);
v___x_1181_ = lean_float_of_nat(v___x_1179_);
v___x_1182_ = lean_box_float(v___x_1180_);
v___x_1183_ = lean_box_float(v___x_1181_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_a_1178_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
lean_inc_ref(v___y_1174_);
lean_inc(v___y_1173_);
v___x_1186_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1173_, v___y_1163_, v___y_1174_, v___y_1159_, v___y_1160_, v___y_1157_, v___y_1164_, v___x_1185_, v___y_1168_, v___y_1165_, v___y_1169_, v___y_1175_, v___y_1166_, v___y_1177_, v___y_1161_, v___y_1176_, v___y_1167_, v___y_1171_, v___y_1162_);
v___y_1132_ = v___y_1161_;
v___y_1133_ = v___y_1162_;
v___y_1134_ = v___y_1165_;
v___y_1135_ = v___y_1166_;
v___y_1136_ = v___y_1168_;
v___y_1137_ = v___y_1169_;
v___y_1138_ = v___y_1167_;
v___y_1139_ = v___y_1170_;
v___y_1140_ = v___y_1171_;
v___y_1141_ = v___y_1172_;
v___y_1142_ = v___y_1175_;
v___y_1143_ = v___y_1176_;
v___y_1144_ = v___y_1177_;
v___y_1145_ = v___x_1186_;
goto v___jp_1131_;
}
v___jp_1187_:
{
lean_object* v___x_1210_; double v___x_1211_; double v___x_1212_; double v___x_1213_; double v___x_1214_; double v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1210_ = lean_io_mono_nanos_now();
v___x_1211_ = lean_float_of_nat(v___y_1207_);
v___x_1212_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0);
v___x_1213_ = lean_float_div(v___x_1211_, v___x_1212_);
v___x_1214_ = lean_float_of_nat(v___x_1210_);
v___x_1215_ = lean_float_div(v___x_1214_, v___x_1212_);
v___x_1216_ = lean_box_float(v___x_1213_);
v___x_1217_ = lean_box_float(v___x_1215_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_a_1209_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
lean_inc_ref(v___y_1204_);
lean_inc(v___y_1203_);
v___x_1220_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1203_, v___y_1193_, v___y_1204_, v___y_1189_, v___y_1190_, v___y_1188_, v___y_1194_, v___x_1219_, v___y_1198_, v___y_1195_, v___y_1199_, v___y_1205_, v___y_1196_, v___y_1208_, v___y_1191_, v___y_1206_, v___y_1197_, v___y_1201_, v___y_1192_);
v___y_1132_ = v___y_1191_;
v___y_1133_ = v___y_1192_;
v___y_1134_ = v___y_1195_;
v___y_1135_ = v___y_1196_;
v___y_1136_ = v___y_1198_;
v___y_1137_ = v___y_1199_;
v___y_1138_ = v___y_1197_;
v___y_1139_ = v___y_1200_;
v___y_1140_ = v___y_1201_;
v___y_1141_ = v___y_1202_;
v___y_1142_ = v___y_1205_;
v___y_1143_ = v___y_1206_;
v___y_1144_ = v___y_1208_;
v___y_1145_ = v___x_1220_;
goto v___jp_1131_;
}
v___jp_1221_:
{
lean_object* v___x_1242_; lean_object* v_a_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1242_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v___y_1227_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1242_);
v___x_1244_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1245_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v___y_1223_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_io_mono_nanos_now();
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1231_);
lean_inc(v___y_1228_);
lean_inc_ref(v___y_1230_);
v___x_1247_ = lean_apply_12(v___y_1240_, v___y_1230_, v___y_1228_, v___y_1231_, v___y_1238_, v___y_1229_, v___y_1241_, v___y_1224_, v___y_1239_, v___y_1232_, v___y_1234_, v___y_1227_, lean_box(0));
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 1);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
v___y_1188_ = v_a_1243_;
v___y_1189_ = v___y_1223_;
v___y_1190_ = v___y_1222_;
v___y_1191_ = v___y_1224_;
v___y_1192_ = v___y_1227_;
v___y_1193_ = v___y_1226_;
v___y_1194_ = v___y_1225_;
v___y_1195_ = v___y_1228_;
v___y_1196_ = v___y_1229_;
v___y_1197_ = v___y_1232_;
v___y_1198_ = v___y_1230_;
v___y_1199_ = v___y_1231_;
v___y_1200_ = v___y_1233_;
v___y_1201_ = v___y_1234_;
v___y_1202_ = v___y_1235_;
v___y_1203_ = v___y_1237_;
v___y_1204_ = v___y_1236_;
v___y_1205_ = v___y_1238_;
v___y_1206_ = v___y_1239_;
v___y_1207_ = v___x_1246_;
v___y_1208_ = v___y_1241_;
v_a_1209_ = v___x_1253_;
goto v___jp_1187_;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1247_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1247_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 0);
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
v___y_1188_ = v_a_1243_;
v___y_1189_ = v___y_1223_;
v___y_1190_ = v___y_1222_;
v___y_1191_ = v___y_1224_;
v___y_1192_ = v___y_1227_;
v___y_1193_ = v___y_1226_;
v___y_1194_ = v___y_1225_;
v___y_1195_ = v___y_1228_;
v___y_1196_ = v___y_1229_;
v___y_1197_ = v___y_1232_;
v___y_1198_ = v___y_1230_;
v___y_1199_ = v___y_1231_;
v___y_1200_ = v___y_1233_;
v___y_1201_ = v___y_1234_;
v___y_1202_ = v___y_1235_;
v___y_1203_ = v___y_1237_;
v___y_1204_ = v___y_1236_;
v___y_1205_ = v___y_1238_;
v___y_1206_ = v___y_1239_;
v___y_1207_ = v___x_1246_;
v___y_1208_ = v___y_1241_;
v_a_1209_ = v___x_1261_;
goto v___jp_1187_;
}
}
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1231_);
lean_inc(v___y_1228_);
lean_inc_ref(v___y_1230_);
v___x_1265_ = lean_apply_12(v___y_1240_, v___y_1230_, v___y_1228_, v___y_1231_, v___y_1238_, v___y_1229_, v___y_1241_, v___y_1224_, v___y_1239_, v___y_1232_, v___y_1234_, v___y_1227_, lean_box(0));
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v___y_1157_ = v_a_1243_;
v___y_1158_ = v___x_1264_;
v___y_1159_ = v___y_1223_;
v___y_1160_ = v___y_1222_;
v___y_1161_ = v___y_1224_;
v___y_1162_ = v___y_1227_;
v___y_1163_ = v___y_1226_;
v___y_1164_ = v___y_1225_;
v___y_1165_ = v___y_1228_;
v___y_1166_ = v___y_1229_;
v___y_1167_ = v___y_1232_;
v___y_1168_ = v___y_1230_;
v___y_1169_ = v___y_1231_;
v___y_1170_ = v___y_1233_;
v___y_1171_ = v___y_1234_;
v___y_1172_ = v___y_1235_;
v___y_1173_ = v___y_1237_;
v___y_1174_ = v___y_1236_;
v___y_1175_ = v___y_1238_;
v___y_1176_ = v___y_1239_;
v___y_1177_ = v___y_1241_;
v_a_1178_ = v___x_1271_;
goto v___jp_1156_;
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1265_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1265_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 0);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v___y_1157_ = v_a_1243_;
v___y_1158_ = v___x_1264_;
v___y_1159_ = v___y_1223_;
v___y_1160_ = v___y_1222_;
v___y_1161_ = v___y_1224_;
v___y_1162_ = v___y_1227_;
v___y_1163_ = v___y_1226_;
v___y_1164_ = v___y_1225_;
v___y_1165_ = v___y_1228_;
v___y_1166_ = v___y_1229_;
v___y_1167_ = v___y_1232_;
v___y_1168_ = v___y_1230_;
v___y_1169_ = v___y_1231_;
v___y_1170_ = v___y_1233_;
v___y_1171_ = v___y_1234_;
v___y_1172_ = v___y_1235_;
v___y_1173_ = v___y_1237_;
v___y_1174_ = v___y_1236_;
v___y_1175_ = v___y_1238_;
v___y_1176_ = v___y_1239_;
v___y_1177_ = v___y_1241_;
v_a_1178_ = v___x_1279_;
goto v___jp_1156_;
}
}
}
}
}
v___jp_1282_:
{
if (v_fixedInt_1284_ == 0)
{
v___y_1082_ = v___y_1283_;
v___y_1083_ = v___y_1285_;
v___y_1084_ = v___y_1286_;
v___y_1085_ = v___y_1287_;
v___y_1086_ = v___y_1288_;
v___y_1087_ = v___y_1289_;
v___y_1088_ = v___y_1290_;
v___y_1089_ = v___y_1291_;
v___y_1090_ = v___y_1292_;
v___y_1091_ = v___y_1293_;
v___y_1092_ = v___y_1294_;
v___y_1093_ = v___y_1295_;
v___y_1094_ = v___y_1296_;
goto v___jp_1081_;
}
else
{
lean_object* v___x_1297_; lean_object* v_toCold_1298_; lean_object* v_options_1299_; uint8_t v_hasTrace_1300_; 
v___x_1297_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_toCold_1298_ = lean_ctor_get(v___y_1295_, 0);
v_options_1299_ = lean_ctor_get(v_toCold_1298_, 2);
v_hasTrace_1300_ = lean_ctor_get_uint8(v_options_1299_, sizeof(void*)*1);
if (v_hasTrace_1300_ == 0)
{
lean_object* v_run_x27_1301_; lean_object* v___x_1302_; 
v_run_x27_1301_ = lean_ctor_get(v___x_1297_, 1);
lean_inc_ref(v_run_x27_1301_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
lean_inc(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1302_ = lean_apply_12(v_run_x27_1301_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, lean_box(0));
v___y_1132_ = v___y_1292_;
v___y_1133_ = v___y_1296_;
v___y_1134_ = v___y_1287_;
v___y_1135_ = v___y_1290_;
v___y_1136_ = v___y_1286_;
v___y_1137_ = v___y_1288_;
v___y_1138_ = v___y_1294_;
v___y_1139_ = v___y_1283_;
v___y_1140_ = v___y_1295_;
v___y_1141_ = v___y_1285_;
v___y_1142_ = v___y_1289_;
v___y_1143_ = v___y_1293_;
v___y_1144_ = v___y_1291_;
v___y_1145_ = v___x_1302_;
goto v___jp_1131_;
}
else
{
lean_object* v_name_1303_; lean_object* v_run_x27_1304_; lean_object* v_inheritedTraceOptions_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_name_1303_ = lean_ctor_get(v___x_1297_, 0);
v_run_x27_1304_ = lean_ctor_get(v___x_1297_, 1);
v_inheritedTraceOptions_1305_ = lean_ctor_get(v_toCold_1298_, 11);
lean_inc(v_name_1303_);
v___f_1306_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1306_, 0, v_name_1303_);
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_1308_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1));
v___x_1309_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7);
v___x_1310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1305_, v_options_1299_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = l_Lean_trace_profiler;
v___x_1312_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_options_1299_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec_ref(v___f_1306_);
lean_inc_ref(v_run_x27_1304_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
lean_inc(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1313_ = lean_apply_12(v_run_x27_1304_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, lean_box(0));
v___y_1132_ = v___y_1292_;
v___y_1133_ = v___y_1296_;
v___y_1134_ = v___y_1287_;
v___y_1135_ = v___y_1290_;
v___y_1136_ = v___y_1286_;
v___y_1137_ = v___y_1288_;
v___y_1138_ = v___y_1294_;
v___y_1139_ = v___y_1283_;
v___y_1140_ = v___y_1295_;
v___y_1141_ = v___y_1285_;
v___y_1142_ = v___y_1289_;
v___y_1143_ = v___y_1293_;
v___y_1144_ = v___y_1291_;
v___y_1145_ = v___x_1313_;
goto v___jp_1131_;
}
else
{
lean_inc_ref(v_run_x27_1304_);
v___y_1222_ = v___x_1310_;
v___y_1223_ = v_options_1299_;
v___y_1224_ = v___y_1292_;
v___y_1225_ = v___f_1306_;
v___y_1226_ = v_hasTrace_1300_;
v___y_1227_ = v___y_1296_;
v___y_1228_ = v___y_1287_;
v___y_1229_ = v___y_1290_;
v___y_1230_ = v___y_1286_;
v___y_1231_ = v___y_1288_;
v___y_1232_ = v___y_1294_;
v___y_1233_ = v___y_1283_;
v___y_1234_ = v___y_1295_;
v___y_1235_ = v___y_1285_;
v___y_1236_ = v___x_1308_;
v___y_1237_ = v___x_1307_;
v___y_1238_ = v___y_1289_;
v___y_1239_ = v___y_1293_;
v___y_1240_ = v_run_x27_1304_;
v___y_1241_ = v___y_1291_;
goto v___jp_1221_;
}
}
else
{
lean_inc_ref(v_run_x27_1304_);
v___y_1222_ = v___x_1310_;
v___y_1223_ = v_options_1299_;
v___y_1224_ = v___y_1292_;
v___y_1225_ = v___f_1306_;
v___y_1226_ = v_hasTrace_1300_;
v___y_1227_ = v___y_1296_;
v___y_1228_ = v___y_1287_;
v___y_1229_ = v___y_1290_;
v___y_1230_ = v___y_1286_;
v___y_1231_ = v___y_1288_;
v___y_1232_ = v___y_1294_;
v___y_1233_ = v___y_1283_;
v___y_1234_ = v___y_1295_;
v___y_1235_ = v___y_1285_;
v___y_1236_ = v___x_1308_;
v___y_1237_ = v___x_1307_;
v___y_1238_ = v___y_1289_;
v___y_1239_ = v___y_1293_;
v___y_1240_ = v_run_x27_1304_;
v___y_1241_ = v___y_1291_;
goto v___jp_1221_;
}
}
}
}
v___jp_1314_:
{
if (lean_obj_tag(v___y_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1339_; 
v_a_1329_ = lean_ctor_get(v___y_1328_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___y_1328_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1331_ = v___y_1328_;
v_isShared_1332_ = v_isSharedCheck_1339_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___y_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1339_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
uint8_t v___x_1333_; 
v___x_1333_ = lean_unbox(v_a_1329_);
lean_dec(v_a_1329_);
if (v___x_1333_ == 0)
{
uint8_t v_fixedInt_1334_; 
lean_del_object(v___x_1331_);
v_fixedInt_1334_ = lean_ctor_get_uint8(v___y_1320_, sizeof(void*)*3 + 6);
v___y_1283_ = v___y_1320_;
v_fixedInt_1284_ = v_fixedInt_1334_;
v___y_1285_ = v___y_1322_;
v___y_1286_ = v___y_1316_;
v___y_1287_ = v___y_1321_;
v___y_1288_ = v___y_1318_;
v___y_1289_ = v___y_1324_;
v___y_1290_ = v___y_1315_;
v___y_1291_ = v___y_1317_;
v___y_1292_ = v___y_1319_;
v___y_1293_ = v___y_1325_;
v___y_1294_ = v___y_1326_;
v___y_1295_ = v___y_1327_;
v___y_1296_ = v___y_1323_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_box(v___y_1322_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1335_);
v___x_1337_ = v___x_1331_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
else
{
return v___y_1328_;
}
}
v___jp_1340_:
{
lean_object* v___x_1363_; double v___x_1364_; double v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1363_ = lean_io_get_num_heartbeats();
v___x_1364_ = lean_float_of_nat(v___y_1352_);
v___x_1365_ = lean_float_of_nat(v___x_1363_);
v___x_1366_ = lean_box_float(v___x_1364_);
v___x_1367_ = lean_box_float(v___x_1365_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_a_1362_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1349_);
v___x_1370_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1349_, v___y_1356_, v___y_1343_, v___y_1344_, v___y_1347_, v___y_1357_, v___y_1355_, v___x_1369_, v___y_1345_, v___y_1353_, v___y_1348_, v___y_1360_, v___y_1341_, v___y_1342_, v___y_1346_, v___y_1359_, v___y_1358_, v___y_1361_, v___y_1354_);
v___y_1315_ = v___y_1341_;
v___y_1316_ = v___y_1345_;
v___y_1317_ = v___y_1342_;
v___y_1318_ = v___y_1348_;
v___y_1319_ = v___y_1346_;
v___y_1320_ = v___y_1350_;
v___y_1321_ = v___y_1353_;
v___y_1322_ = v___y_1351_;
v___y_1323_ = v___y_1354_;
v___y_1324_ = v___y_1360_;
v___y_1325_ = v___y_1359_;
v___y_1326_ = v___y_1358_;
v___y_1327_ = v___y_1361_;
v___y_1328_ = v___x_1370_;
goto v___jp_1314_;
}
v___jp_1371_:
{
lean_object* v___x_1394_; double v___x_1395_; double v___x_1396_; double v___x_1397_; double v___x_1398_; double v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1394_ = lean_io_mono_nanos_now();
v___x_1395_ = lean_float_of_nat(v___y_1374_);
v___x_1396_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0);
v___x_1397_ = lean_float_div(v___x_1395_, v___x_1396_);
v___x_1398_ = lean_float_of_nat(v___x_1394_);
v___x_1399_ = lean_float_div(v___x_1398_, v___x_1396_);
v___x_1400_ = lean_box_float(v___x_1397_);
v___x_1401_ = lean_box_float(v___x_1399_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_a_1393_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1381_);
v___x_1404_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1381_, v___y_1387_, v___y_1375_, v___y_1376_, v___y_1379_, v___y_1388_, v___y_1386_, v___x_1403_, v___y_1377_, v___y_1384_, v___y_1380_, v___y_1391_, v___y_1372_, v___y_1373_, v___y_1378_, v___y_1390_, v___y_1389_, v___y_1392_, v___y_1385_);
v___y_1315_ = v___y_1372_;
v___y_1316_ = v___y_1377_;
v___y_1317_ = v___y_1373_;
v___y_1318_ = v___y_1380_;
v___y_1319_ = v___y_1378_;
v___y_1320_ = v___y_1382_;
v___y_1321_ = v___y_1384_;
v___y_1322_ = v___y_1383_;
v___y_1323_ = v___y_1385_;
v___y_1324_ = v___y_1391_;
v___y_1325_ = v___y_1390_;
v___y_1326_ = v___y_1389_;
v___y_1327_ = v___y_1392_;
v___y_1328_ = v___x_1404_;
goto v___jp_1314_;
}
v___jp_1405_:
{
lean_object* v___x_1426_; lean_object* v_a_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1426_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v___y_1419_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1429_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v___y_1411_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_io_mono_nanos_now();
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1413_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1409_);
v___x_1431_ = lean_apply_12(v___y_1407_, v___y_1409_, v___y_1418_, v___y_1413_, v___y_1422_, v___y_1406_, v___y_1410_, v___y_1414_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1419_, lean_box(0));
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 1);
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
v___y_1372_ = v___y_1406_;
v___y_1373_ = v___y_1410_;
v___y_1374_ = v___x_1430_;
v___y_1375_ = v___y_1408_;
v___y_1376_ = v___y_1411_;
v___y_1377_ = v___y_1409_;
v___y_1378_ = v___y_1414_;
v___y_1379_ = v___y_1412_;
v___y_1380_ = v___y_1413_;
v___y_1381_ = v___y_1415_;
v___y_1382_ = v___y_1416_;
v___y_1383_ = v___y_1417_;
v___y_1384_ = v___y_1418_;
v___y_1385_ = v___y_1419_;
v___y_1386_ = v___y_1420_;
v___y_1387_ = v___y_1421_;
v___y_1388_ = v_a_1427_;
v___y_1389_ = v___y_1424_;
v___y_1390_ = v___y_1423_;
v___y_1391_ = v___y_1422_;
v___y_1392_ = v___y_1425_;
v_a_1393_ = v___x_1437_;
goto v___jp_1371_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
v_a_1440_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1431_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1431_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 0);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
v___y_1372_ = v___y_1406_;
v___y_1373_ = v___y_1410_;
v___y_1374_ = v___x_1430_;
v___y_1375_ = v___y_1408_;
v___y_1376_ = v___y_1411_;
v___y_1377_ = v___y_1409_;
v___y_1378_ = v___y_1414_;
v___y_1379_ = v___y_1412_;
v___y_1380_ = v___y_1413_;
v___y_1381_ = v___y_1415_;
v___y_1382_ = v___y_1416_;
v___y_1383_ = v___y_1417_;
v___y_1384_ = v___y_1418_;
v___y_1385_ = v___y_1419_;
v___y_1386_ = v___y_1420_;
v___y_1387_ = v___y_1421_;
v___y_1388_ = v_a_1427_;
v___y_1389_ = v___y_1424_;
v___y_1390_ = v___y_1423_;
v___y_1391_ = v___y_1422_;
v___y_1392_ = v___y_1425_;
v_a_1393_ = v___x_1445_;
goto v___jp_1371_;
}
}
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1413_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1409_);
v___x_1449_ = lean_apply_12(v___y_1407_, v___y_1409_, v___y_1418_, v___y_1413_, v___y_1422_, v___y_1406_, v___y_1410_, v___y_1414_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1419_, lean_box(0));
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
v___y_1341_ = v___y_1406_;
v___y_1342_ = v___y_1410_;
v___y_1343_ = v___y_1408_;
v___y_1344_ = v___y_1411_;
v___y_1345_ = v___y_1409_;
v___y_1346_ = v___y_1414_;
v___y_1347_ = v___y_1412_;
v___y_1348_ = v___y_1413_;
v___y_1349_ = v___y_1415_;
v___y_1350_ = v___y_1416_;
v___y_1351_ = v___y_1417_;
v___y_1352_ = v___x_1448_;
v___y_1353_ = v___y_1418_;
v___y_1354_ = v___y_1419_;
v___y_1355_ = v___y_1420_;
v___y_1356_ = v___y_1421_;
v___y_1357_ = v_a_1427_;
v___y_1358_ = v___y_1424_;
v___y_1359_ = v___y_1423_;
v___y_1360_ = v___y_1422_;
v___y_1361_ = v___y_1425_;
v_a_1362_ = v___x_1455_;
goto v___jp_1340_;
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1449_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1449_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 0);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
v___y_1341_ = v___y_1406_;
v___y_1342_ = v___y_1410_;
v___y_1343_ = v___y_1408_;
v___y_1344_ = v___y_1411_;
v___y_1345_ = v___y_1409_;
v___y_1346_ = v___y_1414_;
v___y_1347_ = v___y_1412_;
v___y_1348_ = v___y_1413_;
v___y_1349_ = v___y_1415_;
v___y_1350_ = v___y_1416_;
v___y_1351_ = v___y_1417_;
v___y_1352_ = v___x_1448_;
v___y_1353_ = v___y_1418_;
v___y_1354_ = v___y_1419_;
v___y_1355_ = v___y_1420_;
v___y_1356_ = v___y_1421_;
v___y_1357_ = v_a_1427_;
v___y_1358_ = v___y_1424_;
v___y_1359_ = v___y_1423_;
v___y_1360_ = v___y_1422_;
v___y_1361_ = v___y_1425_;
v_a_1362_ = v___x_1463_;
goto v___jp_1340_;
}
}
}
}
}
v___jp_1466_:
{
if (v_enums_1469_ == 0)
{
v___y_1283_ = v___y_1467_;
v_fixedInt_1284_ = v_fixedInt_1468_;
v___y_1285_ = v___y_1470_;
v___y_1286_ = v___y_1471_;
v___y_1287_ = v___y_1472_;
v___y_1288_ = v___y_1473_;
v___y_1289_ = v___y_1474_;
v___y_1290_ = v___y_1475_;
v___y_1291_ = v___y_1476_;
v___y_1292_ = v___y_1477_;
v___y_1293_ = v___y_1478_;
v___y_1294_ = v___y_1479_;
v___y_1295_ = v___y_1480_;
v___y_1296_ = v___y_1481_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1482_; lean_object* v_toCold_1483_; lean_object* v_options_1484_; uint8_t v_hasTrace_1485_; 
v___x_1482_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_toCold_1483_ = lean_ctor_get(v___y_1480_, 0);
v_options_1484_ = lean_ctor_get(v_toCold_1483_, 2);
v_hasTrace_1485_ = lean_ctor_get_uint8(v_options_1484_, sizeof(void*)*1);
if (v_hasTrace_1485_ == 0)
{
lean_object* v_run_x27_1486_; lean_object* v___x_1487_; 
v_run_x27_1486_ = lean_ctor_get(v___x_1482_, 1);
lean_inc_ref(v_run_x27_1486_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
v___x_1487_ = lean_apply_12(v_run_x27_1486_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, lean_box(0));
v___y_1315_ = v___y_1475_;
v___y_1316_ = v___y_1471_;
v___y_1317_ = v___y_1476_;
v___y_1318_ = v___y_1473_;
v___y_1319_ = v___y_1477_;
v___y_1320_ = v___y_1467_;
v___y_1321_ = v___y_1472_;
v___y_1322_ = v___y_1470_;
v___y_1323_ = v___y_1481_;
v___y_1324_ = v___y_1474_;
v___y_1325_ = v___y_1478_;
v___y_1326_ = v___y_1479_;
v___y_1327_ = v___y_1480_;
v___y_1328_ = v___x_1487_;
goto v___jp_1314_;
}
else
{
lean_object* v_name_1488_; lean_object* v_run_x27_1489_; lean_object* v_inheritedTraceOptions_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_name_1488_ = lean_ctor_get(v___x_1482_, 0);
v_run_x27_1489_ = lean_ctor_get(v___x_1482_, 1);
v_inheritedTraceOptions_1490_ = lean_ctor_get(v_toCold_1483_, 11);
lean_inc(v_name_1488_);
v___f_1491_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1491_, 0, v_name_1488_);
v___x_1492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_1493_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1));
v___x_1494_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7);
v___x_1495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1490_, v_options_1484_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = l_Lean_trace_profiler;
v___x_1497_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_options_1484_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
lean_dec_ref(v___f_1491_);
lean_inc_ref(v_run_x27_1489_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc_ref(v___y_1474_);
lean_inc(v___y_1473_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
v___x_1498_ = lean_apply_12(v_run_x27_1489_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, lean_box(0));
v___y_1315_ = v___y_1475_;
v___y_1316_ = v___y_1471_;
v___y_1317_ = v___y_1476_;
v___y_1318_ = v___y_1473_;
v___y_1319_ = v___y_1477_;
v___y_1320_ = v___y_1467_;
v___y_1321_ = v___y_1472_;
v___y_1322_ = v___y_1470_;
v___y_1323_ = v___y_1481_;
v___y_1324_ = v___y_1474_;
v___y_1325_ = v___y_1478_;
v___y_1326_ = v___y_1479_;
v___y_1327_ = v___y_1480_;
v___y_1328_ = v___x_1498_;
goto v___jp_1314_;
}
else
{
lean_inc_ref(v_run_x27_1489_);
v___y_1406_ = v___y_1475_;
v___y_1407_ = v_run_x27_1489_;
v___y_1408_ = v___x_1493_;
v___y_1409_ = v___y_1471_;
v___y_1410_ = v___y_1476_;
v___y_1411_ = v_options_1484_;
v___y_1412_ = v___x_1495_;
v___y_1413_ = v___y_1473_;
v___y_1414_ = v___y_1477_;
v___y_1415_ = v___x_1492_;
v___y_1416_ = v___y_1467_;
v___y_1417_ = v___y_1470_;
v___y_1418_ = v___y_1472_;
v___y_1419_ = v___y_1481_;
v___y_1420_ = v___f_1491_;
v___y_1421_ = v_hasTrace_1485_;
v___y_1422_ = v___y_1474_;
v___y_1423_ = v___y_1478_;
v___y_1424_ = v___y_1479_;
v___y_1425_ = v___y_1480_;
goto v___jp_1405_;
}
}
else
{
lean_inc_ref(v_run_x27_1489_);
v___y_1406_ = v___y_1475_;
v___y_1407_ = v_run_x27_1489_;
v___y_1408_ = v___x_1493_;
v___y_1409_ = v___y_1471_;
v___y_1410_ = v___y_1476_;
v___y_1411_ = v_options_1484_;
v___y_1412_ = v___x_1495_;
v___y_1413_ = v___y_1473_;
v___y_1414_ = v___y_1477_;
v___y_1415_ = v___x_1492_;
v___y_1416_ = v___y_1467_;
v___y_1417_ = v___y_1470_;
v___y_1418_ = v___y_1472_;
v___y_1419_ = v___y_1481_;
v___y_1420_ = v___f_1491_;
v___y_1421_ = v_hasTrace_1485_;
v___y_1422_ = v___y_1474_;
v___y_1423_ = v___y_1478_;
v___y_1424_ = v___y_1479_;
v___y_1425_ = v___y_1480_;
goto v___jp_1405_;
}
}
}
}
v___jp_1499_:
{
if (lean_obj_tag(v___y_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1525_; 
v_a_1514_ = lean_ctor_get(v___y_1513_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___y_1513_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1516_ = v___y_1513_;
v_isShared_1517_ = v_isSharedCheck_1525_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___y_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1525_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_unbox(v_a_1514_);
lean_dec(v_a_1514_);
if (v___x_1518_ == 0)
{
uint8_t v_fixedInt_1519_; uint8_t v_enums_1520_; 
lean_del_object(v___x_1516_);
v_fixedInt_1519_ = lean_ctor_get_uint8(v___y_1506_, sizeof(void*)*3 + 6);
v_enums_1520_ = lean_ctor_get_uint8(v___y_1506_, sizeof(void*)*3 + 7);
v___y_1467_ = v___y_1506_;
v_fixedInt_1468_ = v_fixedInt_1519_;
v_enums_1469_ = v_enums_1520_;
v___y_1470_ = v___y_1507_;
v___y_1471_ = v___y_1503_;
v___y_1472_ = v___y_1512_;
v___y_1473_ = v___y_1502_;
v___y_1474_ = v___y_1509_;
v___y_1475_ = v___y_1500_;
v___y_1476_ = v___y_1508_;
v___y_1477_ = v___y_1510_;
v___y_1478_ = v___y_1511_;
v___y_1479_ = v___y_1501_;
v___y_1480_ = v___y_1504_;
v___y_1481_ = v___y_1505_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_box(v___y_1507_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1521_);
v___x_1523_ = v___x_1516_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
return v___y_1513_;
}
}
v___jp_1526_:
{
lean_object* v___x_1549_; double v___x_1550_; double v___x_1551_; double v___x_1552_; double v___x_1553_; double v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1549_ = lean_io_mono_nanos_now();
v___x_1550_ = lean_float_of_nat(v___y_1533_);
v___x_1551_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0);
v___x_1552_ = lean_float_div(v___x_1550_, v___x_1551_);
v___x_1553_ = lean_float_of_nat(v___x_1549_);
v___x_1554_ = lean_float_div(v___x_1553_, v___x_1551_);
v___x_1555_ = lean_box_float(v___x_1552_);
v___x_1556_ = lean_box_float(v___x_1554_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_a_1548_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
lean_inc_ref(v___y_1527_);
lean_inc(v___y_1541_);
v___x_1559_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1541_, v___y_1534_, v___y_1527_, v___y_1530_, v___y_1528_, v___y_1529_, v___y_1542_, v___x_1558_, v___y_1538_, v___y_1547_, v___y_1535_, v___y_1544_, v___y_1532_, v___y_1543_, v___y_1545_, v___y_1546_, v___y_1531_, v___y_1537_, v___y_1536_);
v___y_1500_ = v___y_1532_;
v___y_1501_ = v___y_1531_;
v___y_1502_ = v___y_1535_;
v___y_1503_ = v___y_1538_;
v___y_1504_ = v___y_1537_;
v___y_1505_ = v___y_1536_;
v___y_1506_ = v___y_1539_;
v___y_1507_ = v___y_1540_;
v___y_1508_ = v___y_1543_;
v___y_1509_ = v___y_1544_;
v___y_1510_ = v___y_1545_;
v___y_1511_ = v___y_1546_;
v___y_1512_ = v___y_1547_;
v___y_1513_ = v___x_1559_;
goto v___jp_1499_;
}
v___jp_1560_:
{
lean_object* v___x_1583_; double v___x_1584_; double v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1583_ = lean_io_get_num_heartbeats();
v___x_1584_ = lean_float_of_nat(v___y_1569_);
v___x_1585_ = lean_float_of_nat(v___x_1583_);
v___x_1586_ = lean_box_float(v___x_1584_);
v___x_1587_ = lean_box_float(v___x_1585_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_a_1582_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
lean_inc_ref(v___y_1561_);
lean_inc(v___y_1575_);
v___x_1590_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1575_, v___y_1567_, v___y_1561_, v___y_1564_, v___y_1562_, v___y_1563_, v___y_1576_, v___x_1589_, v___y_1572_, v___y_1581_, v___y_1568_, v___y_1578_, v___y_1566_, v___y_1577_, v___y_1579_, v___y_1580_, v___y_1565_, v___y_1571_, v___y_1570_);
v___y_1500_ = v___y_1566_;
v___y_1501_ = v___y_1565_;
v___y_1502_ = v___y_1568_;
v___y_1503_ = v___y_1572_;
v___y_1504_ = v___y_1571_;
v___y_1505_ = v___y_1570_;
v___y_1506_ = v___y_1573_;
v___y_1507_ = v___y_1574_;
v___y_1508_ = v___y_1577_;
v___y_1509_ = v___y_1578_;
v___y_1510_ = v___y_1579_;
v___y_1511_ = v___y_1580_;
v___y_1512_ = v___y_1581_;
v___y_1513_ = v___x_1590_;
goto v___jp_1499_;
}
v___jp_1591_:
{
lean_object* v___x_1612_; lean_object* v_a_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1612_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v___y_1602_);
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref(v___x_1612_);
v___x_1614_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1615_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v___y_1594_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_io_mono_nanos_now();
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1610_);
lean_inc(v___y_1609_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1595_);
lean_inc_ref(v___y_1608_);
lean_inc(v___y_1598_);
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1600_);
v___x_1617_ = lean_apply_12(v___y_1599_, v___y_1600_, v___y_1611_, v___y_1598_, v___y_1608_, v___y_1595_, v___y_1607_, v___y_1609_, v___y_1610_, v___y_1596_, v___y_1601_, v___y_1602_, lean_box(0));
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set_tag(v___x_1620_, 1);
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
v___y_1527_ = v___y_1593_;
v___y_1528_ = v___y_1592_;
v___y_1529_ = v_a_1613_;
v___y_1530_ = v___y_1594_;
v___y_1531_ = v___y_1596_;
v___y_1532_ = v___y_1595_;
v___y_1533_ = v___x_1616_;
v___y_1534_ = v___y_1597_;
v___y_1535_ = v___y_1598_;
v___y_1536_ = v___y_1602_;
v___y_1537_ = v___y_1601_;
v___y_1538_ = v___y_1600_;
v___y_1539_ = v___y_1603_;
v___y_1540_ = v___y_1604_;
v___y_1541_ = v___y_1606_;
v___y_1542_ = v___y_1605_;
v___y_1543_ = v___y_1607_;
v___y_1544_ = v___y_1608_;
v___y_1545_ = v___y_1609_;
v___y_1546_ = v___y_1610_;
v___y_1547_ = v___y_1611_;
v_a_1548_ = v___x_1623_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1617_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1617_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 0);
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
v___y_1527_ = v___y_1593_;
v___y_1528_ = v___y_1592_;
v___y_1529_ = v_a_1613_;
v___y_1530_ = v___y_1594_;
v___y_1531_ = v___y_1596_;
v___y_1532_ = v___y_1595_;
v___y_1533_ = v___x_1616_;
v___y_1534_ = v___y_1597_;
v___y_1535_ = v___y_1598_;
v___y_1536_ = v___y_1602_;
v___y_1537_ = v___y_1601_;
v___y_1538_ = v___y_1600_;
v___y_1539_ = v___y_1603_;
v___y_1540_ = v___y_1604_;
v___y_1541_ = v___y_1606_;
v___y_1542_ = v___y_1605_;
v___y_1543_ = v___y_1607_;
v___y_1544_ = v___y_1608_;
v___y_1545_ = v___y_1609_;
v___y_1546_ = v___y_1610_;
v___y_1547_ = v___y_1611_;
v_a_1548_ = v___x_1631_;
goto v___jp_1526_;
}
}
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1610_);
lean_inc(v___y_1609_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1595_);
lean_inc_ref(v___y_1608_);
lean_inc(v___y_1598_);
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1600_);
v___x_1635_ = lean_apply_12(v___y_1599_, v___y_1600_, v___y_1611_, v___y_1598_, v___y_1608_, v___y_1595_, v___y_1607_, v___y_1609_, v___y_1610_, v___y_1596_, v___y_1601_, v___y_1602_, lean_box(0));
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set_tag(v___x_1638_, 1);
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
v___y_1561_ = v___y_1593_;
v___y_1562_ = v___y_1592_;
v___y_1563_ = v_a_1613_;
v___y_1564_ = v___y_1594_;
v___y_1565_ = v___y_1596_;
v___y_1566_ = v___y_1595_;
v___y_1567_ = v___y_1597_;
v___y_1568_ = v___y_1598_;
v___y_1569_ = v___x_1634_;
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___y_1601_;
v___y_1572_ = v___y_1600_;
v___y_1573_ = v___y_1603_;
v___y_1574_ = v___y_1604_;
v___y_1575_ = v___y_1606_;
v___y_1576_ = v___y_1605_;
v___y_1577_ = v___y_1607_;
v___y_1578_ = v___y_1608_;
v___y_1579_ = v___y_1609_;
v___y_1580_ = v___y_1610_;
v___y_1581_ = v___y_1611_;
v_a_1582_ = v___x_1641_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_a_1644_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1635_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1635_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 0);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
v___y_1561_ = v___y_1593_;
v___y_1562_ = v___y_1592_;
v___y_1563_ = v_a_1613_;
v___y_1564_ = v___y_1594_;
v___y_1565_ = v___y_1596_;
v___y_1566_ = v___y_1595_;
v___y_1567_ = v___y_1597_;
v___y_1568_ = v___y_1598_;
v___y_1569_ = v___x_1634_;
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___y_1601_;
v___y_1572_ = v___y_1600_;
v___y_1573_ = v___y_1603_;
v___y_1574_ = v___y_1604_;
v___y_1575_ = v___y_1606_;
v___y_1576_ = v___y_1605_;
v___y_1577_ = v___y_1607_;
v___y_1578_ = v___y_1608_;
v___y_1579_ = v___y_1609_;
v___y_1580_ = v___y_1610_;
v___y_1581_ = v___y_1611_;
v_a_1582_ = v___x_1649_;
goto v___jp_1560_;
}
}
}
}
}
v___jp_1652_:
{
if (lean_obj_tag(v___y_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1696_; 
v_a_1666_ = lean_ctor_get(v___y_1665_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___y_1665_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1668_ = v___y_1665_;
v_isShared_1669_ = v_isSharedCheck_1696_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___y_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1696_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint8_t v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = 1;
v___x_1671_ = lean_unbox(v_a_1666_);
lean_dec(v_a_1666_);
if (v___x_1671_ == 0)
{
uint8_t v_structures_1672_; 
lean_del_object(v___x_1668_);
v_structures_1672_ = lean_ctor_get_uint8(v___y_1663_, sizeof(void*)*3 + 5);
if (v_structures_1672_ == 0)
{
uint8_t v_fixedInt_1673_; uint8_t v_enums_1674_; 
v_fixedInt_1673_ = lean_ctor_get_uint8(v___y_1663_, sizeof(void*)*3 + 6);
v_enums_1674_ = lean_ctor_get_uint8(v___y_1663_, sizeof(void*)*3 + 7);
v___y_1467_ = v___y_1663_;
v_fixedInt_1468_ = v_fixedInt_1673_;
v_enums_1469_ = v_enums_1674_;
v___y_1470_ = v___x_1670_;
v___y_1471_ = v___y_1662_;
v___y_1472_ = v___y_1664_;
v___y_1473_ = v___y_1658_;
v___y_1474_ = v___y_1654_;
v___y_1475_ = v___y_1656_;
v___y_1476_ = v___y_1653_;
v___y_1477_ = v___y_1657_;
v___y_1478_ = v___y_1659_;
v___y_1479_ = v___y_1655_;
v___y_1480_ = v___y_1661_;
v___y_1481_ = v___y_1660_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1675_; lean_object* v_toCold_1676_; lean_object* v_options_1677_; uint8_t v_hasTrace_1678_; 
v___x_1675_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_toCold_1676_ = lean_ctor_get(v___y_1661_, 0);
v_options_1677_ = lean_ctor_get(v_toCold_1676_, 2);
v_hasTrace_1678_ = lean_ctor_get_uint8(v_options_1677_, sizeof(void*)*1);
if (v_hasTrace_1678_ == 0)
{
lean_object* v_run_x27_1679_; lean_object* v___x_1680_; 
v_run_x27_1679_ = lean_ctor_get(v___x_1675_, 1);
lean_inc_ref(v_run_x27_1679_);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1661_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1658_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1662_);
v___x_1680_ = lean_apply_12(v_run_x27_1679_, v___y_1662_, v___y_1664_, v___y_1658_, v___y_1654_, v___y_1656_, v___y_1653_, v___y_1657_, v___y_1659_, v___y_1655_, v___y_1661_, v___y_1660_, lean_box(0));
v___y_1500_ = v___y_1656_;
v___y_1501_ = v___y_1655_;
v___y_1502_ = v___y_1658_;
v___y_1503_ = v___y_1662_;
v___y_1504_ = v___y_1661_;
v___y_1505_ = v___y_1660_;
v___y_1506_ = v___y_1663_;
v___y_1507_ = v___x_1670_;
v___y_1508_ = v___y_1653_;
v___y_1509_ = v___y_1654_;
v___y_1510_ = v___y_1657_;
v___y_1511_ = v___y_1659_;
v___y_1512_ = v___y_1664_;
v___y_1513_ = v___x_1680_;
goto v___jp_1499_;
}
else
{
lean_object* v_name_1681_; lean_object* v_run_x27_1682_; lean_object* v_inheritedTraceOptions_1683_; lean_object* v___f_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_name_1681_ = lean_ctor_get(v___x_1675_, 0);
v_run_x27_1682_ = lean_ctor_get(v___x_1675_, 1);
v_inheritedTraceOptions_1683_ = lean_ctor_get(v_toCold_1676_, 11);
lean_inc(v_name_1681_);
v___f_1684_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1684_, 0, v_name_1681_);
v___x_1685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_1686_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1));
v___x_1687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7);
v___x_1688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1683_, v_options_1677_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = l_Lean_trace_profiler;
v___x_1690_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_options_1677_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref(v___f_1684_);
lean_inc_ref(v_run_x27_1682_);
lean_inc(v___y_1660_);
lean_inc_ref(v___y_1661_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1659_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1653_);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1658_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1662_);
v___x_1691_ = lean_apply_12(v_run_x27_1682_, v___y_1662_, v___y_1664_, v___y_1658_, v___y_1654_, v___y_1656_, v___y_1653_, v___y_1657_, v___y_1659_, v___y_1655_, v___y_1661_, v___y_1660_, lean_box(0));
v___y_1500_ = v___y_1656_;
v___y_1501_ = v___y_1655_;
v___y_1502_ = v___y_1658_;
v___y_1503_ = v___y_1662_;
v___y_1504_ = v___y_1661_;
v___y_1505_ = v___y_1660_;
v___y_1506_ = v___y_1663_;
v___y_1507_ = v___x_1670_;
v___y_1508_ = v___y_1653_;
v___y_1509_ = v___y_1654_;
v___y_1510_ = v___y_1657_;
v___y_1511_ = v___y_1659_;
v___y_1512_ = v___y_1664_;
v___y_1513_ = v___x_1691_;
goto v___jp_1499_;
}
else
{
lean_inc_ref(v_run_x27_1682_);
v___y_1592_ = v___x_1688_;
v___y_1593_ = v___x_1686_;
v___y_1594_ = v_options_1677_;
v___y_1595_ = v___y_1656_;
v___y_1596_ = v___y_1655_;
v___y_1597_ = v_hasTrace_1678_;
v___y_1598_ = v___y_1658_;
v___y_1599_ = v_run_x27_1682_;
v___y_1600_ = v___y_1662_;
v___y_1601_ = v___y_1661_;
v___y_1602_ = v___y_1660_;
v___y_1603_ = v___y_1663_;
v___y_1604_ = v___x_1670_;
v___y_1605_ = v___f_1684_;
v___y_1606_ = v___x_1685_;
v___y_1607_ = v___y_1653_;
v___y_1608_ = v___y_1654_;
v___y_1609_ = v___y_1657_;
v___y_1610_ = v___y_1659_;
v___y_1611_ = v___y_1664_;
goto v___jp_1591_;
}
}
else
{
lean_inc_ref(v_run_x27_1682_);
v___y_1592_ = v___x_1688_;
v___y_1593_ = v___x_1686_;
v___y_1594_ = v_options_1677_;
v___y_1595_ = v___y_1656_;
v___y_1596_ = v___y_1655_;
v___y_1597_ = v_hasTrace_1678_;
v___y_1598_ = v___y_1658_;
v___y_1599_ = v_run_x27_1682_;
v___y_1600_ = v___y_1662_;
v___y_1601_ = v___y_1661_;
v___y_1602_ = v___y_1660_;
v___y_1603_ = v___y_1663_;
v___y_1604_ = v___x_1670_;
v___y_1605_ = v___f_1684_;
v___y_1606_ = v___x_1685_;
v___y_1607_ = v___y_1653_;
v___y_1608_ = v___y_1654_;
v___y_1609_ = v___y_1657_;
v___y_1610_ = v___y_1659_;
v___y_1611_ = v___y_1664_;
goto v___jp_1591_;
}
}
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_box(v___x_1670_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1692_);
v___x_1694_ = v___x_1668_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
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
return v___y_1665_;
}
}
v___jp_1697_:
{
lean_object* v___x_1719_; double v___x_1720_; double v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1719_ = lean_io_get_num_heartbeats();
v___x_1720_ = lean_float_of_nat(v___y_1706_);
v___x_1721_ = lean_float_of_nat(v___x_1719_);
v___x_1722_ = lean_box_float(v___x_1720_);
v___x_1723_ = lean_box_float(v___x_1721_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1722_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_a_1718_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
lean_inc_ref(v___y_1716_);
lean_inc(v___y_1714_);
v___x_1726_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1714_, v___y_1707_, v___y_1716_, v___y_1715_, v___y_1712_, v___y_1709_, v___y_1700_, v___x_1725_, v___y_1704_, v___y_1717_, v___y_1701_, v___y_1710_, v___y_1699_, v___y_1708_, v___y_1711_, v___y_1713_, v___y_1698_, v___y_1703_, v___y_1702_);
v___y_1653_ = v___y_1708_;
v___y_1654_ = v___y_1710_;
v___y_1655_ = v___y_1698_;
v___y_1656_ = v___y_1699_;
v___y_1657_ = v___y_1711_;
v___y_1658_ = v___y_1701_;
v___y_1659_ = v___y_1713_;
v___y_1660_ = v___y_1702_;
v___y_1661_ = v___y_1703_;
v___y_1662_ = v___y_1704_;
v___y_1663_ = v___y_1705_;
v___y_1664_ = v___y_1717_;
v___y_1665_ = v___x_1726_;
goto v___jp_1652_;
}
v___jp_1727_:
{
lean_object* v___x_1749_; double v___x_1750_; double v___x_1751_; double v___x_1752_; double v___x_1753_; double v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1749_ = lean_io_mono_nanos_now();
v___x_1750_ = lean_float_of_nat(v___y_1740_);
v___x_1751_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0);
v___x_1752_ = lean_float_div(v___x_1750_, v___x_1751_);
v___x_1753_ = lean_float_of_nat(v___x_1749_);
v___x_1754_ = lean_float_div(v___x_1753_, v___x_1751_);
v___x_1755_ = lean_box_float(v___x_1752_);
v___x_1756_ = lean_box_float(v___x_1754_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_a_1748_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
lean_inc_ref(v___y_1746_);
lean_inc(v___y_1744_);
v___x_1759_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1744_, v___y_1736_, v___y_1746_, v___y_1745_, v___y_1742_, v___y_1738_, v___y_1730_, v___x_1758_, v___y_1734_, v___y_1747_, v___y_1731_, v___y_1739_, v___y_1729_, v___y_1737_, v___y_1741_, v___y_1743_, v___y_1728_, v___y_1733_, v___y_1732_);
v___y_1653_ = v___y_1737_;
v___y_1654_ = v___y_1739_;
v___y_1655_ = v___y_1728_;
v___y_1656_ = v___y_1729_;
v___y_1657_ = v___y_1741_;
v___y_1658_ = v___y_1731_;
v___y_1659_ = v___y_1743_;
v___y_1660_ = v___y_1732_;
v___y_1661_ = v___y_1733_;
v___y_1662_ = v___y_1734_;
v___y_1663_ = v___y_1735_;
v___y_1664_ = v___y_1747_;
v___y_1665_ = v___x_1759_;
goto v___jp_1652_;
}
v___jp_1760_:
{
lean_object* v___x_1780_; lean_object* v_a_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1780_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v___y_1767_);
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1783_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v___y_1777_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_io_mono_nanos_now();
lean_inc(v___y_1767_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1775_);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1770_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1772_);
lean_inc(v___y_1764_);
lean_inc(v___y_1779_);
lean_inc_ref(v___y_1765_);
v___x_1785_ = lean_apply_12(v___y_1771_, v___y_1765_, v___y_1779_, v___y_1764_, v___y_1772_, v___y_1761_, v___y_1770_, v___y_1774_, v___y_1775_, v___y_1762_, v___y_1766_, v___y_1767_, lean_box(0));
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 1);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
v___y_1728_ = v___y_1762_;
v___y_1729_ = v___y_1761_;
v___y_1730_ = v___y_1763_;
v___y_1731_ = v___y_1764_;
v___y_1732_ = v___y_1767_;
v___y_1733_ = v___y_1766_;
v___y_1734_ = v___y_1765_;
v___y_1735_ = v___y_1768_;
v___y_1736_ = v___y_1769_;
v___y_1737_ = v___y_1770_;
v___y_1738_ = v_a_1781_;
v___y_1739_ = v___y_1772_;
v___y_1740_ = v___x_1784_;
v___y_1741_ = v___y_1774_;
v___y_1742_ = v___y_1773_;
v___y_1743_ = v___y_1775_;
v___y_1744_ = v___y_1776_;
v___y_1745_ = v___y_1777_;
v___y_1746_ = v___y_1778_;
v___y_1747_ = v___y_1779_;
v_a_1748_ = v___x_1791_;
goto v___jp_1727_;
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_a_1794_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1785_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1785_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 0);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
v___y_1728_ = v___y_1762_;
v___y_1729_ = v___y_1761_;
v___y_1730_ = v___y_1763_;
v___y_1731_ = v___y_1764_;
v___y_1732_ = v___y_1767_;
v___y_1733_ = v___y_1766_;
v___y_1734_ = v___y_1765_;
v___y_1735_ = v___y_1768_;
v___y_1736_ = v___y_1769_;
v___y_1737_ = v___y_1770_;
v___y_1738_ = v_a_1781_;
v___y_1739_ = v___y_1772_;
v___y_1740_ = v___x_1784_;
v___y_1741_ = v___y_1774_;
v___y_1742_ = v___y_1773_;
v___y_1743_ = v___y_1775_;
v___y_1744_ = v___y_1776_;
v___y_1745_ = v___y_1777_;
v___y_1746_ = v___y_1778_;
v___y_1747_ = v___y_1779_;
v_a_1748_ = v___x_1799_;
goto v___jp_1727_;
}
}
}
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1767_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1775_);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1770_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1772_);
lean_inc(v___y_1764_);
lean_inc(v___y_1779_);
lean_inc_ref(v___y_1765_);
v___x_1803_ = lean_apply_12(v___y_1771_, v___y_1765_, v___y_1779_, v___y_1764_, v___y_1772_, v___y_1761_, v___y_1770_, v___y_1774_, v___y_1775_, v___y_1762_, v___y_1766_, v___y_1767_, lean_box(0));
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set_tag(v___x_1806_, 1);
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
v___y_1698_ = v___y_1762_;
v___y_1699_ = v___y_1761_;
v___y_1700_ = v___y_1763_;
v___y_1701_ = v___y_1764_;
v___y_1702_ = v___y_1767_;
v___y_1703_ = v___y_1766_;
v___y_1704_ = v___y_1765_;
v___y_1705_ = v___y_1768_;
v___y_1706_ = v___x_1802_;
v___y_1707_ = v___y_1769_;
v___y_1708_ = v___y_1770_;
v___y_1709_ = v_a_1781_;
v___y_1710_ = v___y_1772_;
v___y_1711_ = v___y_1774_;
v___y_1712_ = v___y_1773_;
v___y_1713_ = v___y_1775_;
v___y_1714_ = v___y_1776_;
v___y_1715_ = v___y_1777_;
v___y_1716_ = v___y_1778_;
v___y_1717_ = v___y_1779_;
v_a_1718_ = v___x_1809_;
goto v___jp_1697_;
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1803_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1803_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 0);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
v___y_1698_ = v___y_1762_;
v___y_1699_ = v___y_1761_;
v___y_1700_ = v___y_1763_;
v___y_1701_ = v___y_1764_;
v___y_1702_ = v___y_1767_;
v___y_1703_ = v___y_1766_;
v___y_1704_ = v___y_1765_;
v___y_1705_ = v___y_1768_;
v___y_1706_ = v___x_1802_;
v___y_1707_ = v___y_1769_;
v___y_1708_ = v___y_1770_;
v___y_1709_ = v_a_1781_;
v___y_1710_ = v___y_1772_;
v___y_1711_ = v___y_1774_;
v___y_1712_ = v___y_1773_;
v___y_1713_ = v___y_1775_;
v___y_1714_ = v___y_1776_;
v___y_1715_ = v___y_1777_;
v___y_1716_ = v___y_1778_;
v___y_1717_ = v___y_1779_;
v_a_1718_ = v___x_1817_;
goto v___jp_1697_;
}
}
}
}
}
v___jp_1820_:
{
lean_object* v___x_1833_; lean_object* v_toCold_1834_; lean_object* v_options_1835_; uint8_t v_hasTrace_1836_; 
v___x_1833_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v_toCold_1834_ = lean_ctor_get(v___y_1831_, 0);
v_options_1835_ = lean_ctor_get(v_toCold_1834_, 2);
v_hasTrace_1836_ = lean_ctor_get_uint8(v_options_1835_, sizeof(void*)*1);
if (v_hasTrace_1836_ == 0)
{
lean_object* v_run_x27_1837_; lean_object* v___x_1838_; 
v_run_x27_1837_ = lean_ctor_get(v___x_1833_, 1);
lean_inc_ref(v_run_x27_1837_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
v___x_1838_ = lean_apply_12(v_run_x27_1837_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, lean_box(0));
v___y_1653_ = v___y_1827_;
v___y_1654_ = v___y_1825_;
v___y_1655_ = v___y_1830_;
v___y_1656_ = v___y_1826_;
v___y_1657_ = v___y_1828_;
v___y_1658_ = v___y_1824_;
v___y_1659_ = v___y_1829_;
v___y_1660_ = v___y_1832_;
v___y_1661_ = v___y_1831_;
v___y_1662_ = v___y_1822_;
v___y_1663_ = v___y_1821_;
v___y_1664_ = v___y_1823_;
v___y_1665_ = v___x_1838_;
goto v___jp_1652_;
}
else
{
lean_object* v_name_1839_; lean_object* v_run_x27_1840_; lean_object* v_inheritedTraceOptions_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_name_1839_ = lean_ctor_get(v___x_1833_, 0);
v_run_x27_1840_ = lean_ctor_get(v___x_1833_, 1);
v_inheritedTraceOptions_1841_ = lean_ctor_get(v_toCold_1834_, 11);
lean_inc(v_name_1839_);
v___f_1842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1842_, 0, v_name_1839_);
v___x_1843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_1844_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1));
v___x_1845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7);
v___x_1846_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1841_, v_options_1835_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = l_Lean_trace_profiler;
v___x_1848_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_options_1835_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
lean_dec_ref(v___f_1842_);
lean_inc_ref(v_run_x27_1840_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1828_);
lean_inc_ref(v___y_1827_);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
v___x_1849_ = lean_apply_12(v_run_x27_1840_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, lean_box(0));
v___y_1653_ = v___y_1827_;
v___y_1654_ = v___y_1825_;
v___y_1655_ = v___y_1830_;
v___y_1656_ = v___y_1826_;
v___y_1657_ = v___y_1828_;
v___y_1658_ = v___y_1824_;
v___y_1659_ = v___y_1829_;
v___y_1660_ = v___y_1832_;
v___y_1661_ = v___y_1831_;
v___y_1662_ = v___y_1822_;
v___y_1663_ = v___y_1821_;
v___y_1664_ = v___y_1823_;
v___y_1665_ = v___x_1849_;
goto v___jp_1652_;
}
else
{
lean_inc_ref(v_run_x27_1840_);
v___y_1761_ = v___y_1826_;
v___y_1762_ = v___y_1830_;
v___y_1763_ = v___f_1842_;
v___y_1764_ = v___y_1824_;
v___y_1765_ = v___y_1822_;
v___y_1766_ = v___y_1831_;
v___y_1767_ = v___y_1832_;
v___y_1768_ = v___y_1821_;
v___y_1769_ = v_hasTrace_1836_;
v___y_1770_ = v___y_1827_;
v___y_1771_ = v_run_x27_1840_;
v___y_1772_ = v___y_1825_;
v___y_1773_ = v___x_1846_;
v___y_1774_ = v___y_1828_;
v___y_1775_ = v___y_1829_;
v___y_1776_ = v___x_1843_;
v___y_1777_ = v_options_1835_;
v___y_1778_ = v___x_1844_;
v___y_1779_ = v___y_1823_;
goto v___jp_1760_;
}
}
else
{
lean_inc_ref(v_run_x27_1840_);
v___y_1761_ = v___y_1826_;
v___y_1762_ = v___y_1830_;
v___y_1763_ = v___f_1842_;
v___y_1764_ = v___y_1824_;
v___y_1765_ = v___y_1822_;
v___y_1766_ = v___y_1831_;
v___y_1767_ = v___y_1832_;
v___y_1768_ = v___y_1821_;
v___y_1769_ = v_hasTrace_1836_;
v___y_1770_ = v___y_1827_;
v___y_1771_ = v_run_x27_1840_;
v___y_1772_ = v___y_1825_;
v___y_1773_ = v___x_1846_;
v___y_1774_ = v___y_1828_;
v___y_1775_ = v___y_1829_;
v___y_1776_ = v___x_1843_;
v___y_1777_ = v_options_1835_;
v___y_1778_ = v___x_1844_;
v___y_1779_ = v___y_1823_;
goto v___jp_1760_;
}
}
}
v___jp_1850_:
{
if (lean_obj_tag(v___y_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1874_; 
v_a_1865_ = lean_ctor_get(v___y_1864_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___y_1864_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1867_ = v___y_1864_;
v_isShared_1868_ = v_isSharedCheck_1874_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___y_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1874_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_unbox(v_a_1865_);
lean_dec(v_a_1865_);
if (v___x_1869_ == 0)
{
lean_del_object(v___x_1867_);
v___y_1821_ = v___y_1857_;
v___y_1822_ = v___y_1855_;
v___y_1823_ = v___y_1861_;
v___y_1824_ = v___y_1856_;
v___y_1825_ = v___y_1854_;
v___y_1826_ = v___y_1860_;
v___y_1827_ = v___y_1863_;
v___y_1828_ = v___y_1852_;
v___y_1829_ = v___y_1853_;
v___y_1830_ = v___y_1859_;
v___y_1831_ = v___y_1851_;
v___y_1832_ = v___y_1862_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = lean_box(v___y_1858_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1870_);
v___x_1872_ = v___x_1867_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
return v___y_1864_;
}
}
v___jp_1875_:
{
lean_object* v___x_1898_; double v___x_1899_; double v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1898_ = lean_io_get_num_heartbeats();
v___x_1899_ = lean_float_of_nat(v___y_1884_);
v___x_1900_ = lean_float_of_nat(v___x_1898_);
v___x_1901_ = lean_box_float(v___x_1899_);
v___x_1902_ = lean_box_float(v___x_1900_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_a_1897_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
lean_inc_ref(v___y_1880_);
lean_inc(v___y_1883_);
v___x_1905_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1883_, v___y_1891_, v___y_1880_, v___y_1893_, v___y_1881_, v___y_1895_, v___y_1888_, v___x_1904_, v___y_1882_, v___y_1892_, v___y_1885_, v___y_1879_, v___y_1890_, v___y_1896_, v___y_1877_, v___y_1878_, v___y_1889_, v___y_1876_, v___y_1894_);
v___y_1851_ = v___y_1876_;
v___y_1852_ = v___y_1877_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1879_;
v___y_1855_ = v___y_1882_;
v___y_1856_ = v___y_1885_;
v___y_1857_ = v___y_1886_;
v___y_1858_ = v___y_1887_;
v___y_1859_ = v___y_1889_;
v___y_1860_ = v___y_1890_;
v___y_1861_ = v___y_1892_;
v___y_1862_ = v___y_1894_;
v___y_1863_ = v___y_1896_;
v___y_1864_ = v___x_1905_;
goto v___jp_1850_;
}
v___jp_1906_:
{
lean_object* v___x_1929_; double v___x_1930_; double v___x_1931_; double v___x_1932_; double v___x_1933_; double v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1929_ = lean_io_mono_nanos_now();
v___x_1930_ = lean_float_of_nat(v___y_1908_);
v___x_1931_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0);
v___x_1932_ = lean_float_div(v___x_1930_, v___x_1931_);
v___x_1933_ = lean_float_of_nat(v___x_1929_);
v___x_1934_ = lean_float_div(v___x_1933_, v___x_1931_);
v___x_1935_ = lean_box_float(v___x_1932_);
v___x_1936_ = lean_box_float(v___x_1934_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_a_1928_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1915_);
v___x_1939_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___y_1915_, v___y_1922_, v___y_1912_, v___y_1924_, v___y_1913_, v___y_1926_, v___y_1919_, v___x_1938_, v___y_1914_, v___y_1923_, v___y_1916_, v___y_1911_, v___y_1921_, v___y_1927_, v___y_1909_, v___y_1910_, v___y_1920_, v___y_1907_, v___y_1925_);
v___y_1851_ = v___y_1907_;
v___y_1852_ = v___y_1909_;
v___y_1853_ = v___y_1910_;
v___y_1854_ = v___y_1911_;
v___y_1855_ = v___y_1914_;
v___y_1856_ = v___y_1916_;
v___y_1857_ = v___y_1917_;
v___y_1858_ = v___y_1918_;
v___y_1859_ = v___y_1920_;
v___y_1860_ = v___y_1921_;
v___y_1861_ = v___y_1923_;
v___y_1862_ = v___y_1925_;
v___y_1863_ = v___y_1927_;
v___y_1864_ = v___x_1939_;
goto v___jp_1850_;
}
v___jp_1940_:
{
lean_object* v___x_1961_; lean_object* v_a_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1961_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v___y_1959_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1961_);
v___x_1963_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1964_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v___y_1958_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_io_mono_nanos_now();
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1944_);
lean_inc(v___y_1949_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1947_);
v___x_1966_ = lean_apply_12(v___y_1955_, v___y_1947_, v___y_1957_, v___y_1949_, v___y_1944_, v___y_1954_, v___y_1960_, v___y_1942_, v___y_1943_, v___y_1953_, v___y_1941_, v___y_1959_, lean_box(0));
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 1);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v___y_1907_ = v___y_1941_;
v___y_1908_ = v___x_1965_;
v___y_1909_ = v___y_1942_;
v___y_1910_ = v___y_1943_;
v___y_1911_ = v___y_1944_;
v___y_1912_ = v___y_1946_;
v___y_1913_ = v___y_1945_;
v___y_1914_ = v___y_1947_;
v___y_1915_ = v___y_1948_;
v___y_1916_ = v___y_1949_;
v___y_1917_ = v___y_1950_;
v___y_1918_ = v___y_1951_;
v___y_1919_ = v___y_1952_;
v___y_1920_ = v___y_1953_;
v___y_1921_ = v___y_1954_;
v___y_1922_ = v___y_1956_;
v___y_1923_ = v___y_1957_;
v___y_1924_ = v___y_1958_;
v___y_1925_ = v___y_1959_;
v___y_1926_ = v_a_1962_;
v___y_1927_ = v___y_1960_;
v_a_1928_ = v___x_1972_;
goto v___jp_1906_;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1966_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1966_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 0);
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
v___y_1907_ = v___y_1941_;
v___y_1908_ = v___x_1965_;
v___y_1909_ = v___y_1942_;
v___y_1910_ = v___y_1943_;
v___y_1911_ = v___y_1944_;
v___y_1912_ = v___y_1946_;
v___y_1913_ = v___y_1945_;
v___y_1914_ = v___y_1947_;
v___y_1915_ = v___y_1948_;
v___y_1916_ = v___y_1949_;
v___y_1917_ = v___y_1950_;
v___y_1918_ = v___y_1951_;
v___y_1919_ = v___y_1952_;
v___y_1920_ = v___y_1953_;
v___y_1921_ = v___y_1954_;
v___y_1922_ = v___y_1956_;
v___y_1923_ = v___y_1957_;
v___y_1924_ = v___y_1958_;
v___y_1925_ = v___y_1959_;
v___y_1926_ = v_a_1962_;
v___y_1927_ = v___y_1960_;
v_a_1928_ = v___x_1980_;
goto v___jp_1906_;
}
}
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1944_);
lean_inc(v___y_1949_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1947_);
v___x_1984_ = lean_apply_12(v___y_1955_, v___y_1947_, v___y_1957_, v___y_1949_, v___y_1944_, v___y_1954_, v___y_1960_, v___y_1942_, v___y_1943_, v___y_1953_, v___y_1941_, v___y_1959_, lean_box(0));
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 1);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
v___y_1876_ = v___y_1941_;
v___y_1877_ = v___y_1942_;
v___y_1878_ = v___y_1943_;
v___y_1879_ = v___y_1944_;
v___y_1880_ = v___y_1946_;
v___y_1881_ = v___y_1945_;
v___y_1882_ = v___y_1947_;
v___y_1883_ = v___y_1948_;
v___y_1884_ = v___x_1983_;
v___y_1885_ = v___y_1949_;
v___y_1886_ = v___y_1950_;
v___y_1887_ = v___y_1951_;
v___y_1888_ = v___y_1952_;
v___y_1889_ = v___y_1953_;
v___y_1890_ = v___y_1954_;
v___y_1891_ = v___y_1956_;
v___y_1892_ = v___y_1957_;
v___y_1893_ = v___y_1958_;
v___y_1894_ = v___y_1959_;
v___y_1895_ = v_a_1962_;
v___y_1896_ = v___y_1960_;
v_a_1897_ = v___x_1990_;
goto v___jp_1875_;
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
v_a_1993_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1984_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1984_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set_tag(v___x_1995_, 0);
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
v___y_1876_ = v___y_1941_;
v___y_1877_ = v___y_1942_;
v___y_1878_ = v___y_1943_;
v___y_1879_ = v___y_1944_;
v___y_1880_ = v___y_1946_;
v___y_1881_ = v___y_1945_;
v___y_1882_ = v___y_1947_;
v___y_1883_ = v___y_1948_;
v___y_1884_ = v___x_1983_;
v___y_1885_ = v___y_1949_;
v___y_1886_ = v___y_1950_;
v___y_1887_ = v___y_1951_;
v___y_1888_ = v___y_1952_;
v___y_1889_ = v___y_1953_;
v___y_1890_ = v___y_1954_;
v___y_1891_ = v___y_1956_;
v___y_1892_ = v___y_1957_;
v___y_1893_ = v___y_1958_;
v___y_1894_ = v___y_1959_;
v___y_1895_ = v_a_1962_;
v___y_1896_ = v___y_1960_;
v_a_1897_ = v___x_1998_;
goto v___jp_1875_;
}
}
}
}
}
v___jp_2001_:
{
lean_object* v___x_2014_; lean_object* v_toCold_2015_; lean_object* v_options_2016_; lean_object* v_name_2017_; lean_object* v_run_x27_2018_; lean_object* v_inheritedTraceOptions_2019_; uint8_t v_hasTrace_2020_; uint8_t v___x_2021_; 
v___x_2014_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_toCold_2015_ = lean_ctor_get(v___y_2002_, 0);
v_options_2016_ = lean_ctor_get(v_toCold_2015_, 2);
v_name_2017_ = lean_ctor_get(v___x_2014_, 0);
v_run_x27_2018_ = lean_ctor_get(v___x_2014_, 1);
v_inheritedTraceOptions_2019_ = lean_ctor_get(v_toCold_2015_, 11);
v_hasTrace_2020_ = lean_ctor_get_uint8(v_options_2016_, sizeof(void*)*1);
v___x_2021_ = 1;
if (v_hasTrace_2020_ == 0)
{
lean_object* v___x_2022_; 
lean_inc_ref(v_run_x27_2018_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2007_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2006_);
v___x_2022_ = lean_apply_12(v_run_x27_2018_, v___y_2006_, v___y_2011_, v___y_2007_, v___y_2005_, v___y_2010_, v___y_2013_, v___y_2003_, v___y_2004_, v___y_2009_, v___y_2002_, v___y_2012_, lean_box(0));
v___y_1851_ = v___y_2002_;
v___y_1852_ = v___y_2003_;
v___y_1853_ = v___y_2004_;
v___y_1854_ = v___y_2005_;
v___y_1855_ = v___y_2006_;
v___y_1856_ = v___y_2007_;
v___y_1857_ = v___y_2008_;
v___y_1858_ = v___x_2021_;
v___y_1859_ = v___y_2009_;
v___y_1860_ = v___y_2010_;
v___y_1861_ = v___y_2011_;
v___y_1862_ = v___y_2012_;
v___y_1863_ = v___y_2013_;
v___y_1864_ = v___x_2022_;
goto v___jp_1850_;
}
else
{
lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
lean_inc(v_name_2017_);
v___f_2023_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2023_, 0, v_name_2017_);
v___x_2024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_2025_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1));
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7);
v___x_2027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2019_, v_options_2016_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = l_Lean_trace_profiler;
v___x_2029_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_options_2016_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_dec_ref(v___f_2023_);
lean_inc_ref(v_run_x27_2018_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2007_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2006_);
v___x_2030_ = lean_apply_12(v_run_x27_2018_, v___y_2006_, v___y_2011_, v___y_2007_, v___y_2005_, v___y_2010_, v___y_2013_, v___y_2003_, v___y_2004_, v___y_2009_, v___y_2002_, v___y_2012_, lean_box(0));
v___y_1851_ = v___y_2002_;
v___y_1852_ = v___y_2003_;
v___y_1853_ = v___y_2004_;
v___y_1854_ = v___y_2005_;
v___y_1855_ = v___y_2006_;
v___y_1856_ = v___y_2007_;
v___y_1857_ = v___y_2008_;
v___y_1858_ = v___x_2021_;
v___y_1859_ = v___y_2009_;
v___y_1860_ = v___y_2010_;
v___y_1861_ = v___y_2011_;
v___y_1862_ = v___y_2012_;
v___y_1863_ = v___y_2013_;
v___y_1864_ = v___x_2030_;
goto v___jp_1850_;
}
else
{
lean_inc_ref(v_run_x27_2018_);
v___y_1941_ = v___y_2002_;
v___y_1942_ = v___y_2003_;
v___y_1943_ = v___y_2004_;
v___y_1944_ = v___y_2005_;
v___y_1945_ = v___x_2027_;
v___y_1946_ = v___x_2025_;
v___y_1947_ = v___y_2006_;
v___y_1948_ = v___x_2024_;
v___y_1949_ = v___y_2007_;
v___y_1950_ = v___y_2008_;
v___y_1951_ = v___x_2021_;
v___y_1952_ = v___f_2023_;
v___y_1953_ = v___y_2009_;
v___y_1954_ = v___y_2010_;
v___y_1955_ = v_run_x27_2018_;
v___y_1956_ = v_hasTrace_2020_;
v___y_1957_ = v___y_2011_;
v___y_1958_ = v_options_2016_;
v___y_1959_ = v___y_2012_;
v___y_1960_ = v___y_2013_;
goto v___jp_1940_;
}
}
else
{
lean_inc_ref(v_run_x27_2018_);
v___y_1941_ = v___y_2002_;
v___y_1942_ = v___y_2003_;
v___y_1943_ = v___y_2004_;
v___y_1944_ = v___y_2005_;
v___y_1945_ = v___x_2027_;
v___y_1946_ = v___x_2025_;
v___y_1947_ = v___y_2006_;
v___y_1948_ = v___x_2024_;
v___y_1949_ = v___y_2007_;
v___y_1950_ = v___y_2008_;
v___y_1951_ = v___x_2021_;
v___y_1952_ = v___f_2023_;
v___y_1953_ = v___y_2009_;
v___y_1954_ = v___y_2010_;
v___y_1955_ = v_run_x27_2018_;
v___y_1956_ = v_hasTrace_2020_;
v___y_1957_ = v___y_2011_;
v___y_1958_ = v_options_2016_;
v___y_1959_ = v___y_2012_;
v___y_1960_ = v___y_2013_;
goto v___jp_1940_;
}
}
}
v___jp_2031_:
{
lean_object* v_config_2043_; uint8_t v_structures_2044_; 
v_config_2043_ = lean_ctor_get(v___y_2032_, 0);
v_structures_2044_ = lean_ctor_get_uint8(v_config_2043_, sizeof(void*)*3 + 5);
if (v_structures_2044_ == 0)
{
uint8_t v_enums_2045_; 
v_enums_2045_ = lean_ctor_get_uint8(v_config_2043_, sizeof(void*)*3 + 7);
if (v_enums_2045_ == 0)
{
v___y_1821_ = v_config_2043_;
v___y_1822_ = v___y_2032_;
v___y_1823_ = v___y_2033_;
v___y_1824_ = v___y_2034_;
v___y_1825_ = v___y_2035_;
v___y_1826_ = v___y_2036_;
v___y_1827_ = v___y_2037_;
v___y_1828_ = v___y_2038_;
v___y_1829_ = v___y_2039_;
v___y_1830_ = v___y_2040_;
v___y_1831_ = v___y_2041_;
v___y_1832_ = v___y_2042_;
goto v___jp_1820_;
}
else
{
v___y_2002_ = v___y_2041_;
v___y_2003_ = v___y_2038_;
v___y_2004_ = v___y_2039_;
v___y_2005_ = v___y_2035_;
v___y_2006_ = v___y_2032_;
v___y_2007_ = v___y_2034_;
v___y_2008_ = v_config_2043_;
v___y_2009_ = v___y_2040_;
v___y_2010_ = v___y_2036_;
v___y_2011_ = v___y_2033_;
v___y_2012_ = v___y_2042_;
v___y_2013_ = v___y_2037_;
goto v___jp_2001_;
}
}
else
{
v___y_2002_ = v___y_2041_;
v___y_2003_ = v___y_2038_;
v___y_2004_ = v___y_2039_;
v___y_2005_ = v___y_2035_;
v___y_2006_ = v___y_2032_;
v___y_2007_ = v___y_2034_;
v___y_2008_ = v_config_2043_;
v___y_2009_ = v___y_2040_;
v___y_2010_ = v___y_2036_;
v___y_2011_ = v___y_2033_;
v___y_2012_ = v___y_2042_;
v___y_2013_ = v___y_2037_;
goto v___jp_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___boxed(lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline(v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3(lean_object* v_00_u03b1_2076_, lean_object* v_x_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___redArg(v_x_2077_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2091_, lean_object* v_x_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__3(v_00_u03b1_2091_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3(lean_object* v_cls_2106_, lean_object* v_msg_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg(v_cls_2106_, v_msg_2107_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___boxed(lean_object* v_cls_2121_, lean_object* v_msg_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3(v_cls_2121_, v_msg_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2(lean_object* v_oldTraces_2136_, lean_object* v_data_2137_, lean_object* v_ref_2138_, lean_object* v_msg_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___redArg(v_oldTraces_2136_, v_data_2137_, v_ref_2138_, v_msg_2139_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2___boxed(lean_object* v_oldTraces_2153_, lean_object* v_data_2154_, lean_object* v_ref_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2_spec__2(v_oldTraces_2153_, v_data_2154_, v_ref_2155_, v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object* v_____r_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___boxed), 12, 0);
v___x_2184_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_withCaches___redArg(v___x_2183_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object* v_____r_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(v_____r_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(lean_object* v_hyps_x3f_2199_, lean_object* v___f_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
if (lean_obj_tag(v_hyps_x3f_2199_) == 1)
{
lean_object* v_val_2213_; lean_object* v___x_2214_; lean_object* v_caches_2215_; lean_object* v_typeAnalysis_2216_; lean_object* v_target_2217_; uint8_t v_didChange_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2228_; 
v_val_2213_ = lean_ctor_get(v_hyps_x3f_2199_, 0);
v___x_2214_ = lean_st_ref_take(v___y_2202_);
v_caches_2215_ = lean_ctor_get(v___x_2214_, 0);
v_typeAnalysis_2216_ = lean_ctor_get(v___x_2214_, 1);
v_target_2217_ = lean_ctor_get(v___x_2214_, 2);
v_didChange_2218_ = lean_ctor_get_uint8(v___x_2214_, sizeof(void*)*4);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2214_, 3);
lean_dec(v_unused_2229_);
v___x_2220_ = v___x_2214_;
v_isShared_2221_ = v_isSharedCheck_2228_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_target_2217_);
lean_inc(v_typeAnalysis_2216_);
lean_inc(v_caches_2215_);
lean_dec(v___x_2214_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2228_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2222_ = lean_box(0);
lean_inc(v_val_2213_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 3, v_val_2213_);
v___x_2224_ = v___x_2220_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_caches_2215_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_typeAnalysis_2216_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_target_2217_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_val_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*4, v_didChange_2218_);
v___x_2224_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_st_ref_put(v___y_2202_, v___x_2224_);
lean_inc(v___y_2211_);
lean_inc_ref(v___y_2210_);
lean_inc(v___y_2209_);
lean_inc_ref(v___y_2208_);
lean_inc(v___y_2207_);
lean_inc_ref(v___y_2206_);
lean_inc(v___y_2205_);
lean_inc_ref(v___y_2204_);
lean_inc(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
v___x_2226_ = lean_apply_13(v___f_2200_, v___x_2222_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, lean_box(0));
return v___x_2226_;
}
}
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; uint8_t v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v___x_2232_ = lean_unbox(v_a_2231_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_dec_ref_known(v___x_2230_, 1);
v___x_2233_ = lean_box(0);
lean_inc(v___y_2211_);
lean_inc_ref(v___y_2210_);
lean_inc(v___y_2209_);
lean_inc_ref(v___y_2208_);
lean_inc(v___y_2207_);
lean_inc_ref(v___y_2206_);
lean_inc(v___y_2205_);
lean_inc_ref(v___y_2204_);
lean_inc(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
v___x_2234_ = lean_apply_13(v___f_2200_, v___x_2233_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, lean_box(0));
return v___x_2234_;
}
else
{
lean_dec_ref(v___f_2200_);
return v___x_2230_;
}
}
else
{
lean_dec_ref(v___f_2200_);
return v___x_2230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1___boxed(lean_object* v_hyps_x3f_2235_, lean_object* v___f_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_2235_, v___f_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v_hyps_x3f_2235_);
return v_res_2249_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__1));
v___x_2254_ = l_Lean_MessageData_ofFormat(v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2(lean_object* v_x_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___closed__2);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2___boxed(lean_object* v_x_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__2(v_x_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_x_2270_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object* v_hyps_x3f_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_toCold_2299_; lean_object* v_options_2300_; lean_object* v_inheritedTraceOptions_2301_; uint8_t v_hasTrace_2302_; lean_object* v___f_2303_; 
v_toCold_2299_ = lean_ctor_get(v_a_2296_, 0);
v_options_2300_ = lean_ctor_get(v_toCold_2299_, 2);
v_inheritedTraceOptions_2301_ = lean_ctor_get(v_toCold_2299_, 11);
v_hasTrace_2302_ = lean_ctor_get_uint8(v_options_2300_, sizeof(void*)*1);
v___f_2303_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__0));
if (v_hasTrace_2302_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_2286_, v___f_2303_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
return v___x_2304_;
}
else
{
lean_object* v___f_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v_a_2313_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v_a_2328_; 
v___f_2305_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__1));
v___x_2306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__4));
v___x_2307_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__3___redArg___closed__1));
v___x_2308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__7);
v___x_2309_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2301_, v_options_2300_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = l_Lean_trace_profiler;
v___x_2379_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_options_2300_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_2286_, v___f_2303_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
return v___x_2380_;
}
else
{
goto v___jp_2337_;
}
}
else
{
goto v___jp_2337_;
}
v___jp_2310_:
{
lean_object* v___x_2314_; double v___x_2315_; double v___x_2316_; double v___x_2317_; double v___x_2318_; double v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2314_ = lean_io_mono_nanos_now();
v___x_2315_ = lean_float_of_nat(v___y_2312_);
v___x_2316_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline___closed__0);
v___x_2317_ = lean_float_div(v___x_2315_, v___x_2316_);
v___x_2318_ = lean_float_of_nat(v___x_2314_);
v___x_2319_ = lean_float_div(v___x_2318_, v___x_2316_);
v___x_2320_ = lean_box_float(v___x_2317_);
v___x_2321_ = lean_box_float(v___x_2319_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_a_2313_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___x_2306_, v_hasTrace_2302_, v___x_2307_, v_options_2300_, v___x_2309_, v___y_2311_, v___f_2305_, v___x_2323_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
return v___x_2324_;
}
v___jp_2325_:
{
lean_object* v___x_2329_; double v___x_2330_; double v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2329_ = lean_io_get_num_heartbeats();
v___x_2330_ = lean_float_of_nat(v___y_2326_);
v___x_2331_ = lean_float_of_nat(v___x_2329_);
v___x_2332_ = lean_box_float(v___x_2330_);
v___x_2333_ = lean_box_float(v___x_2331_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_a_2328_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__2(v___x_2306_, v_hasTrace_2302_, v___x_2307_, v_options_2300_, v___x_2309_, v___y_2327_, v___f_2305_, v___x_2335_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
return v___x_2336_;
}
v___jp_2337_:
{
lean_object* v___x_2338_; lean_object* v_a_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2338_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__0___redArg(v_a_2297_);
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2341_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_runPipeline_spec__1(v_options_2300_, v___x_2340_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_io_mono_nanos_now();
v___x_2343_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_2286_, v___f_2303_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 1);
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
v___y_2311_ = v_a_2339_;
v___y_2312_ = v___x_2342_;
v_a_2313_ = v___x_2349_;
goto v___jp_2310_;
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2343_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2343_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 0);
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
v___y_2311_ = v_a_2339_;
v___y_2312_ = v___x_2342_;
v_a_2313_ = v___x_2357_;
goto v___jp_2310_;
}
}
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_io_get_num_heartbeats();
v___x_2361_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__1(v_hyps_x3f_2286_, v___f_2303_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set_tag(v___x_2364_, 1);
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
v___y_2326_ = v___x_2360_;
v___y_2327_ = v_a_2339_;
v_a_2328_ = v___x_2367_;
goto v___jp_2325_;
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2361_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2361_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set_tag(v___x_2372_, 0);
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
v___y_2326_ = v___x_2360_;
v___y_2327_ = v_a_2339_;
v_a_2328_ = v___x_2375_;
goto v___jp_2325_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object* v_hyps_x3f_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v_hyps_x3f_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_hyps_x3f_2381_);
return v_res_2394_;
}
}
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
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
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
