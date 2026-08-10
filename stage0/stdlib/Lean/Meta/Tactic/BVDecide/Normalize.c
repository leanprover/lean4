// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize
// Imports: public import Lean.Elab.Tactic.FalseOrByContra public import Lean.Meta.Tactic.BVDecide.Normalize.Basic public import Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow public import Lean.Meta.Tactic.BVDecide.Normalize.Simproc public import Lean.Meta.Tactic.BVDecide.Normalize.Rewrite public import Lean.Meta.Tactic.BVDecide.Normalize.AndFlatten public import Lean.Meta.Tactic.BVDecide.Normalize.EmbeddedConstraint public import Lean.Meta.Tactic.BVDecide.Normalize.AC public import Lean.Meta.Tactic.BVDecide.Normalize.Structures public import Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec public import Lean.Meta.Tactic.BVDecide.Normalize.Enums public import Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis public import Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit public import Lean.Meta.Tactic.BVDecide.Normalize.Reduction public import Lean.Meta.Tactic.BVDecide.Normalize.CollectHyps import Lean.Meta.Sym.Util import Lean.Meta.Sym.Intro import Lean.Meta.Tactic.Grind.Intro
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
lean_object* l_Lean_MVarId_falseOrByContra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_assertAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_trace_profiler;
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
extern lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_intros___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed, .m_arity = 15, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__2_value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__1_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "internalizing grind goal produced multiple goals"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Preprocessing goal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9___boxed(lean_object**);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Running preprocessing pipeline"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_acNf_19_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*2 + 2);
v_andFlattening_20_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_21_ = lean_ctor_get_uint8(v_config_18_, sizeof(void*)*2 + 4);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_Grind_Action_assertAll___redArg(v___y_63_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0___boxed(lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__0(v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_78_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(lean_object* v___x_91_, lean_object* v___f_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_Action_andThen(v___x_91_, v___f_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1___boxed(lean_object* v___x_107_, lean_object* v___f_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___lam__1(v___x_107_, v___f_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_env_130_; lean_object* v___x_131_; lean_object* v_mctx_132_; lean_object* v_lctx_133_; lean_object* v_options_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = lean_st_ref_get(v___y_125_);
v_mctx_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_mctx_132_);
lean_dec(v___x_131_);
v_lctx_133_ = lean_ctor_get(v___y_124_, 2);
v_options_134_ = lean_ctor_get(v___y_126_, 2);
lean_inc_ref(v_options_134_);
lean_inc_ref(v_lctx_133_);
v___x_135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_135_, 0, v_env_130_);
lean_ctor_set(v___x_135_, 1, v_mctx_132_);
lean_ctor_set(v___x_135_, 2, v_lctx_133_);
lean_ctor_set(v___x_135_, 3, v_options_134_);
v___x_136_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v_msgData_123_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0___boxed(lean_object* v_msgData_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(v_msgData_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___redArg(lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_ref_151_; lean_object* v___x_152_; lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
v_ref_151_ = lean_ctor_get(v___y_148_, 5);
v___x_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
lean_inc(v_ref_151_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_ref_151_);
lean_ctor_set(v___x_157_, 1, v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 1);
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___redArg___boxed(lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___redArg(v_msg_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_168_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__5(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__4));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; lean_object* v_target_194_; 
v___x_193_ = lean_st_ref_get(v_a_182_);
v_target_194_ = lean_ctor_get(v___x_193_, 4);
lean_inc_ref(v_target_194_);
lean_dec(v___x_193_);
if (lean_obj_tag(v_target_194_) == 0)
{
lean_object* v_mvar_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_258_; 
v_mvar_195_ = lean_ctor_get(v_target_194_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v_target_194_);
if (v_isSharedCheck_258_ == 0)
{
v___x_197_ = v_target_194_;
v_isShared_198_ = v_isSharedCheck_258_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_mvar_195_);
lean_dec(v_target_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_258_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = 1;
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__0));
v___x_201_ = l_Lean_MVarId_falseOrByContra(v_mvar_195_, v___x_200_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_249_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_249_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_249_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_249_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
if (lean_obj_tag(v_a_202_) == 1)
{
lean_object* v_val_206_; lean_object* v___x_207_; 
lean_del_object(v___x_204_);
v_val_206_ = lean_ctor_get(v_a_202_, 0);
lean_inc(v_val_206_);
lean_dec_ref_known(v_a_202_, 1);
v___x_207_ = l_Lean_Meta_Sym_preprocessMVar(v_val_206_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_236_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_236_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_236_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_236_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v_rewriteSimpCache_213_; lean_object* v_rewriteDSimpCache_214_; lean_object* v_acCache_215_; lean_object* v_typeAnalysis_216_; lean_object* v_hypotheses_217_; uint8_t v_didChange_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_234_; 
v___x_212_ = lean_st_ref_take(v_a_182_);
v_rewriteSimpCache_213_ = lean_ctor_get(v___x_212_, 0);
v_rewriteDSimpCache_214_ = lean_ctor_get(v___x_212_, 1);
v_acCache_215_ = lean_ctor_get(v___x_212_, 2);
v_typeAnalysis_216_ = lean_ctor_get(v___x_212_, 3);
v_hypotheses_217_ = lean_ctor_get(v___x_212_, 5);
v_didChange_218_ = lean_ctor_get_uint8(v___x_212_, sizeof(void*)*6);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v___x_212_, 4);
lean_dec(v_unused_235_);
v___x_220_ = v___x_212_;
v_isShared_221_ = v_isSharedCheck_234_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_hypotheses_217_);
lean_inc(v_typeAnalysis_216_);
lean_inc(v_acCache_215_);
lean_inc(v_rewriteDSimpCache_214_);
lean_inc(v_rewriteSimpCache_213_);
lean_dec(v___x_212_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_234_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v_a_208_);
v___x_223_ = v___x_197_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_208_);
v___x_223_ = v_reuseFailAlloc_233_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_225_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 4, v___x_223_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_rewriteSimpCache_213_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_rewriteDSimpCache_214_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_acCache_215_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_typeAnalysis_216_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_232_, 5, v_hypotheses_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_232_, sizeof(void*)*6, v_didChange_218_);
v___x_225_ = v_reuseFailAlloc_232_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_226_ = lean_st_ref_set(v_a_182_, v___x_225_);
v___x_227_ = 0;
v___x_228_ = lean_box(v___x_227_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_228_);
v___x_230_ = v___x_210_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_del_object(v___x_197_);
v_a_237_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_207_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_207_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec(v_a_202_);
lean_del_object(v___x_197_);
v___x_245_ = lean_box(v___x_199_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_245_);
v___x_247_ = v___x_204_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_del_object(v___x_197_);
v_a_250_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_201_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_201_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
else
{
lean_object* v_goal_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_317_; 
v_goal_259_ = lean_ctor_get(v_target_194_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_target_194_);
if (v_isSharedCheck_317_ == 0)
{
v___x_261_ = v_target_194_;
v_isShared_262_ = v_isSharedCheck_317_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_goal_259_);
lean_dec(v_target_194_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_317_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___f_263_; lean_object* v___x_264_; 
v___f_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__3));
v___x_264_ = l_Lean_Meta_Grind_Action_run(v_goal_259_, v___f_263_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_308_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_308_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_308_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_308_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
if (lean_obj_tag(v_a_265_) == 0)
{
uint8_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec_ref_known(v_a_265_, 1);
lean_del_object(v___x_261_);
v___x_269_ = 1;
v___x_270_ = lean_box(v___x_269_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_270_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
else
{
lean_object* v_gs_274_; 
v_gs_274_ = lean_ctor_get(v_a_265_, 0);
lean_inc(v_gs_274_);
lean_dec_ref_known(v_a_265_, 1);
if (lean_obj_tag(v_gs_274_) == 0)
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
lean_del_object(v___x_261_);
v___x_275_ = 1;
v___x_276_ = lean_box(v___x_275_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_276_);
v___x_278_ = v___x_267_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
else
{
lean_object* v_tail_280_; 
v_tail_280_ = lean_ctor_get(v_gs_274_, 1);
if (lean_obj_tag(v_tail_280_) == 0)
{
lean_object* v_head_281_; lean_object* v___x_282_; lean_object* v_rewriteSimpCache_283_; lean_object* v_rewriteDSimpCache_284_; lean_object* v_acCache_285_; lean_object* v_typeAnalysis_286_; lean_object* v_hypotheses_287_; uint8_t v_didChange_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_304_; 
v_head_281_ = lean_ctor_get(v_gs_274_, 0);
lean_inc(v_head_281_);
lean_dec_ref_known(v_gs_274_, 2);
v___x_282_ = lean_st_ref_take(v_a_182_);
v_rewriteSimpCache_283_ = lean_ctor_get(v___x_282_, 0);
v_rewriteDSimpCache_284_ = lean_ctor_get(v___x_282_, 1);
v_acCache_285_ = lean_ctor_get(v___x_282_, 2);
v_typeAnalysis_286_ = lean_ctor_get(v___x_282_, 3);
v_hypotheses_287_ = lean_ctor_get(v___x_282_, 5);
v_didChange_288_ = lean_ctor_get_uint8(v___x_282_, sizeof(void*)*6);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v___x_282_, 4);
lean_dec(v_unused_305_);
v___x_290_ = v___x_282_;
v_isShared_291_ = v_isSharedCheck_304_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_hypotheses_287_);
lean_inc(v_typeAnalysis_286_);
lean_inc(v_acCache_285_);
lean_inc(v_rewriteDSimpCache_284_);
lean_inc(v_rewriteSimpCache_283_);
lean_dec(v___x_282_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_304_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v_head_281_);
v___x_293_ = v___x_261_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_head_281_);
v___x_293_ = v_reuseFailAlloc_303_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v___x_293_);
v___x_295_ = v___x_290_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_rewriteSimpCache_283_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_rewriteDSimpCache_284_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_acCache_285_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_typeAnalysis_286_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_302_, 5, v_hypotheses_287_);
lean_ctor_set_uint8(v_reuseFailAlloc_302_, sizeof(void*)*6, v_didChange_288_);
v___x_295_ = v_reuseFailAlloc_302_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_296_ = lean_st_ref_set(v_a_182_, v___x_295_);
v___x_297_ = 0;
v___x_298_ = lean_box(v___x_297_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_298_);
v___x_300_ = v___x_267_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref_known(v_gs_274_, 2);
lean_del_object(v___x_267_);
lean_del_object(v___x_261_);
v___x_306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___closed__5);
v___x_307_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___redArg(v___x_306_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_del_object(v___x_261_);
v_a_309_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_264_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_264_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget___boxed(lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(lean_object* v_00_u03b1_331_, lean_object* v_msg_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___redArg(v_msg_332_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0___boxed(lean_object* v_00_u03b1_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0(v_00_u03b1_346_, v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_360_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_unsigned_to_nat(32u);
v___x_362_ = lean_mk_empty_array_with_capacity(v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_364_ = ((size_t)5ULL);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_unsigned_to_nat(32u);
v___x_367_ = lean_mk_empty_array_with_capacity(v___x_366_);
v___x_368_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__0);
v___x_369_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
lean_ctor_set(v___x_369_, 2, v___x_365_);
lean_ctor_set(v___x_369_, 3, v___x_365_);
lean_ctor_set_usize(v___x_369_, 4, v___x_364_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v_traceState_373_; lean_object* v_traces_374_; lean_object* v___x_375_; lean_object* v_traceState_376_; lean_object* v_env_377_; lean_object* v_nextMacroScope_378_; lean_object* v_ngen_379_; lean_object* v_auxDeclNGen_380_; lean_object* v_cache_381_; lean_object* v_messages_382_; lean_object* v_infoState_383_; lean_object* v_snapshotTasks_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_403_; 
v___x_372_ = lean_st_ref_get(v___y_370_);
v_traceState_373_ = lean_ctor_get(v___x_372_, 4);
lean_inc_ref(v_traceState_373_);
lean_dec(v___x_372_);
v_traces_374_ = lean_ctor_get(v_traceState_373_, 0);
lean_inc_ref(v_traces_374_);
lean_dec_ref(v_traceState_373_);
v___x_375_ = lean_st_ref_take(v___y_370_);
v_traceState_376_ = lean_ctor_get(v___x_375_, 4);
v_env_377_ = lean_ctor_get(v___x_375_, 0);
v_nextMacroScope_378_ = lean_ctor_get(v___x_375_, 1);
v_ngen_379_ = lean_ctor_get(v___x_375_, 2);
v_auxDeclNGen_380_ = lean_ctor_get(v___x_375_, 3);
v_cache_381_ = lean_ctor_get(v___x_375_, 5);
v_messages_382_ = lean_ctor_get(v___x_375_, 6);
v_infoState_383_ = lean_ctor_get(v___x_375_, 7);
v_snapshotTasks_384_ = lean_ctor_get(v___x_375_, 8);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_403_ == 0)
{
v___x_386_ = v___x_375_;
v_isShared_387_ = v_isSharedCheck_403_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_snapshotTasks_384_);
lean_inc(v_infoState_383_);
lean_inc(v_messages_382_);
lean_inc(v_cache_381_);
lean_inc(v_traceState_376_);
lean_inc(v_auxDeclNGen_380_);
lean_inc(v_ngen_379_);
lean_inc(v_nextMacroScope_378_);
lean_inc(v_env_377_);
lean_dec(v___x_375_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_403_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint64_t v_tid_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_401_; 
v_tid_388_ = lean_ctor_get_uint64(v_traceState_376_, sizeof(void*)*1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_traceState_376_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v_traceState_376_, 0);
lean_dec(v_unused_402_);
v___x_390_ = v_traceState_376_;
v_isShared_391_ = v_isSharedCheck_401_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_traceState_376_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_401_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___closed__1);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_392_);
lean_ctor_set_uint64(v_reuseFailAlloc_400_, sizeof(void*)*1, v_tid_388_);
v___x_394_ = v_reuseFailAlloc_400_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 4, v___x_394_);
v___x_396_ = v___x_386_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_env_377_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_nextMacroScope_378_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_ngen_379_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_auxDeclNGen_380_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_399_, 5, v_cache_381_);
lean_ctor_set(v_reuseFailAlloc_399_, 6, v_messages_382_);
lean_ctor_set(v_reuseFailAlloc_399_, 7, v_infoState_383_);
lean_ctor_set(v_reuseFailAlloc_399_, 8, v_snapshotTasks_384_);
v___x_396_ = v_reuseFailAlloc_399_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_st_ref_set(v___y_370_, v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_traces_374_);
return v___x_398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg___boxed(lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_404_);
lean_dec(v___y_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___boxed(lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0(v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(lean_object* v_opts_433_, lean_object* v_opt_434_){
_start:
{
lean_object* v_name_435_; lean_object* v_defValue_436_; lean_object* v_map_437_; lean_object* v___x_438_; 
v_name_435_ = lean_ctor_get(v_opt_434_, 0);
v_defValue_436_ = lean_ctor_get(v_opt_434_, 1);
v_map_437_ = lean_ctor_get(v_opts_433_, 0);
v___x_438_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_437_, v_name_435_);
if (lean_obj_tag(v___x_438_) == 0)
{
uint8_t v___x_439_; 
v___x_439_ = lean_unbox(v_defValue_436_);
return v___x_439_;
}
else
{
lean_object* v_val_440_; 
v_val_440_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v___x_438_, 1);
if (lean_obj_tag(v_val_440_) == 1)
{
uint8_t v_v_441_; 
v_v_441_ = lean_ctor_get_uint8(v_val_440_, 0);
lean_dec_ref_known(v_val_440_, 0);
return v_v_441_;
}
else
{
uint8_t v___x_442_; 
lean_dec(v_val_440_);
v___x_442_ = lean_unbox(v_defValue_436_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1___boxed(lean_object* v_opts_443_, lean_object* v_opt_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_opts_443_, v_opt_444_);
lean_dec_ref(v_opt_444_);
lean_dec_ref(v_opts_443_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__0));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(lean_object* v___x_450_, lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_name_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_474_; 
v_name_464_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_450_, 1);
lean_dec(v_unused_475_);
v___x_466_ = v___x_450_;
v_isShared_467_ = v_isSharedCheck_474_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_name_464_);
lean_dec(v___x_450_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_474_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___closed__1);
v___x_469_ = l_Lean_MessageData_ofName(v_name_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 7);
lean_ctor_set(v___x_466_, 1, v___x_469_);
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_473_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed(lean_object* v___x_476_, lean_object* v_x_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0(v___x_476_, v_x_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v_x_477_);
return v_res_490_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__1));
v___x_495_ = l_Lean_MessageData_ofFormat(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6(lean_object* v_x_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___closed__2);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6___boxed(lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__6(v_x_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_x_511_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(lean_object* v_opts_525_, lean_object* v_opt_526_){
_start:
{
lean_object* v_name_527_; lean_object* v_defValue_528_; lean_object* v_map_529_; lean_object* v___x_530_; 
v_name_527_ = lean_ctor_get(v_opt_526_, 0);
v_defValue_528_ = lean_ctor_get(v_opt_526_, 1);
v_map_529_ = lean_ctor_get(v_opts_525_, 0);
v___x_530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_529_, v_name_527_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_inc(v_defValue_528_);
return v_defValue_528_;
}
else
{
lean_object* v_val_531_; 
v_val_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_val_531_);
lean_dec_ref_known(v___x_530_, 1);
if (lean_obj_tag(v_val_531_) == 3)
{
lean_object* v_v_532_; 
v_v_532_ = lean_ctor_get(v_val_531_, 0);
lean_inc(v_v_532_);
lean_dec_ref_known(v_val_531_, 1);
return v_v_532_;
}
else
{
lean_dec(v_val_531_);
lean_inc(v_defValue_528_);
return v_defValue_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5___boxed(lean_object* v_opts_533_, lean_object* v_opt_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(v_opts_533_, v_opt_534_);
lean_dec_ref(v_opt_534_);
lean_dec_ref(v_opts_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3(size_t v_sz_536_, size_t v_i_537_, lean_object* v_bs_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_lt(v_i_537_, v_sz_536_);
if (v___x_539_ == 0)
{
return v_bs_538_;
}
else
{
lean_object* v_v_540_; lean_object* v_msg_541_; lean_object* v___x_542_; lean_object* v_bs_x27_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v_v_540_ = lean_array_uget_borrowed(v_bs_538_, v_i_537_);
v_msg_541_ = lean_ctor_get(v_v_540_, 1);
lean_inc_ref(v_msg_541_);
v___x_542_ = lean_unsigned_to_nat(0u);
v_bs_x27_543_ = lean_array_uset(v_bs_538_, v_i_537_, v___x_542_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_537_, v___x_544_);
v___x_546_ = lean_array_uset(v_bs_x27_543_, v_i_537_, v_msg_541_);
v_i_537_ = v___x_545_;
v_bs_538_ = v___x_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_bs_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3(v_sz_boxed_551_, v_i_boxed_552_, v_bs_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(lean_object* v_oldTraces_554_, lean_object* v_data_555_, lean_object* v_ref_556_, lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_fileName_563_; lean_object* v_fileMap_564_; lean_object* v_options_565_; lean_object* v_currRecDepth_566_; lean_object* v_maxRecDepth_567_; lean_object* v_ref_568_; lean_object* v_currNamespace_569_; lean_object* v_openDecls_570_; lean_object* v_initHeartbeats_571_; lean_object* v_maxHeartbeats_572_; lean_object* v_quotContext_573_; lean_object* v_currMacroScope_574_; uint8_t v_diag_575_; lean_object* v_cancelTk_x3f_576_; uint8_t v_suppressElabErrors_577_; lean_object* v_inheritedTraceOptions_578_; lean_object* v___x_579_; lean_object* v_traceState_580_; lean_object* v_traces_581_; lean_object* v_ref_582_; lean_object* v___x_583_; lean_object* v___x_584_; size_t v_sz_585_; size_t v___x_586_; lean_object* v___x_587_; lean_object* v_msg_588_; lean_object* v___x_589_; lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_627_; 
v_fileName_563_ = lean_ctor_get(v___y_560_, 0);
v_fileMap_564_ = lean_ctor_get(v___y_560_, 1);
v_options_565_ = lean_ctor_get(v___y_560_, 2);
v_currRecDepth_566_ = lean_ctor_get(v___y_560_, 3);
v_maxRecDepth_567_ = lean_ctor_get(v___y_560_, 4);
v_ref_568_ = lean_ctor_get(v___y_560_, 5);
v_currNamespace_569_ = lean_ctor_get(v___y_560_, 6);
v_openDecls_570_ = lean_ctor_get(v___y_560_, 7);
v_initHeartbeats_571_ = lean_ctor_get(v___y_560_, 8);
v_maxHeartbeats_572_ = lean_ctor_get(v___y_560_, 9);
v_quotContext_573_ = lean_ctor_get(v___y_560_, 10);
v_currMacroScope_574_ = lean_ctor_get(v___y_560_, 11);
v_diag_575_ = lean_ctor_get_uint8(v___y_560_, sizeof(void*)*14);
v_cancelTk_x3f_576_ = lean_ctor_get(v___y_560_, 12);
v_suppressElabErrors_577_ = lean_ctor_get_uint8(v___y_560_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_578_ = lean_ctor_get(v___y_560_, 13);
v___x_579_ = lean_st_ref_get(v___y_561_);
v_traceState_580_ = lean_ctor_get(v___x_579_, 4);
lean_inc_ref(v_traceState_580_);
lean_dec(v___x_579_);
v_traces_581_ = lean_ctor_get(v_traceState_580_, 0);
lean_inc_ref(v_traces_581_);
lean_dec_ref(v_traceState_580_);
v_ref_582_ = l_Lean_replaceRef(v_ref_556_, v_ref_568_);
lean_inc_ref(v_inheritedTraceOptions_578_);
lean_inc(v_cancelTk_x3f_576_);
lean_inc(v_currMacroScope_574_);
lean_inc(v_quotContext_573_);
lean_inc(v_maxHeartbeats_572_);
lean_inc(v_initHeartbeats_571_);
lean_inc(v_openDecls_570_);
lean_inc(v_currNamespace_569_);
lean_inc(v_maxRecDepth_567_);
lean_inc(v_currRecDepth_566_);
lean_inc_ref(v_options_565_);
lean_inc_ref(v_fileMap_564_);
lean_inc_ref(v_fileName_563_);
v___x_583_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_583_, 0, v_fileName_563_);
lean_ctor_set(v___x_583_, 1, v_fileMap_564_);
lean_ctor_set(v___x_583_, 2, v_options_565_);
lean_ctor_set(v___x_583_, 3, v_currRecDepth_566_);
lean_ctor_set(v___x_583_, 4, v_maxRecDepth_567_);
lean_ctor_set(v___x_583_, 5, v_ref_582_);
lean_ctor_set(v___x_583_, 6, v_currNamespace_569_);
lean_ctor_set(v___x_583_, 7, v_openDecls_570_);
lean_ctor_set(v___x_583_, 8, v_initHeartbeats_571_);
lean_ctor_set(v___x_583_, 9, v_maxHeartbeats_572_);
lean_ctor_set(v___x_583_, 10, v_quotContext_573_);
lean_ctor_set(v___x_583_, 11, v_currMacroScope_574_);
lean_ctor_set(v___x_583_, 12, v_cancelTk_x3f_576_);
lean_ctor_set(v___x_583_, 13, v_inheritedTraceOptions_578_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*14, v_diag_575_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*14 + 1, v_suppressElabErrors_577_);
v___x_584_ = l_Lean_PersistentArray_toArray___redArg(v_traces_581_);
lean_dec_ref(v_traces_581_);
v_sz_585_ = lean_array_size(v___x_584_);
v___x_586_ = ((size_t)0ULL);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2_spec__3(v_sz_585_, v___x_586_, v___x_584_);
v_msg_588_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_588_, 0, v_data_555_);
lean_ctor_set(v_msg_588_, 1, v_msg_557_);
lean_ctor_set(v_msg_588_, 2, v___x_587_);
v___x_589_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(v_msg_588_, v___y_558_, v___y_559_, v___x_583_, v___y_561_);
lean_dec_ref_known(v___x_583_, 14);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_627_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_627_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_627_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v_traceState_595_; lean_object* v_env_596_; lean_object* v_nextMacroScope_597_; lean_object* v_ngen_598_; lean_object* v_auxDeclNGen_599_; lean_object* v_cache_600_; lean_object* v_messages_601_; lean_object* v_infoState_602_; lean_object* v_snapshotTasks_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_626_; 
v___x_594_ = lean_st_ref_take(v___y_561_);
v_traceState_595_ = lean_ctor_get(v___x_594_, 4);
v_env_596_ = lean_ctor_get(v___x_594_, 0);
v_nextMacroScope_597_ = lean_ctor_get(v___x_594_, 1);
v_ngen_598_ = lean_ctor_get(v___x_594_, 2);
v_auxDeclNGen_599_ = lean_ctor_get(v___x_594_, 3);
v_cache_600_ = lean_ctor_get(v___x_594_, 5);
v_messages_601_ = lean_ctor_get(v___x_594_, 6);
v_infoState_602_ = lean_ctor_get(v___x_594_, 7);
v_snapshotTasks_603_ = lean_ctor_get(v___x_594_, 8);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_626_ == 0)
{
v___x_605_ = v___x_594_;
v_isShared_606_ = v_isSharedCheck_626_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_snapshotTasks_603_);
lean_inc(v_infoState_602_);
lean_inc(v_messages_601_);
lean_inc(v_cache_600_);
lean_inc(v_traceState_595_);
lean_inc(v_auxDeclNGen_599_);
lean_inc(v_ngen_598_);
lean_inc(v_nextMacroScope_597_);
lean_inc(v_env_596_);
lean_dec(v___x_594_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_626_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
uint64_t v_tid_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_624_; 
v_tid_607_ = lean_ctor_get_uint64(v_traceState_595_, sizeof(void*)*1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_traceState_595_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v_traceState_595_, 0);
lean_dec(v_unused_625_);
v___x_609_ = v_traceState_595_;
v_isShared_610_ = v_isSharedCheck_624_;
goto v_resetjp_608_;
}
else
{
lean_dec(v_traceState_595_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_624_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v_ref_556_);
lean_ctor_set(v___x_611_, 1, v_a_590_);
v___x_612_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_554_, v___x_611_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_612_);
v___x_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_612_);
lean_ctor_set_uint64(v_reuseFailAlloc_623_, sizeof(void*)*1, v_tid_607_);
v___x_614_ = v_reuseFailAlloc_623_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v___x_614_);
v___x_616_ = v___x_605_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_env_596_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_nextMacroScope_597_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_ngen_598_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_auxDeclNGen_599_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v_cache_600_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_messages_601_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_infoState_602_);
lean_ctor_set(v_reuseFailAlloc_622_, 8, v_snapshotTasks_603_);
v___x_616_ = v_reuseFailAlloc_622_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = lean_st_ref_set(v___y_561_, v___x_616_);
v___x_618_ = lean_box(0);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_618_);
v___x_620_ = v___x_592_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_628_, lean_object* v_data_629_, lean_object* v_ref_630_, lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(v_oldTraces_628_, v_data_629_, v_ref_630_, v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_638_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v_x_638_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_638_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v_x_638_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v_x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v_x_638_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_638_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v_x_638_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v_x_638_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 0);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg___boxed(lean_object* v_x_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_656_);
return v_res_658_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4(lean_object* v_e_659_){
_start:
{
if (lean_obj_tag(v_e_659_) == 0)
{
uint8_t v___x_660_; 
v___x_660_ = 2;
return v___x_660_;
}
else
{
lean_object* v_a_661_; uint8_t v___x_662_; 
v_a_661_ = lean_ctor_get(v_e_659_, 0);
v___x_662_ = lean_unbox(v_a_661_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; 
v___x_663_ = 1;
return v___x_663_;
}
else
{
uint8_t v___x_664_; 
v___x_664_ = 0;
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4___boxed(lean_object* v_e_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4(v_e_665_);
lean_dec_ref(v_e_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0(void){
_start:
{
lean_object* v___x_668_; double v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_float_of_nat(v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__1));
v___x_672_ = l_Lean_stringToMessageData(v___x_671_);
return v___x_672_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3(void){
_start:
{
lean_object* v___x_673_; double v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1000u);
v___x_674_ = lean_float_of_nat(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(lean_object* v_cls_675_, uint8_t v_collapsed_676_, lean_object* v_tag_677_, lean_object* v_opts_678_, uint8_t v_clsEnabled_679_, lean_object* v_oldTraces_680_, lean_object* v_msg_681_, lean_object* v_resStartStop_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v_data_700_; lean_object* v_fst_711_; lean_object* v_snd_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___y_716_; lean_object* v_a_717_; uint8_t v___y_732_; double v___y_763_; 
v_fst_695_ = lean_ctor_get(v_resStartStop_682_, 0);
lean_inc(v_fst_695_);
v_snd_696_ = lean_ctor_get(v_resStartStop_682_, 1);
lean_inc(v_snd_696_);
lean_dec_ref(v_resStartStop_682_);
v_fst_711_ = lean_ctor_get(v_snd_696_, 0);
lean_inc(v_fst_711_);
v_snd_712_ = lean_ctor_get(v_snd_696_, 1);
lean_inc(v_snd_712_);
lean_dec(v_snd_696_);
v___x_713_ = l_Lean_trace_profiler;
v___x_714_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_opts_678_, v___x_713_);
if (v___x_714_ == 0)
{
v___y_732_ = v___x_714_;
goto v___jp_731_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = l_Lean_trace_profiler_useHeartbeats;
v___x_769_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_opts_678_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; double v___x_772_; double v___x_773_; double v___x_774_; 
v___x_770_ = l_Lean_trace_profiler_threshold;
v___x_771_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(v_opts_678_, v___x_770_);
v___x_772_ = lean_float_of_nat(v___x_771_);
v___x_773_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__3);
v___x_774_ = lean_float_div(v___x_772_, v___x_773_);
v___y_763_ = v___x_774_;
goto v___jp_762_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; double v___x_777_; 
v___x_775_ = l_Lean_trace_profiler_threshold;
v___x_776_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__5(v_opts_678_, v___x_775_);
v___x_777_ = lean_float_of_nat(v___x_776_);
v___y_763_ = v___x_777_;
goto v___jp_762_;
}
}
v___jp_697_:
{
lean_object* v___x_701_; 
lean_inc(v___y_699_);
v___x_701_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(v_oldTraces_680_, v_data_700_, v___y_699_, v___y_698_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v___x_702_; 
lean_dec_ref_known(v___x_701_, 1);
v___x_702_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_695_);
return v___x_702_;
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v_fst_695_);
v_a_703_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_701_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_701_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
v___jp_715_:
{
uint8_t v_result_718_; lean_object* v___x_719_; lean_object* v___x_720_; double v___x_721_; lean_object* v_data_722_; 
v_result_718_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__4(v_fst_695_);
v___x_719_ = lean_box(v_result_718_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
v___x_721_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0);
lean_inc_ref(v_tag_677_);
lean_inc_ref(v___x_720_);
lean_inc(v_cls_675_);
v_data_722_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_722_, 0, v_cls_675_);
lean_ctor_set(v_data_722_, 1, v___x_720_);
lean_ctor_set(v_data_722_, 2, v_tag_677_);
lean_ctor_set_float(v_data_722_, sizeof(void*)*3, v___x_721_);
lean_ctor_set_float(v_data_722_, sizeof(void*)*3 + 8, v___x_721_);
lean_ctor_set_uint8(v_data_722_, sizeof(void*)*3 + 16, v_collapsed_676_);
if (v___x_714_ == 0)
{
lean_dec_ref_known(v___x_720_, 1);
lean_dec(v_snd_712_);
lean_dec(v_fst_711_);
lean_dec_ref(v_tag_677_);
lean_dec(v_cls_675_);
v___y_698_ = v_a_717_;
v___y_699_ = v___y_716_;
v_data_700_ = v_data_722_;
goto v___jp_697_;
}
else
{
lean_object* v_data_723_; double v___x_724_; double v___x_725_; 
lean_dec_ref_known(v_data_722_, 3);
v_data_723_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_723_, 0, v_cls_675_);
lean_ctor_set(v_data_723_, 1, v___x_720_);
lean_ctor_set(v_data_723_, 2, v_tag_677_);
v___x_724_ = lean_unbox_float(v_fst_711_);
lean_dec(v_fst_711_);
lean_ctor_set_float(v_data_723_, sizeof(void*)*3, v___x_724_);
v___x_725_ = lean_unbox_float(v_snd_712_);
lean_dec(v_snd_712_);
lean_ctor_set_float(v_data_723_, sizeof(void*)*3 + 8, v___x_725_);
lean_ctor_set_uint8(v_data_723_, sizeof(void*)*3 + 16, v_collapsed_676_);
v___y_698_ = v_a_717_;
v___y_699_ = v___y_716_;
v_data_700_ = v_data_723_;
goto v___jp_697_;
}
}
v___jp_726_:
{
lean_object* v_ref_727_; lean_object* v___x_728_; 
v_ref_727_ = lean_ctor_get(v___y_692_, 5);
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_685_);
lean_inc(v___y_684_);
lean_inc_ref(v___y_683_);
lean_inc(v_fst_695_);
v___x_728_ = lean_apply_13(v_msg_681_, v_fst_695_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, lean_box(0));
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___y_716_ = v_ref_727_;
v_a_717_ = v_a_729_;
goto v___jp_715_;
}
else
{
lean_object* v___x_730_; 
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__2);
v___y_716_ = v_ref_727_;
v_a_717_ = v___x_730_;
goto v___jp_715_;
}
}
v___jp_731_:
{
if (v_clsEnabled_679_ == 0)
{
if (v___y_732_ == 0)
{
lean_object* v___x_733_; lean_object* v_traceState_734_; lean_object* v_env_735_; lean_object* v_nextMacroScope_736_; lean_object* v_ngen_737_; lean_object* v_auxDeclNGen_738_; lean_object* v_cache_739_; lean_object* v_messages_740_; lean_object* v_infoState_741_; lean_object* v_snapshotTasks_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_snd_712_);
lean_dec(v_fst_711_);
lean_dec_ref(v_msg_681_);
lean_dec_ref(v_tag_677_);
lean_dec(v_cls_675_);
v___x_733_ = lean_st_ref_take(v___y_693_);
v_traceState_734_ = lean_ctor_get(v___x_733_, 4);
v_env_735_ = lean_ctor_get(v___x_733_, 0);
v_nextMacroScope_736_ = lean_ctor_get(v___x_733_, 1);
v_ngen_737_ = lean_ctor_get(v___x_733_, 2);
v_auxDeclNGen_738_ = lean_ctor_get(v___x_733_, 3);
v_cache_739_ = lean_ctor_get(v___x_733_, 5);
v_messages_740_ = lean_ctor_get(v___x_733_, 6);
v_infoState_741_ = lean_ctor_get(v___x_733_, 7);
v_snapshotTasks_742_ = lean_ctor_get(v___x_733_, 8);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_761_ == 0)
{
v___x_744_ = v___x_733_;
v_isShared_745_ = v_isSharedCheck_761_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snapshotTasks_742_);
lean_inc(v_infoState_741_);
lean_inc(v_messages_740_);
lean_inc(v_cache_739_);
lean_inc(v_traceState_734_);
lean_inc(v_auxDeclNGen_738_);
lean_inc(v_ngen_737_);
lean_inc(v_nextMacroScope_736_);
lean_inc(v_env_735_);
lean_dec(v___x_733_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_761_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
uint64_t v_tid_746_; lean_object* v_traces_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_760_; 
v_tid_746_ = lean_ctor_get_uint64(v_traceState_734_, sizeof(void*)*1);
v_traces_747_ = lean_ctor_get(v_traceState_734_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_traceState_734_);
if (v_isSharedCheck_760_ == 0)
{
v___x_749_ = v_traceState_734_;
v_isShared_750_ = v_isSharedCheck_760_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_traces_747_);
lean_dec(v_traceState_734_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_760_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_680_, v_traces_747_);
lean_dec_ref(v_traces_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_751_);
lean_ctor_set_uint64(v_reuseFailAlloc_759_, sizeof(void*)*1, v_tid_746_);
v___x_753_ = v_reuseFailAlloc_759_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 4, v___x_753_);
v___x_755_ = v___x_744_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_env_735_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_nextMacroScope_736_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_ngen_737_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_auxDeclNGen_738_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_758_, 5, v_cache_739_);
lean_ctor_set(v_reuseFailAlloc_758_, 6, v_messages_740_);
lean_ctor_set(v_reuseFailAlloc_758_, 7, v_infoState_741_);
lean_ctor_set(v_reuseFailAlloc_758_, 8, v_snapshotTasks_742_);
v___x_755_ = v_reuseFailAlloc_758_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_st_ref_set(v___y_693_, v___x_755_);
v___x_757_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_fst_695_);
return v___x_757_;
}
}
}
}
}
else
{
goto v___jp_726_;
}
}
else
{
goto v___jp_726_;
}
}
v___jp_762_:
{
double v___x_764_; double v___x_765_; double v___x_766_; uint8_t v___x_767_; 
v___x_764_ = lean_unbox_float(v_snd_712_);
v___x_765_ = lean_unbox_float(v_fst_711_);
v___x_766_ = lean_float_sub(v___x_764_, v___x_765_);
v___x_767_ = lean_float_decLt(v___y_763_, v___x_766_);
v___y_732_ = v___x_767_;
goto v___jp_731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___boxed(lean_object** _args){
lean_object* v_cls_778_ = _args[0];
lean_object* v_collapsed_779_ = _args[1];
lean_object* v_tag_780_ = _args[2];
lean_object* v_opts_781_ = _args[3];
lean_object* v_clsEnabled_782_ = _args[4];
lean_object* v_oldTraces_783_ = _args[5];
lean_object* v_msg_784_ = _args[6];
lean_object* v_resStartStop_785_ = _args[7];
lean_object* v___y_786_ = _args[8];
lean_object* v___y_787_ = _args[9];
lean_object* v___y_788_ = _args[10];
lean_object* v___y_789_ = _args[11];
lean_object* v___y_790_ = _args[12];
lean_object* v___y_791_ = _args[13];
lean_object* v___y_792_ = _args[14];
lean_object* v___y_793_ = _args[15];
lean_object* v___y_794_ = _args[16];
lean_object* v___y_795_ = _args[17];
lean_object* v___y_796_ = _args[18];
lean_object* v___y_797_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_798_; uint8_t v_clsEnabled_boxed_799_; lean_object* v_res_800_; 
v_collapsed_boxed_798_ = lean_unbox(v_collapsed_779_);
v_clsEnabled_boxed_799_ = lean_unbox(v_clsEnabled_782_);
v_res_800_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_778_, v_collapsed_boxed_798_, v_tag_780_, v_opts_781_, v_clsEnabled_boxed_799_, v_oldTraces_783_, v_msg_784_, v_resStartStop_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec_ref(v_opts_781_);
return v_res_800_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0(void){
_start:
{
lean_object* v___x_801_; double v___x_802_; 
v___x_801_ = lean_unsigned_to_nat(1000000000u);
v___x_802_ = lean_float_of_nat(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___f_804_; 
v___x_803_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 14, 1);
lean_closure_set(v___f_804_, 0, v___x_803_);
return v___f_804_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4(void){
_start:
{
lean_object* v___x_808_; lean_object* v___f_809_; 
v___x_808_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v___f_809_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 14, 1);
lean_closure_set(v___f_809_, 0, v___x_808_);
return v___f_809_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5(void){
_start:
{
lean_object* v___x_810_; lean_object* v___f_811_; 
v___x_810_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v___f_811_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 14, 1);
lean_closure_set(v___f_811_, 0, v___x_810_);
return v___f_811_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6(void){
_start:
{
lean_object* v___x_812_; lean_object* v___f_813_; 
v___x_812_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 14, 1);
lean_closure_set(v___f_813_, 0, v___x_812_);
return v___f_813_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7(void){
_start:
{
lean_object* v___x_814_; lean_object* v___f_815_; 
v___x_814_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 14, 1);
lean_closure_set(v___f_815_, 0, v___x_814_);
return v___f_815_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8(void){
_start:
{
lean_object* v___x_816_; lean_object* v___f_817_; 
v___x_816_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v___f_817_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__0___boxed), 14, 1);
lean_closure_set(v___f_817_, 0, v___x_816_);
return v___f_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8(uint8_t v___x_818_, uint8_t v_hasTrace_819_, lean_object* v_cls_820_, lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v_____r_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___y_837_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; uint8_t v___y_868_; lean_object* v___y_869_; lean_object* v_a_870_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; uint8_t v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; uint8_t v___y_895_; lean_object* v___y_896_; lean_object* v_a_897_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; uint8_t v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; uint8_t v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v_config_965_; uint8_t v_structures_966_; uint8_t v_fixedInt_967_; uint8_t v_enums_968_; uint8_t v_shortCircuit_969_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; uint8_t v___y_1046_; lean_object* v___y_1047_; uint8_t v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v_a_1054_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1075_; lean_object* v___y_1076_; uint8_t v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v_a_1084_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; uint8_t v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; uint8_t v___y_1213_; lean_object* v___y_1214_; uint8_t v___y_1215_; lean_object* v_a_1216_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; lean_object* v_a_1243_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; uint8_t v___y_1270_; uint8_t v___y_1271_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; uint8_t v___y_1371_; uint8_t v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v_a_1378_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v_a_1405_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; uint8_t v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; uint8_t v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v_a_1528_; uint8_t v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; uint8_t v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v_a_1558_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; uint8_t v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1650_; lean_object* v___y_1662_; uint8_t v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; uint8_t v___y_1666_; lean_object* v___y_1667_; lean_object* v_a_1668_; lean_object* v___y_1678_; uint8_t v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v_a_1684_; uint8_t v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; uint8_t v___y_1701_; 
v_config_965_ = lean_ctor_get(v___y_824_, 0);
v_structures_966_ = lean_ctor_get_uint8(v_config_965_, sizeof(void*)*2 + 5);
v_fixedInt_967_ = lean_ctor_get_uint8(v_config_965_, sizeof(void*)*2 + 6);
v_enums_968_ = lean_ctor_get_uint8(v_config_965_, sizeof(void*)*2 + 7);
v_shortCircuit_969_ = lean_ctor_get_uint8(v_config_965_, sizeof(void*)*2 + 9);
if (v_structures_966_ == 0)
{
if (v_enums_968_ == 0)
{
v___y_1624_ = v___y_824_;
v___y_1625_ = v___y_825_;
v___y_1626_ = v___y_826_;
v___y_1627_ = v___y_827_;
v___y_1628_ = v___y_828_;
v___y_1629_ = v___y_829_;
v___y_1630_ = v___y_830_;
v___y_1631_ = v___y_831_;
v___y_1632_ = v___y_832_;
v___y_1633_ = v___y_833_;
v___y_1634_ = v___y_834_;
goto v___jp_1623_;
}
else
{
goto v___jp_1741_;
}
}
else
{
goto v___jp_1741_;
}
v___jp_836_:
{
if (lean_obj_tag(v___y_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_851_; 
v_a_838_ = lean_ctor_get(v___y_837_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___y_837_);
if (v_isSharedCheck_851_ == 0)
{
v___x_840_ = v___y_837_;
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___y_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_851_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
uint8_t v___x_842_; 
v___x_842_ = lean_unbox(v_a_838_);
lean_dec(v_a_838_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_box(v___x_818_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_843_);
v___x_845_ = v___x_840_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_847_ = lean_box(v_hasTrace_819_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_847_);
v___x_849_ = v___x_840_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
return v___y_837_;
}
}
v___jp_852_:
{
lean_object* v___x_871_; double v___x_872_; double v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_871_ = lean_io_get_num_heartbeats();
v___x_872_ = lean_float_of_nat(v___y_861_);
v___x_873_ = lean_float_of_nat(v___x_871_);
v___x_874_ = lean_box_float(v___x_872_);
v___x_875_ = lean_box_float(v___x_873_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_a_870_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
lean_inc_ref(v___y_864_);
v___x_878_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_868_, v___x_821_, v___y_855_, v___y_858_, v___y_854_, v___y_864_, v___x_877_, v___y_866_, v___y_863_, v___y_865_, v___y_856_, v___y_859_, v___y_853_, v___y_869_, v___y_857_, v___y_860_, v___y_862_, v___y_867_);
v___y_837_ = v___x_878_;
goto v___jp_836_;
}
v___jp_879_:
{
lean_object* v___x_898_; double v___x_899_; double v___x_900_; double v___x_901_; double v___x_902_; double v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_898_ = lean_io_mono_nanos_now();
v___x_899_ = lean_float_of_nat(v___y_882_);
v___x_900_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_901_ = lean_float_div(v___x_899_, v___x_900_);
v___x_902_ = lean_float_of_nat(v___x_898_);
v___x_903_ = lean_float_div(v___x_902_, v___x_900_);
v___x_904_ = lean_box_float(v___x_901_);
v___x_905_ = lean_box_float(v___x_903_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v_a_897_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
lean_inc_ref(v___y_891_);
v___x_908_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_895_, v___x_821_, v___y_883_, v___y_886_, v___y_881_, v___y_891_, v___x_907_, v___y_893_, v___y_890_, v___y_892_, v___y_884_, v___y_887_, v___y_880_, v___y_896_, v___y_885_, v___y_888_, v___y_889_, v___y_894_);
v___y_837_ = v___x_908_;
goto v___jp_836_;
}
v___jp_909_:
{
lean_object* v___x_926_; lean_object* v_a_927_; uint8_t v___x_928_; 
v___x_926_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_924_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref(v___x_926_);
v___x_928_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_912_, v___x_822_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_io_mono_nanos_now();
lean_inc(v___y_924_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_921_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_922_);
v___x_930_ = lean_apply_12(v___y_918_, v___y_922_, v___y_919_, v___y_921_, v___y_911_, v___y_915_, v___y_910_, v___y_925_, v___y_913_, v___y_916_, v___y_917_, v___y_924_, lean_box(0));
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 1);
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
v___y_880_ = v___y_910_;
v___y_881_ = v_a_927_;
v___y_882_ = v___x_929_;
v___y_883_ = v___y_912_;
v___y_884_ = v___y_911_;
v___y_885_ = v___y_913_;
v___y_886_ = v___y_914_;
v___y_887_ = v___y_915_;
v___y_888_ = v___y_916_;
v___y_889_ = v___y_917_;
v___y_890_ = v___y_919_;
v___y_891_ = v___y_920_;
v___y_892_ = v___y_921_;
v___y_893_ = v___y_922_;
v___y_894_ = v___y_924_;
v___y_895_ = v___y_923_;
v___y_896_ = v___y_925_;
v_a_897_ = v___x_936_;
goto v___jp_879_;
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v_a_939_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_930_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_930_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 0);
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
v___y_880_ = v___y_910_;
v___y_881_ = v_a_927_;
v___y_882_ = v___x_929_;
v___y_883_ = v___y_912_;
v___y_884_ = v___y_911_;
v___y_885_ = v___y_913_;
v___y_886_ = v___y_914_;
v___y_887_ = v___y_915_;
v___y_888_ = v___y_916_;
v___y_889_ = v___y_917_;
v___y_890_ = v___y_919_;
v___y_891_ = v___y_920_;
v___y_892_ = v___y_921_;
v___y_893_ = v___y_922_;
v___y_894_ = v___y_924_;
v___y_895_ = v___y_923_;
v___y_896_ = v___y_925_;
v_a_897_ = v___x_944_;
goto v___jp_879_;
}
}
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_io_get_num_heartbeats();
lean_inc(v___y_924_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_921_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_922_);
v___x_948_ = lean_apply_12(v___y_918_, v___y_922_, v___y_919_, v___y_921_, v___y_911_, v___y_915_, v___y_910_, v___y_925_, v___y_913_, v___y_916_, v___y_917_, v___y_924_, lean_box(0));
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 1);
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v___y_853_ = v___y_910_;
v___y_854_ = v_a_927_;
v___y_855_ = v___y_912_;
v___y_856_ = v___y_911_;
v___y_857_ = v___y_913_;
v___y_858_ = v___y_914_;
v___y_859_ = v___y_915_;
v___y_860_ = v___y_916_;
v___y_861_ = v___x_947_;
v___y_862_ = v___y_917_;
v___y_863_ = v___y_919_;
v___y_864_ = v___y_920_;
v___y_865_ = v___y_921_;
v___y_866_ = v___y_922_;
v___y_867_ = v___y_924_;
v___y_868_ = v___y_923_;
v___y_869_ = v___y_925_;
v_a_870_ = v___x_954_;
goto v___jp_852_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_948_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_948_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 0);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v___y_853_ = v___y_910_;
v___y_854_ = v_a_927_;
v___y_855_ = v___y_912_;
v___y_856_ = v___y_911_;
v___y_857_ = v___y_913_;
v___y_858_ = v___y_914_;
v___y_859_ = v___y_915_;
v___y_860_ = v___y_916_;
v___y_861_ = v___x_947_;
v___y_862_ = v___y_917_;
v___y_863_ = v___y_919_;
v___y_864_ = v___y_920_;
v___y_865_ = v___y_921_;
v___y_866_ = v___y_922_;
v___y_867_ = v___y_924_;
v___y_868_ = v___y_923_;
v___y_869_ = v___y_925_;
v_a_870_ = v___x_962_;
goto v___jp_852_;
}
}
}
}
}
v___jp_970_:
{
lean_object* v___x_982_; lean_object* v_a_983_; lean_object* v___x_984_; 
v___x_982_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_971_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___x_982_);
v___x_984_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_983_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v_a_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1012_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_1012_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1012_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
uint8_t v___x_989_; 
v___x_989_ = lean_unbox(v_a_985_);
lean_dec(v_a_985_);
if (v___x_989_ == 0)
{
if (v_shortCircuit_969_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_992_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
v___x_990_ = lean_box(v___x_818_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_990_);
v___x_992_ = v___x_987_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
else
{
lean_object* v___x_994_; lean_object* v_options_995_; uint8_t v_hasTrace_996_; 
lean_del_object(v___x_987_);
v___x_994_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_options_995_ = lean_ctor_get(v___y_980_, 2);
v_hasTrace_996_ = lean_ctor_get_uint8(v_options_995_, sizeof(void*)*1);
if (v_hasTrace_996_ == 0)
{
lean_object* v_run_x27_997_; lean_object* v___x_998_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
v_run_x27_997_ = lean_ctor_get(v___x_994_, 1);
lean_inc_ref(v_run_x27_997_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
v___x_998_ = lean_apply_12(v_run_x27_997_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, lean_box(0));
v___y_837_ = v___x_998_;
goto v___jp_836_;
}
else
{
lean_object* v_run_x27_999_; lean_object* v_inheritedTraceOptions_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_run_x27_999_ = lean_ctor_get(v___x_994_, 1);
v_inheritedTraceOptions_1000_ = lean_ctor_get(v___y_980_, 13);
v___f_1001_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1);
v___x_1002_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_820_);
v___x_1003_ = l_Lean_Name_append(v___x_1002_, v_cls_820_);
v___x_1004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1000_, v_options_995_, v___x_1003_);
lean_dec(v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = l_Lean_trace_profiler;
v___x_1006_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_995_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
lean_inc_ref(v_run_x27_999_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
v___x_1007_ = lean_apply_12(v_run_x27_999_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, lean_box(0));
v___y_837_ = v___x_1007_;
goto v___jp_836_;
}
else
{
lean_inc_ref(v_run_x27_999_);
v___y_910_ = v___y_976_;
v___y_911_ = v___y_974_;
v___y_912_ = v_options_995_;
v___y_913_ = v___y_978_;
v___y_914_ = v___x_1004_;
v___y_915_ = v___y_975_;
v___y_916_ = v___y_979_;
v___y_917_ = v___y_980_;
v___y_918_ = v_run_x27_999_;
v___y_919_ = v___y_972_;
v___y_920_ = v___f_1001_;
v___y_921_ = v___y_973_;
v___y_922_ = v___y_971_;
v___y_923_ = v_hasTrace_996_;
v___y_924_ = v___y_981_;
v___y_925_ = v___y_977_;
goto v___jp_909_;
}
}
else
{
lean_inc_ref(v_run_x27_999_);
v___y_910_ = v___y_976_;
v___y_911_ = v___y_974_;
v___y_912_ = v_options_995_;
v___y_913_ = v___y_978_;
v___y_914_ = v___x_1004_;
v___y_915_ = v___y_975_;
v___y_916_ = v___y_979_;
v___y_917_ = v___y_980_;
v___y_918_ = v_run_x27_999_;
v___y_919_ = v___y_972_;
v___y_920_ = v___f_1001_;
v___y_921_ = v___y_973_;
v___y_922_ = v___y_971_;
v___y_923_ = v_hasTrace_996_;
v___y_924_ = v___y_981_;
v___y_925_ = v___y_977_;
goto v___jp_909_;
}
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
v___x_1008_ = lean_box(v_hasTrace_819_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_1008_);
v___x_1010_ = v___x_987_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
return v___x_984_;
}
}
v___jp_1013_:
{
if (lean_obj_tag(v___y_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1035_; 
v_a_1026_ = lean_ctor_get(v___y_1025_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___y_1025_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1028_ = v___y_1025_;
v_isShared_1029_ = v_isSharedCheck_1035_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___y_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1035_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_unbox(v_a_1026_);
lean_dec(v_a_1026_);
if (v___x_1030_ == 0)
{
lean_del_object(v___x_1028_);
v___y_971_ = v___y_1024_;
v___y_972_ = v___y_1017_;
v___y_973_ = v___y_1016_;
v___y_974_ = v___y_1015_;
v___y_975_ = v___y_1022_;
v___y_976_ = v___y_1023_;
v___y_977_ = v___y_1019_;
v___y_978_ = v___y_1018_;
v___y_979_ = v___y_1014_;
v___y_980_ = v___y_1020_;
v___y_981_ = v___y_1021_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
v___x_1031_ = lean_box(v_hasTrace_819_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1031_);
v___x_1033_ = v___x_1028_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
return v___y_1025_;
}
}
v___jp_1036_:
{
lean_object* v___x_1055_; double v___x_1056_; double v___x_1057_; double v___x_1058_; double v___x_1059_; double v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1055_ = lean_io_mono_nanos_now();
v___x_1056_ = lean_float_of_nat(v___y_1043_);
v___x_1057_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1058_ = lean_float_div(v___x_1056_, v___x_1057_);
v___x_1059_ = lean_float_of_nat(v___x_1055_);
v___x_1060_ = lean_float_div(v___x_1059_, v___x_1057_);
v___x_1061_ = lean_box_float(v___x_1058_);
v___x_1062_ = lean_box_float(v___x_1060_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_a_1054_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
lean_inc_ref(v___y_1052_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1065_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1048_, v___x_821_, v___y_1037_, v___y_1046_, v___y_1047_, v___y_1052_, v___x_1064_, v___y_1053_, v___y_1040_, v___y_1038_, v___y_1039_, v___y_1044_, v___y_1045_, v___y_1041_, v___y_1050_, v___y_1049_, v___y_1042_, v___y_1051_);
v___y_1014_ = v___y_1049_;
v___y_1015_ = v___y_1039_;
v___y_1016_ = v___y_1038_;
v___y_1017_ = v___y_1040_;
v___y_1018_ = v___y_1050_;
v___y_1019_ = v___y_1041_;
v___y_1020_ = v___y_1042_;
v___y_1021_ = v___y_1051_;
v___y_1022_ = v___y_1044_;
v___y_1023_ = v___y_1045_;
v___y_1024_ = v___y_1053_;
v___y_1025_ = v___x_1065_;
goto v___jp_1013_;
}
v___jp_1066_:
{
lean_object* v___x_1085_; double v___x_1086_; double v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1085_ = lean_io_get_num_heartbeats();
v___x_1086_ = lean_float_of_nat(v___y_1080_);
v___x_1087_ = lean_float_of_nat(v___x_1085_);
v___x_1088_ = lean_box_float(v___x_1086_);
v___x_1089_ = lean_box_float(v___x_1087_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_a_1084_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
lean_inc_ref(v___y_1082_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1092_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1077_, v___x_821_, v___y_1067_, v___y_1075_, v___y_1076_, v___y_1082_, v___x_1091_, v___y_1083_, v___y_1070_, v___y_1068_, v___y_1069_, v___y_1073_, v___y_1074_, v___y_1071_, v___y_1079_, v___y_1078_, v___y_1072_, v___y_1081_);
v___y_1014_ = v___y_1078_;
v___y_1015_ = v___y_1069_;
v___y_1016_ = v___y_1068_;
v___y_1017_ = v___y_1070_;
v___y_1018_ = v___y_1079_;
v___y_1019_ = v___y_1071_;
v___y_1020_ = v___y_1072_;
v___y_1021_ = v___y_1081_;
v___y_1022_ = v___y_1073_;
v___y_1023_ = v___y_1074_;
v___y_1024_ = v___y_1083_;
v___y_1025_ = v___x_1092_;
goto v___jp_1013_;
}
v___jp_1093_:
{
lean_object* v___x_1110_; lean_object* v_a_1111_; uint8_t v___x_1112_; 
v___x_1110_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1107_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1094_, v___x_822_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_io_mono_nanos_now();
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1099_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1101_);
lean_inc(v___y_1100_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1109_);
v___x_1114_ = lean_apply_12(v___y_1105_, v___y_1109_, v___y_1097_, v___y_1095_, v___y_1096_, v___y_1100_, v___y_1101_, v___y_1098_, v___y_1106_, v___y_1104_, v___y_1099_, v___y_1107_, lean_box(0));
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 1);
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
v___y_1037_ = v___y_1094_;
v___y_1038_ = v___y_1095_;
v___y_1039_ = v___y_1096_;
v___y_1040_ = v___y_1097_;
v___y_1041_ = v___y_1098_;
v___y_1042_ = v___y_1099_;
v___y_1043_ = v___x_1113_;
v___y_1044_ = v___y_1100_;
v___y_1045_ = v___y_1101_;
v___y_1046_ = v___y_1102_;
v___y_1047_ = v_a_1111_;
v___y_1048_ = v___y_1103_;
v___y_1049_ = v___y_1104_;
v___y_1050_ = v___y_1106_;
v___y_1051_ = v___y_1107_;
v___y_1052_ = v___y_1108_;
v___y_1053_ = v___y_1109_;
v_a_1054_ = v___x_1120_;
goto v___jp_1036_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1123_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1114_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1114_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
v___y_1037_ = v___y_1094_;
v___y_1038_ = v___y_1095_;
v___y_1039_ = v___y_1096_;
v___y_1040_ = v___y_1097_;
v___y_1041_ = v___y_1098_;
v___y_1042_ = v___y_1099_;
v___y_1043_ = v___x_1113_;
v___y_1044_ = v___y_1100_;
v___y_1045_ = v___y_1101_;
v___y_1046_ = v___y_1102_;
v___y_1047_ = v_a_1111_;
v___y_1048_ = v___y_1103_;
v___y_1049_ = v___y_1104_;
v___y_1050_ = v___y_1106_;
v___y_1051_ = v___y_1107_;
v___y_1052_ = v___y_1108_;
v___y_1053_ = v___y_1109_;
v_a_1054_ = v___x_1128_;
goto v___jp_1036_;
}
}
}
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1099_);
lean_inc(v___y_1104_);
lean_inc_ref(v___y_1106_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1101_);
lean_inc(v___y_1100_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1109_);
v___x_1132_ = lean_apply_12(v___y_1105_, v___y_1109_, v___y_1097_, v___y_1095_, v___y_1096_, v___y_1100_, v___y_1101_, v___y_1098_, v___y_1106_, v___y_1104_, v___y_1099_, v___y_1107_, lean_box(0));
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 1);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
v___y_1067_ = v___y_1094_;
v___y_1068_ = v___y_1095_;
v___y_1069_ = v___y_1096_;
v___y_1070_ = v___y_1097_;
v___y_1071_ = v___y_1098_;
v___y_1072_ = v___y_1099_;
v___y_1073_ = v___y_1100_;
v___y_1074_ = v___y_1101_;
v___y_1075_ = v___y_1102_;
v___y_1076_ = v_a_1111_;
v___y_1077_ = v___y_1103_;
v___y_1078_ = v___y_1104_;
v___y_1079_ = v___y_1106_;
v___y_1080_ = v___x_1131_;
v___y_1081_ = v___y_1107_;
v___y_1082_ = v___y_1108_;
v___y_1083_ = v___y_1109_;
v_a_1084_ = v___x_1138_;
goto v___jp_1066_;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1132_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1132_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
v___y_1067_ = v___y_1094_;
v___y_1068_ = v___y_1095_;
v___y_1069_ = v___y_1096_;
v___y_1070_ = v___y_1097_;
v___y_1071_ = v___y_1098_;
v___y_1072_ = v___y_1099_;
v___y_1073_ = v___y_1100_;
v___y_1074_ = v___y_1101_;
v___y_1075_ = v___y_1102_;
v___y_1076_ = v_a_1111_;
v___y_1077_ = v___y_1103_;
v___y_1078_ = v___y_1104_;
v___y_1079_ = v___y_1106_;
v___y_1080_ = v___x_1131_;
v___y_1081_ = v___y_1107_;
v___y_1082_ = v___y_1108_;
v___y_1083_ = v___y_1109_;
v_a_1084_ = v___x_1146_;
goto v___jp_1066_;
}
}
}
}
}
v___jp_1149_:
{
if (v_fixedInt_967_ == 0)
{
v___y_971_ = v___y_1150_;
v___y_972_ = v___y_1151_;
v___y_973_ = v___y_1152_;
v___y_974_ = v___y_1153_;
v___y_975_ = v___y_1154_;
v___y_976_ = v___y_1155_;
v___y_977_ = v___y_1156_;
v___y_978_ = v___y_1157_;
v___y_979_ = v___y_1158_;
v___y_980_ = v___y_1159_;
v___y_981_ = v___y_1160_;
goto v___jp_970_;
}
else
{
lean_object* v___x_1161_; lean_object* v_options_1162_; uint8_t v_hasTrace_1163_; 
v___x_1161_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_options_1162_ = lean_ctor_get(v___y_1159_, 2);
v_hasTrace_1163_ = lean_ctor_get_uint8(v_options_1162_, sizeof(void*)*1);
if (v_hasTrace_1163_ == 0)
{
lean_object* v_run_x27_1164_; lean_object* v___x_1165_; 
v_run_x27_1164_ = lean_ctor_get(v___x_1161_, 1);
lean_inc_ref(v_run_x27_1164_);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
lean_inc(v___y_1152_);
lean_inc(v___y_1151_);
lean_inc_ref(v___y_1150_);
v___x_1165_ = lean_apply_12(v_run_x27_1164_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, lean_box(0));
v___y_1014_ = v___y_1158_;
v___y_1015_ = v___y_1153_;
v___y_1016_ = v___y_1152_;
v___y_1017_ = v___y_1151_;
v___y_1018_ = v___y_1157_;
v___y_1019_ = v___y_1156_;
v___y_1020_ = v___y_1159_;
v___y_1021_ = v___y_1160_;
v___y_1022_ = v___y_1154_;
v___y_1023_ = v___y_1155_;
v___y_1024_ = v___y_1150_;
v___y_1025_ = v___x_1165_;
goto v___jp_1013_;
}
else
{
lean_object* v_run_x27_1166_; lean_object* v_inheritedTraceOptions_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_run_x27_1166_ = lean_ctor_get(v___x_1161_, 1);
v_inheritedTraceOptions_1167_ = lean_ctor_get(v___y_1159_, 13);
v___f_1168_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4);
v___x_1169_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_820_);
v___x_1170_ = l_Lean_Name_append(v___x_1169_, v_cls_820_);
v___x_1171_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1167_, v_options_1162_, v___x_1170_);
lean_dec(v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = l_Lean_trace_profiler;
v___x_1173_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1162_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_inc_ref(v_run_x27_1166_);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
lean_inc(v___y_1158_);
lean_inc_ref(v___y_1157_);
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
lean_inc(v___y_1154_);
lean_inc_ref(v___y_1153_);
lean_inc(v___y_1152_);
lean_inc(v___y_1151_);
lean_inc_ref(v___y_1150_);
v___x_1174_ = lean_apply_12(v_run_x27_1166_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, lean_box(0));
v___y_1014_ = v___y_1158_;
v___y_1015_ = v___y_1153_;
v___y_1016_ = v___y_1152_;
v___y_1017_ = v___y_1151_;
v___y_1018_ = v___y_1157_;
v___y_1019_ = v___y_1156_;
v___y_1020_ = v___y_1159_;
v___y_1021_ = v___y_1160_;
v___y_1022_ = v___y_1154_;
v___y_1023_ = v___y_1155_;
v___y_1024_ = v___y_1150_;
v___y_1025_ = v___x_1174_;
goto v___jp_1013_;
}
else
{
lean_inc_ref(v_run_x27_1166_);
v___y_1094_ = v_options_1162_;
v___y_1095_ = v___y_1152_;
v___y_1096_ = v___y_1153_;
v___y_1097_ = v___y_1151_;
v___y_1098_ = v___y_1156_;
v___y_1099_ = v___y_1159_;
v___y_1100_ = v___y_1154_;
v___y_1101_ = v___y_1155_;
v___y_1102_ = v___x_1171_;
v___y_1103_ = v_hasTrace_1163_;
v___y_1104_ = v___y_1158_;
v___y_1105_ = v_run_x27_1166_;
v___y_1106_ = v___y_1157_;
v___y_1107_ = v___y_1160_;
v___y_1108_ = v___f_1168_;
v___y_1109_ = v___y_1150_;
goto v___jp_1093_;
}
}
else
{
lean_inc_ref(v_run_x27_1166_);
v___y_1094_ = v_options_1162_;
v___y_1095_ = v___y_1152_;
v___y_1096_ = v___y_1153_;
v___y_1097_ = v___y_1151_;
v___y_1098_ = v___y_1156_;
v___y_1099_ = v___y_1159_;
v___y_1100_ = v___y_1154_;
v___y_1101_ = v___y_1155_;
v___y_1102_ = v___x_1171_;
v___y_1103_ = v_hasTrace_1163_;
v___y_1104_ = v___y_1158_;
v___y_1105_ = v_run_x27_1166_;
v___y_1106_ = v___y_1157_;
v___y_1107_ = v___y_1160_;
v___y_1108_ = v___f_1168_;
v___y_1109_ = v___y_1150_;
goto v___jp_1093_;
}
}
}
}
v___jp_1175_:
{
if (lean_obj_tag(v___y_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1197_; 
v_a_1188_ = lean_ctor_get(v___y_1187_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___y_1187_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1190_ = v___y_1187_;
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___y_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_unbox(v_a_1188_);
lean_dec(v_a_1188_);
if (v___x_1192_ == 0)
{
lean_del_object(v___x_1190_);
v___y_1150_ = v___y_1185_;
v___y_1151_ = v___y_1186_;
v___y_1152_ = v___y_1184_;
v___y_1153_ = v___y_1176_;
v___y_1154_ = v___y_1183_;
v___y_1155_ = v___y_1182_;
v___y_1156_ = v___y_1178_;
v___y_1157_ = v___y_1180_;
v___y_1158_ = v___y_1177_;
v___y_1159_ = v___y_1179_;
v___y_1160_ = v___y_1181_;
goto v___jp_1149_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
v___x_1193_ = lean_box(v_hasTrace_819_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1193_);
v___x_1195_ = v___x_1190_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
return v___y_1187_;
}
}
v___jp_1198_:
{
lean_object* v___x_1217_; double v___x_1218_; double v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1217_ = lean_io_get_num_heartbeats();
v___x_1218_ = lean_float_of_nat(v___y_1210_);
v___x_1219_ = lean_float_of_nat(v___x_1217_);
v___x_1220_ = lean_box_float(v___x_1218_);
v___x_1221_ = lean_box_float(v___x_1219_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_a_1216_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
lean_inc_ref(v___y_1202_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1224_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1213_, v___x_821_, v___y_1203_, v___y_1215_, v___y_1214_, v___y_1202_, v___x_1223_, v___y_1205_, v___y_1206_, v___y_1212_, v___y_1207_, v___y_1204_, v___y_1211_, v___y_1208_, v___y_1209_, v___y_1199_, v___y_1200_, v___y_1201_);
v___y_1176_ = v___y_1207_;
v___y_1177_ = v___y_1199_;
v___y_1178_ = v___y_1208_;
v___y_1179_ = v___y_1200_;
v___y_1180_ = v___y_1209_;
v___y_1181_ = v___y_1201_;
v___y_1182_ = v___y_1211_;
v___y_1183_ = v___y_1204_;
v___y_1184_ = v___y_1212_;
v___y_1185_ = v___y_1205_;
v___y_1186_ = v___y_1206_;
v___y_1187_ = v___x_1224_;
goto v___jp_1175_;
}
v___jp_1225_:
{
lean_object* v___x_1244_; double v___x_1245_; double v___x_1246_; double v___x_1247_; double v___x_1248_; double v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1244_ = lean_io_mono_nanos_now();
v___x_1245_ = lean_float_of_nat(v___y_1238_);
v___x_1246_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1247_ = lean_float_div(v___x_1245_, v___x_1246_);
v___x_1248_ = lean_float_of_nat(v___x_1244_);
v___x_1249_ = lean_float_div(v___x_1248_, v___x_1246_);
v___x_1250_ = lean_box_float(v___x_1247_);
v___x_1251_ = lean_box_float(v___x_1249_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_a_1243_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
lean_inc_ref(v___y_1229_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1254_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1240_, v___x_821_, v___y_1230_, v___y_1242_, v___y_1241_, v___y_1229_, v___x_1253_, v___y_1232_, v___y_1233_, v___y_1239_, v___y_1234_, v___y_1231_, v___y_1237_, v___y_1235_, v___y_1236_, v___y_1226_, v___y_1227_, v___y_1228_);
v___y_1176_ = v___y_1234_;
v___y_1177_ = v___y_1226_;
v___y_1178_ = v___y_1235_;
v___y_1179_ = v___y_1227_;
v___y_1180_ = v___y_1236_;
v___y_1181_ = v___y_1228_;
v___y_1182_ = v___y_1237_;
v___y_1183_ = v___y_1231_;
v___y_1184_ = v___y_1239_;
v___y_1185_ = v___y_1232_;
v___y_1186_ = v___y_1233_;
v___y_1187_ = v___x_1254_;
goto v___jp_1175_;
}
v___jp_1255_:
{
lean_object* v___x_1272_; lean_object* v_a_1273_; uint8_t v___x_1274_; 
v___x_1272_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1258_);
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1261_, v___x_822_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_io_mono_nanos_now();
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
lean_inc(v___y_1256_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1269_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
v___x_1276_ = lean_apply_12(v___y_1264_, v___y_1262_, v___y_1263_, v___y_1269_, v___y_1265_, v___y_1260_, v___y_1268_, v___y_1266_, v___y_1267_, v___y_1256_, v___y_1257_, v___y_1258_, lean_box(0));
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 1);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
v___y_1226_ = v___y_1256_;
v___y_1227_ = v___y_1257_;
v___y_1228_ = v___y_1258_;
v___y_1229_ = v___y_1259_;
v___y_1230_ = v___y_1261_;
v___y_1231_ = v___y_1260_;
v___y_1232_ = v___y_1262_;
v___y_1233_ = v___y_1263_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v___y_1266_;
v___y_1236_ = v___y_1267_;
v___y_1237_ = v___y_1268_;
v___y_1238_ = v___x_1275_;
v___y_1239_ = v___y_1269_;
v___y_1240_ = v___y_1270_;
v___y_1241_ = v_a_1273_;
v___y_1242_ = v___y_1271_;
v_a_1243_ = v___x_1282_;
goto v___jp_1225_;
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1276_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1276_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 0);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
v___y_1226_ = v___y_1256_;
v___y_1227_ = v___y_1257_;
v___y_1228_ = v___y_1258_;
v___y_1229_ = v___y_1259_;
v___y_1230_ = v___y_1261_;
v___y_1231_ = v___y_1260_;
v___y_1232_ = v___y_1262_;
v___y_1233_ = v___y_1263_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v___y_1266_;
v___y_1236_ = v___y_1267_;
v___y_1237_ = v___y_1268_;
v___y_1238_ = v___x_1275_;
v___y_1239_ = v___y_1269_;
v___y_1240_ = v___y_1270_;
v___y_1241_ = v_a_1273_;
v___y_1242_ = v___y_1271_;
v_a_1243_ = v___x_1290_;
goto v___jp_1225_;
}
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
lean_inc(v___y_1256_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1269_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
v___x_1294_ = lean_apply_12(v___y_1264_, v___y_1262_, v___y_1263_, v___y_1269_, v___y_1265_, v___y_1260_, v___y_1268_, v___y_1266_, v___y_1267_, v___y_1256_, v___y_1257_, v___y_1258_, lean_box(0));
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 1);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
v___y_1199_ = v___y_1256_;
v___y_1200_ = v___y_1257_;
v___y_1201_ = v___y_1258_;
v___y_1202_ = v___y_1259_;
v___y_1203_ = v___y_1261_;
v___y_1204_ = v___y_1260_;
v___y_1205_ = v___y_1262_;
v___y_1206_ = v___y_1263_;
v___y_1207_ = v___y_1265_;
v___y_1208_ = v___y_1266_;
v___y_1209_ = v___y_1267_;
v___y_1210_ = v___x_1293_;
v___y_1211_ = v___y_1268_;
v___y_1212_ = v___y_1269_;
v___y_1213_ = v___y_1270_;
v___y_1214_ = v_a_1273_;
v___y_1215_ = v___y_1271_;
v_a_1216_ = v___x_1300_;
goto v___jp_1198_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1294_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1294_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 0);
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v___y_1199_ = v___y_1256_;
v___y_1200_ = v___y_1257_;
v___y_1201_ = v___y_1258_;
v___y_1202_ = v___y_1259_;
v___y_1203_ = v___y_1261_;
v___y_1204_ = v___y_1260_;
v___y_1205_ = v___y_1262_;
v___y_1206_ = v___y_1263_;
v___y_1207_ = v___y_1265_;
v___y_1208_ = v___y_1266_;
v___y_1209_ = v___y_1267_;
v___y_1210_ = v___x_1293_;
v___y_1211_ = v___y_1268_;
v___y_1212_ = v___y_1269_;
v___y_1213_ = v___y_1270_;
v___y_1214_ = v_a_1273_;
v___y_1215_ = v___y_1271_;
v_a_1216_ = v___x_1308_;
goto v___jp_1198_;
}
}
}
}
}
v___jp_1311_:
{
if (v_enums_968_ == 0)
{
v___y_1150_ = v___y_1312_;
v___y_1151_ = v___y_1313_;
v___y_1152_ = v___y_1314_;
v___y_1153_ = v___y_1315_;
v___y_1154_ = v___y_1316_;
v___y_1155_ = v___y_1317_;
v___y_1156_ = v___y_1318_;
v___y_1157_ = v___y_1319_;
v___y_1158_ = v___y_1320_;
v___y_1159_ = v___y_1321_;
v___y_1160_ = v___y_1322_;
goto v___jp_1149_;
}
else
{
lean_object* v___x_1323_; lean_object* v_options_1324_; uint8_t v_hasTrace_1325_; 
v___x_1323_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_options_1324_ = lean_ctor_get(v___y_1321_, 2);
v_hasTrace_1325_ = lean_ctor_get_uint8(v_options_1324_, sizeof(void*)*1);
if (v_hasTrace_1325_ == 0)
{
lean_object* v_run_x27_1326_; lean_object* v___x_1327_; 
v_run_x27_1326_ = lean_ctor_get(v___x_1323_, 1);
lean_inc_ref(v_run_x27_1326_);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
lean_inc(v___y_1314_);
lean_inc(v___y_1313_);
lean_inc_ref(v___y_1312_);
v___x_1327_ = lean_apply_12(v_run_x27_1326_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, lean_box(0));
v___y_1176_ = v___y_1315_;
v___y_1177_ = v___y_1320_;
v___y_1178_ = v___y_1318_;
v___y_1179_ = v___y_1321_;
v___y_1180_ = v___y_1319_;
v___y_1181_ = v___y_1322_;
v___y_1182_ = v___y_1317_;
v___y_1183_ = v___y_1316_;
v___y_1184_ = v___y_1314_;
v___y_1185_ = v___y_1312_;
v___y_1186_ = v___y_1313_;
v___y_1187_ = v___x_1327_;
goto v___jp_1175_;
}
else
{
lean_object* v_run_x27_1328_; lean_object* v_inheritedTraceOptions_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_run_x27_1328_ = lean_ctor_get(v___x_1323_, 1);
v_inheritedTraceOptions_1329_ = lean_ctor_get(v___y_1321_, 13);
v___f_1330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5);
v___x_1331_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_820_);
v___x_1332_ = l_Lean_Name_append(v___x_1331_, v_cls_820_);
v___x_1333_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1329_, v_options_1324_, v___x_1332_);
lean_dec(v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = l_Lean_trace_profiler;
v___x_1335_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1324_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_inc_ref(v_run_x27_1328_);
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
lean_inc(v___y_1314_);
lean_inc(v___y_1313_);
lean_inc_ref(v___y_1312_);
v___x_1336_ = lean_apply_12(v_run_x27_1328_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, lean_box(0));
v___y_1176_ = v___y_1315_;
v___y_1177_ = v___y_1320_;
v___y_1178_ = v___y_1318_;
v___y_1179_ = v___y_1321_;
v___y_1180_ = v___y_1319_;
v___y_1181_ = v___y_1322_;
v___y_1182_ = v___y_1317_;
v___y_1183_ = v___y_1316_;
v___y_1184_ = v___y_1314_;
v___y_1185_ = v___y_1312_;
v___y_1186_ = v___y_1313_;
v___y_1187_ = v___x_1336_;
goto v___jp_1175_;
}
else
{
lean_inc_ref(v_run_x27_1328_);
v___y_1256_ = v___y_1320_;
v___y_1257_ = v___y_1321_;
v___y_1258_ = v___y_1322_;
v___y_1259_ = v___f_1330_;
v___y_1260_ = v___y_1316_;
v___y_1261_ = v_options_1324_;
v___y_1262_ = v___y_1312_;
v___y_1263_ = v___y_1313_;
v___y_1264_ = v_run_x27_1328_;
v___y_1265_ = v___y_1315_;
v___y_1266_ = v___y_1318_;
v___y_1267_ = v___y_1319_;
v___y_1268_ = v___y_1317_;
v___y_1269_ = v___y_1314_;
v___y_1270_ = v_hasTrace_1325_;
v___y_1271_ = v___x_1333_;
goto v___jp_1255_;
}
}
else
{
lean_inc_ref(v_run_x27_1328_);
v___y_1256_ = v___y_1320_;
v___y_1257_ = v___y_1321_;
v___y_1258_ = v___y_1322_;
v___y_1259_ = v___f_1330_;
v___y_1260_ = v___y_1316_;
v___y_1261_ = v_options_1324_;
v___y_1262_ = v___y_1312_;
v___y_1263_ = v___y_1313_;
v___y_1264_ = v_run_x27_1328_;
v___y_1265_ = v___y_1315_;
v___y_1266_ = v___y_1318_;
v___y_1267_ = v___y_1319_;
v___y_1268_ = v___y_1317_;
v___y_1269_ = v___y_1314_;
v___y_1270_ = v_hasTrace_1325_;
v___y_1271_ = v___x_1333_;
goto v___jp_1255_;
}
}
}
}
v___jp_1337_:
{
if (lean_obj_tag(v___y_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1359_; 
v_a_1350_ = lean_ctor_get(v___y_1349_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___y_1349_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1352_ = v___y_1349_;
v_isShared_1353_ = v_isSharedCheck_1359_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___y_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1359_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_unbox(v_a_1350_);
lean_dec(v_a_1350_);
if (v___x_1354_ == 0)
{
lean_del_object(v___x_1352_);
v___y_1312_ = v___y_1348_;
v___y_1313_ = v___y_1345_;
v___y_1314_ = v___y_1342_;
v___y_1315_ = v___y_1339_;
v___y_1316_ = v___y_1347_;
v___y_1317_ = v___y_1341_;
v___y_1318_ = v___y_1338_;
v___y_1319_ = v___y_1340_;
v___y_1320_ = v___y_1346_;
v___y_1321_ = v___y_1344_;
v___y_1322_ = v___y_1343_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
v___x_1355_ = lean_box(v_hasTrace_819_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
return v___y_1349_;
}
}
v___jp_1360_:
{
lean_object* v___x_1379_; double v___x_1380_; double v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1379_ = lean_io_get_num_heartbeats();
v___x_1380_ = lean_float_of_nat(v___y_1365_);
v___x_1381_ = lean_float_of_nat(v___x_1379_);
v___x_1382_ = lean_box_float(v___x_1380_);
v___x_1383_ = lean_box_float(v___x_1381_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_a_1378_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
lean_inc_ref(v___y_1374_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1386_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1372_, v___x_821_, v___y_1369_, v___y_1371_, v___y_1362_, v___y_1374_, v___x_1385_, v___y_1377_, v___y_1375_, v___y_1366_, v___y_1363_, v___y_1370_, v___y_1367_, v___y_1361_, v___y_1364_, v___y_1376_, v___y_1368_, v___y_1373_);
v___y_1338_ = v___y_1361_;
v___y_1339_ = v___y_1363_;
v___y_1340_ = v___y_1364_;
v___y_1341_ = v___y_1367_;
v___y_1342_ = v___y_1366_;
v___y_1343_ = v___y_1373_;
v___y_1344_ = v___y_1368_;
v___y_1345_ = v___y_1375_;
v___y_1346_ = v___y_1376_;
v___y_1347_ = v___y_1370_;
v___y_1348_ = v___y_1377_;
v___y_1349_ = v___x_1386_;
goto v___jp_1337_;
}
v___jp_1387_:
{
lean_object* v___x_1406_; double v___x_1407_; double v___x_1408_; double v___x_1409_; double v___x_1410_; double v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1406_ = lean_io_mono_nanos_now();
v___x_1407_ = lean_float_of_nat(v___y_1403_);
v___x_1408_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1409_ = lean_float_div(v___x_1407_, v___x_1408_);
v___x_1410_ = lean_float_of_nat(v___x_1406_);
v___x_1411_ = lean_float_div(v___x_1410_, v___x_1408_);
v___x_1412_ = lean_box_float(v___x_1409_);
v___x_1413_ = lean_box_float(v___x_1411_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_a_1405_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
lean_inc_ref(v___y_1400_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1416_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1398_, v___x_821_, v___y_1395_, v___y_1397_, v___y_1389_, v___y_1400_, v___x_1415_, v___y_1404_, v___y_1401_, v___y_1392_, v___y_1390_, v___y_1396_, v___y_1393_, v___y_1388_, v___y_1391_, v___y_1402_, v___y_1394_, v___y_1399_);
v___y_1338_ = v___y_1388_;
v___y_1339_ = v___y_1390_;
v___y_1340_ = v___y_1391_;
v___y_1341_ = v___y_1393_;
v___y_1342_ = v___y_1392_;
v___y_1343_ = v___y_1399_;
v___y_1344_ = v___y_1394_;
v___y_1345_ = v___y_1401_;
v___y_1346_ = v___y_1402_;
v___y_1347_ = v___y_1396_;
v___y_1348_ = v___y_1404_;
v___y_1349_ = v___x_1416_;
goto v___jp_1337_;
}
v___jp_1417_:
{
lean_object* v___x_1434_; lean_object* v_a_1435_; uint8_t v___x_1436_; 
v___x_1434_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1429_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1424_, v___x_822_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_io_mono_nanos_now();
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1421_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1420_);
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1433_);
v___x_1438_ = lean_apply_12(v___y_1426_, v___y_1433_, v___y_1431_, v___y_1420_, v___y_1419_, v___y_1425_, v___y_1421_, v___y_1418_, v___y_1422_, v___y_1432_, v___y_1423_, v___y_1429_, lean_box(0));
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 1);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
v___y_1388_ = v___y_1418_;
v___y_1389_ = v_a_1435_;
v___y_1390_ = v___y_1419_;
v___y_1391_ = v___y_1422_;
v___y_1392_ = v___y_1420_;
v___y_1393_ = v___y_1421_;
v___y_1394_ = v___y_1423_;
v___y_1395_ = v___y_1424_;
v___y_1396_ = v___y_1425_;
v___y_1397_ = v___y_1427_;
v___y_1398_ = v___y_1428_;
v___y_1399_ = v___y_1429_;
v___y_1400_ = v___y_1430_;
v___y_1401_ = v___y_1431_;
v___y_1402_ = v___y_1432_;
v___y_1403_ = v___x_1437_;
v___y_1404_ = v___y_1433_;
v_a_1405_ = v___x_1444_;
goto v___jp_1387_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_a_1447_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1438_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1438_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 0);
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v___y_1388_ = v___y_1418_;
v___y_1389_ = v_a_1435_;
v___y_1390_ = v___y_1419_;
v___y_1391_ = v___y_1422_;
v___y_1392_ = v___y_1420_;
v___y_1393_ = v___y_1421_;
v___y_1394_ = v___y_1423_;
v___y_1395_ = v___y_1424_;
v___y_1396_ = v___y_1425_;
v___y_1397_ = v___y_1427_;
v___y_1398_ = v___y_1428_;
v___y_1399_ = v___y_1429_;
v___y_1400_ = v___y_1430_;
v___y_1401_ = v___y_1431_;
v___y_1402_ = v___y_1432_;
v___y_1403_ = v___x_1437_;
v___y_1404_ = v___y_1433_;
v_a_1405_ = v___x_1452_;
goto v___jp_1387_;
}
}
}
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1422_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1421_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1420_);
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1433_);
v___x_1456_ = lean_apply_12(v___y_1426_, v___y_1433_, v___y_1431_, v___y_1420_, v___y_1419_, v___y_1425_, v___y_1421_, v___y_1418_, v___y_1422_, v___y_1432_, v___y_1423_, v___y_1429_, lean_box(0));
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set_tag(v___x_1459_, 1);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
v___y_1361_ = v___y_1418_;
v___y_1362_ = v_a_1435_;
v___y_1363_ = v___y_1419_;
v___y_1364_ = v___y_1422_;
v___y_1365_ = v___x_1455_;
v___y_1366_ = v___y_1420_;
v___y_1367_ = v___y_1421_;
v___y_1368_ = v___y_1423_;
v___y_1369_ = v___y_1424_;
v___y_1370_ = v___y_1425_;
v___y_1371_ = v___y_1427_;
v___y_1372_ = v___y_1428_;
v___y_1373_ = v___y_1429_;
v___y_1374_ = v___y_1430_;
v___y_1375_ = v___y_1431_;
v___y_1376_ = v___y_1432_;
v___y_1377_ = v___y_1433_;
v_a_1378_ = v___x_1462_;
goto v___jp_1360_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1456_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1456_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 0);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
v___y_1361_ = v___y_1418_;
v___y_1362_ = v_a_1435_;
v___y_1363_ = v___y_1419_;
v___y_1364_ = v___y_1422_;
v___y_1365_ = v___x_1455_;
v___y_1366_ = v___y_1420_;
v___y_1367_ = v___y_1421_;
v___y_1368_ = v___y_1423_;
v___y_1369_ = v___y_1424_;
v___y_1370_ = v___y_1425_;
v___y_1371_ = v___y_1427_;
v___y_1372_ = v___y_1428_;
v___y_1373_ = v___y_1429_;
v___y_1374_ = v___y_1430_;
v___y_1375_ = v___y_1431_;
v___y_1376_ = v___y_1432_;
v___y_1377_ = v___y_1433_;
v_a_1378_ = v___x_1470_;
goto v___jp_1360_;
}
}
}
}
}
v___jp_1473_:
{
if (lean_obj_tag(v___y_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1509_; 
v_a_1486_ = lean_ctor_get(v___y_1485_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___y_1485_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1488_ = v___y_1485_;
v_isShared_1489_ = v_isSharedCheck_1509_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___y_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1509_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_unbox(v_a_1486_);
lean_dec(v_a_1486_);
if (v___x_1490_ == 0)
{
lean_del_object(v___x_1488_);
if (v_structures_966_ == 0)
{
v___y_1312_ = v___y_1484_;
v___y_1313_ = v___y_1481_;
v___y_1314_ = v___y_1478_;
v___y_1315_ = v___y_1475_;
v___y_1316_ = v___y_1483_;
v___y_1317_ = v___y_1477_;
v___y_1318_ = v___y_1474_;
v___y_1319_ = v___y_1476_;
v___y_1320_ = v___y_1482_;
v___y_1321_ = v___y_1480_;
v___y_1322_ = v___y_1479_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1491_; lean_object* v_options_1492_; uint8_t v_hasTrace_1493_; 
v___x_1491_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_options_1492_ = lean_ctor_get(v___y_1480_, 2);
v_hasTrace_1493_ = lean_ctor_get_uint8(v_options_1492_, sizeof(void*)*1);
if (v_hasTrace_1493_ == 0)
{
lean_object* v_run_x27_1494_; lean_object* v___x_1495_; 
v_run_x27_1494_ = lean_ctor_get(v___x_1491_, 1);
lean_inc_ref(v_run_x27_1494_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1477_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1475_);
lean_inc(v___y_1478_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1484_);
v___x_1495_ = lean_apply_12(v_run_x27_1494_, v___y_1484_, v___y_1481_, v___y_1478_, v___y_1475_, v___y_1483_, v___y_1477_, v___y_1474_, v___y_1476_, v___y_1482_, v___y_1480_, v___y_1479_, lean_box(0));
v___y_1338_ = v___y_1474_;
v___y_1339_ = v___y_1475_;
v___y_1340_ = v___y_1476_;
v___y_1341_ = v___y_1477_;
v___y_1342_ = v___y_1478_;
v___y_1343_ = v___y_1479_;
v___y_1344_ = v___y_1480_;
v___y_1345_ = v___y_1481_;
v___y_1346_ = v___y_1482_;
v___y_1347_ = v___y_1483_;
v___y_1348_ = v___y_1484_;
v___y_1349_ = v___x_1495_;
goto v___jp_1337_;
}
else
{
lean_object* v_run_x27_1496_; lean_object* v_inheritedTraceOptions_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_run_x27_1496_ = lean_ctor_get(v___x_1491_, 1);
v_inheritedTraceOptions_1497_ = lean_ctor_get(v___y_1480_, 13);
v___f_1498_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6);
v___x_1499_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_820_);
v___x_1500_ = l_Lean_Name_append(v___x_1499_, v_cls_820_);
v___x_1501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1497_, v_options_1492_, v___x_1500_);
lean_dec(v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = l_Lean_trace_profiler;
v___x_1503_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1492_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_inc_ref(v_run_x27_1496_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1477_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1475_);
lean_inc(v___y_1478_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1484_);
v___x_1504_ = lean_apply_12(v_run_x27_1496_, v___y_1484_, v___y_1481_, v___y_1478_, v___y_1475_, v___y_1483_, v___y_1477_, v___y_1474_, v___y_1476_, v___y_1482_, v___y_1480_, v___y_1479_, lean_box(0));
v___y_1338_ = v___y_1474_;
v___y_1339_ = v___y_1475_;
v___y_1340_ = v___y_1476_;
v___y_1341_ = v___y_1477_;
v___y_1342_ = v___y_1478_;
v___y_1343_ = v___y_1479_;
v___y_1344_ = v___y_1480_;
v___y_1345_ = v___y_1481_;
v___y_1346_ = v___y_1482_;
v___y_1347_ = v___y_1483_;
v___y_1348_ = v___y_1484_;
v___y_1349_ = v___x_1504_;
goto v___jp_1337_;
}
else
{
lean_inc_ref(v_run_x27_1496_);
v___y_1418_ = v___y_1474_;
v___y_1419_ = v___y_1475_;
v___y_1420_ = v___y_1478_;
v___y_1421_ = v___y_1477_;
v___y_1422_ = v___y_1476_;
v___y_1423_ = v___y_1480_;
v___y_1424_ = v_options_1492_;
v___y_1425_ = v___y_1483_;
v___y_1426_ = v_run_x27_1496_;
v___y_1427_ = v___x_1501_;
v___y_1428_ = v_hasTrace_1493_;
v___y_1429_ = v___y_1479_;
v___y_1430_ = v___f_1498_;
v___y_1431_ = v___y_1481_;
v___y_1432_ = v___y_1482_;
v___y_1433_ = v___y_1484_;
goto v___jp_1417_;
}
}
else
{
lean_inc_ref(v_run_x27_1496_);
v___y_1418_ = v___y_1474_;
v___y_1419_ = v___y_1475_;
v___y_1420_ = v___y_1478_;
v___y_1421_ = v___y_1477_;
v___y_1422_ = v___y_1476_;
v___y_1423_ = v___y_1480_;
v___y_1424_ = v_options_1492_;
v___y_1425_ = v___y_1483_;
v___y_1426_ = v_run_x27_1496_;
v___y_1427_ = v___x_1501_;
v___y_1428_ = v_hasTrace_1493_;
v___y_1429_ = v___y_1479_;
v___y_1430_ = v___f_1498_;
v___y_1431_ = v___y_1481_;
v___y_1432_ = v___y_1482_;
v___y_1433_ = v___y_1484_;
goto v___jp_1417_;
}
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
v___x_1505_ = lean_box(v_hasTrace_819_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1505_);
v___x_1507_ = v___x_1488_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
return v___y_1485_;
}
}
v___jp_1510_:
{
lean_object* v___x_1529_; double v___x_1530_; double v___x_1531_; double v___x_1532_; double v___x_1533_; double v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1529_ = lean_io_mono_nanos_now();
v___x_1530_ = lean_float_of_nat(v___y_1519_);
v___x_1531_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1532_ = lean_float_div(v___x_1530_, v___x_1531_);
v___x_1533_ = lean_float_of_nat(v___x_1529_);
v___x_1534_ = lean_float_div(v___x_1533_, v___x_1531_);
v___x_1535_ = lean_box_float(v___x_1532_);
v___x_1536_ = lean_box_float(v___x_1534_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_a_1528_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
lean_inc_ref(v___y_1518_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1539_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1511_, v___x_821_, v___y_1523_, v___y_1524_, v___y_1520_, v___y_1518_, v___x_1538_, v___y_1527_, v___y_1525_, v___y_1515_, v___y_1513_, v___y_1521_, v___y_1516_, v___y_1512_, v___y_1514_, v___y_1526_, v___y_1517_, v___y_1522_);
v___y_1474_ = v___y_1512_;
v___y_1475_ = v___y_1513_;
v___y_1476_ = v___y_1514_;
v___y_1477_ = v___y_1516_;
v___y_1478_ = v___y_1515_;
v___y_1479_ = v___y_1522_;
v___y_1480_ = v___y_1517_;
v___y_1481_ = v___y_1525_;
v___y_1482_ = v___y_1526_;
v___y_1483_ = v___y_1521_;
v___y_1484_ = v___y_1527_;
v___y_1485_ = v___x_1539_;
goto v___jp_1473_;
}
v___jp_1540_:
{
lean_object* v___x_1559_; double v___x_1560_; double v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1559_ = lean_io_get_num_heartbeats();
v___x_1560_ = lean_float_of_nat(v___y_1551_);
v___x_1561_ = lean_float_of_nat(v___x_1559_);
v___x_1562_ = lean_box_float(v___x_1560_);
v___x_1563_ = lean_box_float(v___x_1561_);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1558_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
lean_inc_ref(v___y_1548_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1566_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1541_, v___x_821_, v___y_1553_, v___y_1554_, v___y_1549_, v___y_1548_, v___x_1565_, v___y_1557_, v___y_1555_, v___y_1545_, v___y_1543_, v___y_1550_, v___y_1546_, v___y_1542_, v___y_1544_, v___y_1556_, v___y_1547_, v___y_1552_);
v___y_1474_ = v___y_1542_;
v___y_1475_ = v___y_1543_;
v___y_1476_ = v___y_1544_;
v___y_1477_ = v___y_1546_;
v___y_1478_ = v___y_1545_;
v___y_1479_ = v___y_1552_;
v___y_1480_ = v___y_1547_;
v___y_1481_ = v___y_1555_;
v___y_1482_ = v___y_1556_;
v___y_1483_ = v___y_1550_;
v___y_1484_ = v___y_1557_;
v___y_1485_ = v___x_1566_;
goto v___jp_1473_;
}
v___jp_1567_:
{
lean_object* v___x_1584_; lean_object* v_a_1585_; uint8_t v___x_1586_; 
v___x_1584_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1578_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1579_, v___x_822_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_io_mono_nanos_now();
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1571_);
lean_inc(v___y_1572_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1583_);
v___x_1588_ = lean_apply_12(v___y_1570_, v___y_1583_, v___y_1581_, v___y_1572_, v___y_1571_, v___y_1577_, v___y_1573_, v___y_1569_, v___y_1574_, v___y_1582_, v___y_1576_, v___y_1578_, lean_box(0));
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set_tag(v___x_1591_, 1);
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
v___y_1511_ = v___y_1568_;
v___y_1512_ = v___y_1569_;
v___y_1513_ = v___y_1571_;
v___y_1514_ = v___y_1574_;
v___y_1515_ = v___y_1572_;
v___y_1516_ = v___y_1573_;
v___y_1517_ = v___y_1576_;
v___y_1518_ = v___y_1575_;
v___y_1519_ = v___x_1587_;
v___y_1520_ = v_a_1585_;
v___y_1521_ = v___y_1577_;
v___y_1522_ = v___y_1578_;
v___y_1523_ = v___y_1579_;
v___y_1524_ = v___y_1580_;
v___y_1525_ = v___y_1581_;
v___y_1526_ = v___y_1582_;
v___y_1527_ = v___y_1583_;
v_a_1528_ = v___x_1594_;
goto v___jp_1510_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
v_a_1597_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1588_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1588_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 0);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
v___y_1511_ = v___y_1568_;
v___y_1512_ = v___y_1569_;
v___y_1513_ = v___y_1571_;
v___y_1514_ = v___y_1574_;
v___y_1515_ = v___y_1572_;
v___y_1516_ = v___y_1573_;
v___y_1517_ = v___y_1576_;
v___y_1518_ = v___y_1575_;
v___y_1519_ = v___x_1587_;
v___y_1520_ = v_a_1585_;
v___y_1521_ = v___y_1577_;
v___y_1522_ = v___y_1578_;
v___y_1523_ = v___y_1579_;
v___y_1524_ = v___y_1580_;
v___y_1525_ = v___y_1581_;
v___y_1526_ = v___y_1582_;
v___y_1527_ = v___y_1583_;
v_a_1528_ = v___x_1602_;
goto v___jp_1510_;
}
}
}
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1578_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1569_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1571_);
lean_inc(v___y_1572_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1583_);
v___x_1606_ = lean_apply_12(v___y_1570_, v___y_1583_, v___y_1581_, v___y_1572_, v___y_1571_, v___y_1577_, v___y_1573_, v___y_1569_, v___y_1574_, v___y_1582_, v___y_1576_, v___y_1578_, lean_box(0));
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set_tag(v___x_1609_, 1);
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
v___y_1541_ = v___y_1568_;
v___y_1542_ = v___y_1569_;
v___y_1543_ = v___y_1571_;
v___y_1544_ = v___y_1574_;
v___y_1545_ = v___y_1572_;
v___y_1546_ = v___y_1573_;
v___y_1547_ = v___y_1576_;
v___y_1548_ = v___y_1575_;
v___y_1549_ = v_a_1585_;
v___y_1550_ = v___y_1577_;
v___y_1551_ = v___x_1605_;
v___y_1552_ = v___y_1578_;
v___y_1553_ = v___y_1579_;
v___y_1554_ = v___y_1580_;
v___y_1555_ = v___y_1581_;
v___y_1556_ = v___y_1582_;
v___y_1557_ = v___y_1583_;
v_a_1558_ = v___x_1612_;
goto v___jp_1540_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
v_a_1615_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1606_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1606_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 0);
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
v___y_1541_ = v___y_1568_;
v___y_1542_ = v___y_1569_;
v___y_1543_ = v___y_1571_;
v___y_1544_ = v___y_1574_;
v___y_1545_ = v___y_1572_;
v___y_1546_ = v___y_1573_;
v___y_1547_ = v___y_1576_;
v___y_1548_ = v___y_1575_;
v___y_1549_ = v_a_1585_;
v___y_1550_ = v___y_1577_;
v___y_1551_ = v___x_1605_;
v___y_1552_ = v___y_1578_;
v___y_1553_ = v___y_1579_;
v___y_1554_ = v___y_1580_;
v___y_1555_ = v___y_1581_;
v___y_1556_ = v___y_1582_;
v___y_1557_ = v___y_1583_;
v_a_1558_ = v___x_1620_;
goto v___jp_1540_;
}
}
}
}
}
v___jp_1623_:
{
lean_object* v___x_1635_; lean_object* v_options_1636_; uint8_t v_hasTrace_1637_; 
v___x_1635_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v_options_1636_ = lean_ctor_get(v___y_1633_, 2);
v_hasTrace_1637_ = lean_ctor_get_uint8(v_options_1636_, sizeof(void*)*1);
if (v_hasTrace_1637_ == 0)
{
lean_object* v_run_x27_1638_; lean_object* v___x_1639_; 
v_run_x27_1638_ = lean_ctor_get(v___x_1635_, 1);
lean_inc_ref(v_run_x27_1638_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1626_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
v___x_1639_ = lean_apply_12(v_run_x27_1638_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, lean_box(0));
v___y_1474_ = v___y_1630_;
v___y_1475_ = v___y_1627_;
v___y_1476_ = v___y_1631_;
v___y_1477_ = v___y_1629_;
v___y_1478_ = v___y_1626_;
v___y_1479_ = v___y_1634_;
v___y_1480_ = v___y_1633_;
v___y_1481_ = v___y_1625_;
v___y_1482_ = v___y_1632_;
v___y_1483_ = v___y_1628_;
v___y_1484_ = v___y_1624_;
v___y_1485_ = v___x_1639_;
goto v___jp_1473_;
}
else
{
lean_object* v_run_x27_1640_; lean_object* v_inheritedTraceOptions_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v_run_x27_1640_ = lean_ctor_get(v___x_1635_, 1);
v_inheritedTraceOptions_1641_ = lean_ctor_get(v___y_1633_, 13);
v___f_1642_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7);
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_820_);
v___x_1644_ = l_Lean_Name_append(v___x_1643_, v_cls_820_);
v___x_1645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1641_, v_options_1636_, v___x_1644_);
lean_dec(v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = l_Lean_trace_profiler;
v___x_1647_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1636_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_inc_ref(v_run_x27_1640_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1626_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
v___x_1648_ = lean_apply_12(v_run_x27_1640_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, lean_box(0));
v___y_1474_ = v___y_1630_;
v___y_1475_ = v___y_1627_;
v___y_1476_ = v___y_1631_;
v___y_1477_ = v___y_1629_;
v___y_1478_ = v___y_1626_;
v___y_1479_ = v___y_1634_;
v___y_1480_ = v___y_1633_;
v___y_1481_ = v___y_1625_;
v___y_1482_ = v___y_1632_;
v___y_1483_ = v___y_1628_;
v___y_1484_ = v___y_1624_;
v___y_1485_ = v___x_1648_;
goto v___jp_1473_;
}
else
{
lean_inc_ref(v_run_x27_1640_);
v___y_1568_ = v_hasTrace_1637_;
v___y_1569_ = v___y_1630_;
v___y_1570_ = v_run_x27_1640_;
v___y_1571_ = v___y_1627_;
v___y_1572_ = v___y_1626_;
v___y_1573_ = v___y_1629_;
v___y_1574_ = v___y_1631_;
v___y_1575_ = v___f_1642_;
v___y_1576_ = v___y_1633_;
v___y_1577_ = v___y_1628_;
v___y_1578_ = v___y_1634_;
v___y_1579_ = v_options_1636_;
v___y_1580_ = v___x_1645_;
v___y_1581_ = v___y_1625_;
v___y_1582_ = v___y_1632_;
v___y_1583_ = v___y_1624_;
goto v___jp_1567_;
}
}
else
{
lean_inc_ref(v_run_x27_1640_);
v___y_1568_ = v_hasTrace_1637_;
v___y_1569_ = v___y_1630_;
v___y_1570_ = v_run_x27_1640_;
v___y_1571_ = v___y_1627_;
v___y_1572_ = v___y_1626_;
v___y_1573_ = v___y_1629_;
v___y_1574_ = v___y_1631_;
v___y_1575_ = v___f_1642_;
v___y_1576_ = v___y_1633_;
v___y_1577_ = v___y_1628_;
v___y_1578_ = v___y_1634_;
v___y_1579_ = v_options_1636_;
v___y_1580_ = v___x_1645_;
v___y_1581_ = v___y_1625_;
v___y_1582_ = v___y_1632_;
v___y_1583_ = v___y_1624_;
goto v___jp_1567_;
}
}
}
v___jp_1649_:
{
if (lean_obj_tag(v___y_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1660_; 
v_a_1651_ = lean_ctor_get(v___y_1650_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___y_1650_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1653_ = v___y_1650_;
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___y_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_unbox(v_a_1651_);
lean_dec(v_a_1651_);
if (v___x_1655_ == 0)
{
lean_del_object(v___x_1653_);
v___y_1624_ = v___y_824_;
v___y_1625_ = v___y_825_;
v___y_1626_ = v___y_826_;
v___y_1627_ = v___y_827_;
v___y_1628_ = v___y_828_;
v___y_1629_ = v___y_829_;
v___y_1630_ = v___y_830_;
v___y_1631_ = v___y_831_;
v___y_1632_ = v___y_832_;
v___y_1633_ = v___y_833_;
v___y_1634_ = v___y_834_;
goto v___jp_1623_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
v___x_1656_ = lean_box(v_hasTrace_819_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_dec_ref(v___x_821_);
lean_dec(v_cls_820_);
return v___y_1650_;
}
}
v___jp_1661_:
{
lean_object* v___x_1669_; double v___x_1670_; double v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1669_ = lean_io_get_num_heartbeats();
v___x_1670_ = lean_float_of_nat(v___y_1667_);
v___x_1671_ = lean_float_of_nat(v___x_1669_);
v___x_1672_ = lean_box_float(v___x_1670_);
v___x_1673_ = lean_box_float(v___x_1671_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_a_1668_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
lean_inc_ref(v___y_1665_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1676_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1666_, v___x_821_, v___y_1664_, v___y_1663_, v___y_1662_, v___y_1665_, v___x_1675_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
v___y_1650_ = v___x_1676_;
goto v___jp_1649_;
}
v___jp_1677_:
{
lean_object* v___x_1685_; double v___x_1686_; double v___x_1687_; double v___x_1688_; double v___x_1689_; double v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1685_ = lean_io_mono_nanos_now();
v___x_1686_ = lean_float_of_nat(v___y_1682_);
v___x_1687_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1688_ = lean_float_div(v___x_1686_, v___x_1687_);
v___x_1689_ = lean_float_of_nat(v___x_1685_);
v___x_1690_ = lean_float_div(v___x_1689_, v___x_1687_);
v___x_1691_ = lean_box_float(v___x_1688_);
v___x_1692_ = lean_box_float(v___x_1690_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_a_1684_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
lean_inc_ref(v___y_1681_);
lean_inc_ref(v___x_821_);
lean_inc(v_cls_820_);
v___x_1695_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_820_, v___y_1683_, v___x_821_, v___y_1680_, v___y_1679_, v___y_1678_, v___y_1681_, v___x_1694_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
v___y_1650_ = v___x_1695_;
goto v___jp_1649_;
}
v___jp_1696_:
{
lean_object* v___x_1702_; lean_object* v_a_1703_; uint8_t v___x_1704_; 
v___x_1702_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_834_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1698_, v___x_822_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_io_mono_nanos_now();
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
v___x_1706_ = lean_apply_12(v___y_1700_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, lean_box(0));
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 1);
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
v___y_1678_ = v_a_1703_;
v___y_1679_ = v___y_1697_;
v___y_1680_ = v___y_1698_;
v___y_1681_ = v___y_1699_;
v___y_1682_ = v___x_1705_;
v___y_1683_ = v___y_1701_;
v_a_1684_ = v___x_1712_;
goto v___jp_1677_;
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_a_1715_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1706_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1706_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set_tag(v___x_1717_, 0);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
v___y_1678_ = v_a_1703_;
v___y_1679_ = v___y_1697_;
v___y_1680_ = v___y_1698_;
v___y_1681_ = v___y_1699_;
v___y_1682_ = v___x_1705_;
v___y_1683_ = v___y_1701_;
v_a_1684_ = v___x_1720_;
goto v___jp_1677_;
}
}
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_io_get_num_heartbeats();
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
v___x_1724_ = lean_apply_12(v___y_1700_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, lean_box(0));
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 1);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
v___y_1662_ = v_a_1703_;
v___y_1663_ = v___y_1697_;
v___y_1664_ = v___y_1698_;
v___y_1665_ = v___y_1699_;
v___y_1666_ = v___y_1701_;
v___y_1667_ = v___x_1723_;
v_a_1668_ = v___x_1730_;
goto v___jp_1661_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_a_1733_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1724_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1724_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 0);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
v___y_1662_ = v_a_1703_;
v___y_1663_ = v___y_1697_;
v___y_1664_ = v___y_1698_;
v___y_1665_ = v___y_1699_;
v___y_1666_ = v___y_1701_;
v___y_1667_ = v___x_1723_;
v_a_1668_ = v___x_1738_;
goto v___jp_1661_;
}
}
}
}
}
v___jp_1741_:
{
lean_object* v___x_1742_; lean_object* v_options_1743_; uint8_t v_hasTrace_1744_; 
v___x_1742_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_options_1743_ = lean_ctor_get(v___y_833_, 2);
v_hasTrace_1744_ = lean_ctor_get_uint8(v_options_1743_, sizeof(void*)*1);
if (v_hasTrace_1744_ == 0)
{
lean_object* v_run_x27_1745_; lean_object* v___x_1746_; 
v_run_x27_1745_ = lean_ctor_get(v___x_1742_, 1);
lean_inc_ref(v_run_x27_1745_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
v___x_1746_ = lean_apply_12(v_run_x27_1745_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, lean_box(0));
v___y_1650_ = v___x_1746_;
goto v___jp_1649_;
}
else
{
lean_object* v_run_x27_1747_; lean_object* v_inheritedTraceOptions_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_run_x27_1747_ = lean_ctor_get(v___x_1742_, 1);
v_inheritedTraceOptions_1748_ = lean_ctor_get(v___y_833_, 13);
v___f_1749_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8);
v___x_1750_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_820_);
v___x_1751_ = l_Lean_Name_append(v___x_1750_, v_cls_820_);
v___x_1752_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1748_, v_options_1743_, v___x_1751_);
lean_dec(v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = l_Lean_trace_profiler;
v___x_1754_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1743_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
lean_inc_ref(v_run_x27_1747_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
v___x_1755_ = lean_apply_12(v_run_x27_1747_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, lean_box(0));
v___y_1650_ = v___x_1755_;
goto v___jp_1649_;
}
else
{
lean_inc_ref(v_run_x27_1747_);
v___y_1697_ = v___x_1752_;
v___y_1698_ = v_options_1743_;
v___y_1699_ = v___f_1749_;
v___y_1700_ = v_run_x27_1747_;
v___y_1701_ = v_hasTrace_1744_;
goto v___jp_1696_;
}
}
else
{
lean_inc_ref(v_run_x27_1747_);
v___y_1697_ = v___x_1752_;
v___y_1698_ = v_options_1743_;
v___y_1699_ = v___f_1749_;
v___y_1700_ = v_run_x27_1747_;
v___y_1701_ = v_hasTrace_1744_;
goto v___jp_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___boxed(lean_object** _args){
lean_object* v___x_1756_ = _args[0];
lean_object* v_hasTrace_1757_ = _args[1];
lean_object* v_cls_1758_ = _args[2];
lean_object* v___x_1759_ = _args[3];
lean_object* v___x_1760_ = _args[4];
lean_object* v_____r_1761_ = _args[5];
lean_object* v___y_1762_ = _args[6];
lean_object* v___y_1763_ = _args[7];
lean_object* v___y_1764_ = _args[8];
lean_object* v___y_1765_ = _args[9];
lean_object* v___y_1766_ = _args[10];
lean_object* v___y_1767_ = _args[11];
lean_object* v___y_1768_ = _args[12];
lean_object* v___y_1769_ = _args[13];
lean_object* v___y_1770_ = _args[14];
lean_object* v___y_1771_ = _args[15];
lean_object* v___y_1772_ = _args[16];
lean_object* v___y_1773_ = _args[17];
_start:
{
uint8_t v___x_856459__boxed_1774_; uint8_t v_hasTrace_boxed_1775_; lean_object* v_res_1776_; 
v___x_856459__boxed_1774_ = lean_unbox(v___x_1756_);
v_hasTrace_boxed_1775_ = lean_unbox(v_hasTrace_1757_);
v_res_1776_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8(v___x_856459__boxed_1774_, v_hasTrace_boxed_1775_, v_cls_1758_, v___x_1759_, v___x_1760_, v_____r_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v___x_1760_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9(uint8_t v___x_1777_, lean_object* v_cls_1778_, lean_object* v___x_1779_, lean_object* v___x_1780_, lean_object* v_____r_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
uint8_t v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1812_; uint8_t v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; uint8_t v___y_1823_; lean_object* v___y_1824_; uint8_t v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v_a_1830_; lean_object* v___y_1840_; uint8_t v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; lean_object* v___y_1853_; uint8_t v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v_a_1858_; lean_object* v___y_1871_; uint8_t v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v_config_1927_; uint8_t v_structures_1928_; uint8_t v_fixedInt_1929_; uint8_t v_enums_1930_; uint8_t v_shortCircuit_1931_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; lean_object* v___y_2016_; lean_object* v_a_2017_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; uint8_t v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; uint8_t v___y_2045_; lean_object* v___y_2046_; lean_object* v_a_2047_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; uint8_t v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; uint8_t v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; uint8_t v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v_a_2179_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; uint8_t v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; uint8_t v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v_a_2206_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; uint8_t v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; uint8_t v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; uint8_t v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; lean_object* v_a_2341_; uint8_t v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; uint8_t v___y_2366_; lean_object* v___y_2367_; lean_object* v_a_2368_; uint8_t v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; uint8_t v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; uint8_t v___y_2487_; uint8_t v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v_a_2491_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; uint8_t v___y_2516_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v_a_2521_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; uint8_t v___y_2543_; uint8_t v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2613_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; uint8_t v___y_2628_; uint8_t v___y_2629_; lean_object* v___y_2630_; lean_object* v_a_2631_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2645_; uint8_t v___y_2646_; lean_object* v_a_2647_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; uint8_t v___y_2663_; uint8_t v___y_2664_; uint8_t v___y_2705_; 
v_config_1927_ = lean_ctor_get(v___y_1782_, 0);
v_structures_1928_ = lean_ctor_get_uint8(v_config_1927_, sizeof(void*)*2 + 5);
v_fixedInt_1929_ = lean_ctor_get_uint8(v_config_1927_, sizeof(void*)*2 + 6);
v_enums_1930_ = lean_ctor_get_uint8(v_config_1927_, sizeof(void*)*2 + 7);
v_shortCircuit_1931_ = lean_ctor_get_uint8(v_config_1927_, sizeof(void*)*2 + 9);
if (v_structures_1928_ == 0)
{
v___y_2705_ = v_enums_1930_;
goto v___jp_2704_;
}
else
{
v___y_2705_ = v___x_1777_;
goto v___jp_2704_;
}
v___jp_1794_:
{
if (lean_obj_tag(v___y_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1810_; 
v_a_1797_ = lean_ctor_get(v___y_1796_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___y_1796_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1799_ = v___y_1796_;
v_isShared_1800_ = v_isSharedCheck_1810_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___y_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1810_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_unbox(v_a_1797_);
lean_dec(v_a_1797_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(v___y_1795_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1804_ = v___x_1799_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = lean_box(v___x_1777_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1806_);
v___x_1808_ = v___x_1799_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
return v___y_1796_;
}
}
v___jp_1811_:
{
lean_object* v___x_1831_; double v___x_1832_; double v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1831_ = lean_io_get_num_heartbeats();
v___x_1832_ = lean_float_of_nat(v___y_1826_);
v___x_1833_ = lean_float_of_nat(v___x_1831_);
v___x_1834_ = lean_box_float(v___x_1832_);
v___x_1835_ = lean_box_float(v___x_1833_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_a_1830_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
lean_inc_ref(v___y_1821_);
v___x_1838_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_1825_, v___x_1779_, v___y_1827_, v___y_1823_, v___y_1814_, v___y_1821_, v___x_1837_, v___y_1820_, v___y_1817_, v___y_1815_, v___y_1818_, v___y_1816_, v___y_1819_, v___y_1824_, v___y_1822_, v___y_1829_, v___y_1812_, v___y_1828_);
v___y_1795_ = v___y_1813_;
v___y_1796_ = v___x_1838_;
goto v___jp_1794_;
}
v___jp_1839_:
{
lean_object* v___x_1859_; double v___x_1860_; double v___x_1861_; double v___x_1862_; double v___x_1863_; double v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1859_ = lean_io_mono_nanos_now();
v___x_1860_ = lean_float_of_nat(v___y_1850_);
v___x_1861_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_1862_ = lean_float_div(v___x_1860_, v___x_1861_);
v___x_1863_ = lean_float_of_nat(v___x_1859_);
v___x_1864_ = lean_float_div(v___x_1863_, v___x_1861_);
v___x_1865_ = lean_box_float(v___x_1862_);
v___x_1866_ = lean_box_float(v___x_1864_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v_a_1858_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
lean_inc_ref(v___y_1849_);
v___x_1869_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_1854_, v___x_1779_, v___y_1855_, v___y_1852_, v___y_1842_, v___y_1849_, v___x_1868_, v___y_1848_, v___y_1845_, v___y_1843_, v___y_1846_, v___y_1844_, v___y_1847_, v___y_1853_, v___y_1851_, v___y_1857_, v___y_1840_, v___y_1856_);
v___y_1795_ = v___y_1841_;
v___y_1796_ = v___x_1869_;
goto v___jp_1794_;
}
v___jp_1870_:
{
lean_object* v___x_1888_; lean_object* v_a_1889_; uint8_t v___x_1890_; 
v___x_1888_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1887_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_1885_, v___x_1780_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_io_mono_nanos_now();
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1871_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1880_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1877_);
lean_inc(v___y_1874_);
lean_inc_ref(v___y_1876_);
lean_inc(v___y_1873_);
lean_inc(v___y_1875_);
lean_inc_ref(v___y_1878_);
v___x_1892_ = lean_apply_12(v___y_1883_, v___y_1878_, v___y_1875_, v___y_1873_, v___y_1876_, v___y_1874_, v___y_1877_, v___y_1882_, v___y_1880_, v___y_1886_, v___y_1871_, v___y_1887_, lean_box(0));
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
v___y_1840_ = v___y_1871_;
v___y_1841_ = v___y_1872_;
v___y_1842_ = v_a_1889_;
v___y_1843_ = v___y_1873_;
v___y_1844_ = v___y_1874_;
v___y_1845_ = v___y_1875_;
v___y_1846_ = v___y_1876_;
v___y_1847_ = v___y_1877_;
v___y_1848_ = v___y_1878_;
v___y_1849_ = v___y_1879_;
v___y_1850_ = v___x_1891_;
v___y_1851_ = v___y_1880_;
v___y_1852_ = v___y_1881_;
v___y_1853_ = v___y_1882_;
v___y_1854_ = v___y_1884_;
v___y_1855_ = v___y_1885_;
v___y_1856_ = v___y_1887_;
v___y_1857_ = v___y_1886_;
v_a_1858_ = v___x_1898_;
goto v___jp_1839_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1892_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1892_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 0);
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v___y_1840_ = v___y_1871_;
v___y_1841_ = v___y_1872_;
v___y_1842_ = v_a_1889_;
v___y_1843_ = v___y_1873_;
v___y_1844_ = v___y_1874_;
v___y_1845_ = v___y_1875_;
v___y_1846_ = v___y_1876_;
v___y_1847_ = v___y_1877_;
v___y_1848_ = v___y_1878_;
v___y_1849_ = v___y_1879_;
v___y_1850_ = v___x_1891_;
v___y_1851_ = v___y_1880_;
v___y_1852_ = v___y_1881_;
v___y_1853_ = v___y_1882_;
v___y_1854_ = v___y_1884_;
v___y_1855_ = v___y_1885_;
v___y_1856_ = v___y_1887_;
v___y_1857_ = v___y_1886_;
v_a_1858_ = v___x_1906_;
goto v___jp_1839_;
}
}
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1871_);
lean_inc(v___y_1886_);
lean_inc_ref(v___y_1880_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1877_);
lean_inc(v___y_1874_);
lean_inc_ref(v___y_1876_);
lean_inc(v___y_1873_);
lean_inc(v___y_1875_);
lean_inc_ref(v___y_1878_);
v___x_1910_ = lean_apply_12(v___y_1883_, v___y_1878_, v___y_1875_, v___y_1873_, v___y_1876_, v___y_1874_, v___y_1877_, v___y_1882_, v___y_1880_, v___y_1886_, v___y_1871_, v___y_1887_, lean_box(0));
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 1);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
v___y_1812_ = v___y_1871_;
v___y_1813_ = v___y_1872_;
v___y_1814_ = v_a_1889_;
v___y_1815_ = v___y_1873_;
v___y_1816_ = v___y_1874_;
v___y_1817_ = v___y_1875_;
v___y_1818_ = v___y_1876_;
v___y_1819_ = v___y_1877_;
v___y_1820_ = v___y_1878_;
v___y_1821_ = v___y_1879_;
v___y_1822_ = v___y_1880_;
v___y_1823_ = v___y_1881_;
v___y_1824_ = v___y_1882_;
v___y_1825_ = v___y_1884_;
v___y_1826_ = v___x_1909_;
v___y_1827_ = v___y_1885_;
v___y_1828_ = v___y_1887_;
v___y_1829_ = v___y_1886_;
v_a_1830_ = v___x_1916_;
goto v___jp_1811_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1910_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1910_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 0);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
v___y_1812_ = v___y_1871_;
v___y_1813_ = v___y_1872_;
v___y_1814_ = v_a_1889_;
v___y_1815_ = v___y_1873_;
v___y_1816_ = v___y_1874_;
v___y_1817_ = v___y_1875_;
v___y_1818_ = v___y_1876_;
v___y_1819_ = v___y_1877_;
v___y_1820_ = v___y_1878_;
v___y_1821_ = v___y_1879_;
v___y_1822_ = v___y_1880_;
v___y_1823_ = v___y_1881_;
v___y_1824_ = v___y_1882_;
v___y_1825_ = v___y_1884_;
v___y_1826_ = v___x_1909_;
v___y_1827_ = v___y_1885_;
v___y_1828_ = v___y_1887_;
v___y_1829_ = v___y_1886_;
v_a_1830_ = v___x_1924_;
goto v___jp_1811_;
}
}
}
}
}
v___jp_1932_:
{
lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1946_; 
v___x_1944_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_1933_);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_1945_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v_a_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; uint8_t v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
v___x_1948_ = lean_unbox(v_a_1947_);
if (v___x_1948_ == 0)
{
if (v_shortCircuit_1931_ == 0)
{
lean_dec(v_a_1947_);
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
return v___x_1946_;
}
else
{
lean_object* v___x_1949_; lean_object* v_options_1950_; uint8_t v_hasTrace_1951_; 
lean_dec_ref_known(v___x_1946_, 1);
v___x_1949_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_options_1950_ = lean_ctor_get(v___y_1942_, 2);
v_hasTrace_1951_ = lean_ctor_get_uint8(v_options_1950_, sizeof(void*)*1);
if (v_hasTrace_1951_ == 0)
{
lean_object* v_run_x27_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
v_run_x27_1952_ = lean_ctor_get(v___x_1949_, 1);
lean_inc_ref(v_run_x27_1952_);
lean_inc(v___y_1943_);
lean_inc_ref(v___y_1942_);
lean_inc(v___y_1941_);
lean_inc_ref(v___y_1940_);
lean_inc(v___y_1939_);
lean_inc_ref(v___y_1938_);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1936_);
lean_inc(v___y_1935_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
v___x_1953_ = lean_apply_12(v_run_x27_1952_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, lean_box(0));
v___x_1954_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
v___y_1795_ = v___x_1954_;
v___y_1796_ = v___x_1953_;
goto v___jp_1794_;
}
else
{
lean_object* v_run_x27_1955_; lean_object* v_inheritedTraceOptions_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_run_x27_1955_ = lean_ctor_get(v___x_1949_, 1);
v_inheritedTraceOptions_1956_ = lean_ctor_get(v___y_1942_, 13);
v___f_1957_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1);
v___x_1958_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1778_);
v___x_1959_ = l_Lean_Name_append(v___x_1958_, v_cls_1778_);
v___x_1960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1956_, v_options_1950_, v___x_1959_);
lean_dec(v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = l_Lean_trace_profiler;
v___x_1962_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_1950_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
lean_inc_ref(v_run_x27_1955_);
lean_inc(v___y_1943_);
lean_inc_ref(v___y_1942_);
lean_inc(v___y_1941_);
lean_inc_ref(v___y_1940_);
lean_inc(v___y_1939_);
lean_inc_ref(v___y_1938_);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1936_);
lean_inc(v___y_1935_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
v___x_1963_ = lean_apply_12(v_run_x27_1955_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, lean_box(0));
v___x_1964_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
v___y_1795_ = v___x_1964_;
v___y_1796_ = v___x_1963_;
goto v___jp_1794_;
}
else
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
lean_inc_ref(v_run_x27_1955_);
v___y_1871_ = v___y_1942_;
v___y_1872_ = v___x_1965_;
v___y_1873_ = v___y_1935_;
v___y_1874_ = v___y_1937_;
v___y_1875_ = v___y_1934_;
v___y_1876_ = v___y_1936_;
v___y_1877_ = v___y_1938_;
v___y_1878_ = v___y_1933_;
v___y_1879_ = v___f_1957_;
v___y_1880_ = v___y_1940_;
v___y_1881_ = v___x_1960_;
v___y_1882_ = v___y_1939_;
v___y_1883_ = v_run_x27_1955_;
v___y_1884_ = v_hasTrace_1951_;
v___y_1885_ = v_options_1950_;
v___y_1886_ = v___y_1941_;
v___y_1887_ = v___y_1943_;
goto v___jp_1870_;
}
}
else
{
uint8_t v___x_1966_; 
v___x_1966_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
lean_inc_ref(v_run_x27_1955_);
v___y_1871_ = v___y_1942_;
v___y_1872_ = v___x_1966_;
v___y_1873_ = v___y_1935_;
v___y_1874_ = v___y_1937_;
v___y_1875_ = v___y_1934_;
v___y_1876_ = v___y_1936_;
v___y_1877_ = v___y_1938_;
v___y_1878_ = v___y_1933_;
v___y_1879_ = v___f_1957_;
v___y_1880_ = v___y_1940_;
v___y_1881_ = v___x_1960_;
v___y_1882_ = v___y_1939_;
v___y_1883_ = v_run_x27_1955_;
v___y_1884_ = v_hasTrace_1951_;
v___y_1885_ = v_options_1950_;
v___y_1886_ = v___y_1941_;
v___y_1887_ = v___y_1943_;
goto v___jp_1870_;
}
}
}
}
else
{
lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_a_1947_);
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1946_, 0);
lean_dec(v_unused_1975_);
v___x_1968_ = v___x_1946_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v___x_1946_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_box(v___x_1777_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
return v___x_1946_;
}
}
v___jp_1976_:
{
if (lean_obj_tag(v___y_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1998_; 
v_a_1989_ = lean_ctor_get(v___y_1988_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___y_1988_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1991_ = v___y_1988_;
v_isShared_1992_ = v_isSharedCheck_1998_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___y_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1998_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_unbox(v_a_1989_);
lean_dec(v_a_1989_);
if (v___x_1993_ == 0)
{
lean_del_object(v___x_1991_);
v___y_1933_ = v___y_1979_;
v___y_1934_ = v___y_1986_;
v___y_1935_ = v___y_1978_;
v___y_1936_ = v___y_1980_;
v___y_1937_ = v___y_1982_;
v___y_1938_ = v___y_1977_;
v___y_1939_ = v___y_1983_;
v___y_1940_ = v___y_1984_;
v___y_1941_ = v___y_1987_;
v___y_1942_ = v___y_1985_;
v___y_1943_ = v___y_1981_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
v___x_1994_ = lean_box(v___x_1777_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1994_);
v___x_1996_ = v___x_1991_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
return v___y_1988_;
}
}
v___jp_1999_:
{
lean_object* v___x_2018_; double v___x_2019_; double v___x_2020_; double v___x_2021_; double v___x_2022_; double v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2018_ = lean_io_mono_nanos_now();
v___x_2019_ = lean_float_of_nat(v___y_2007_);
v___x_2020_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2021_ = lean_float_div(v___x_2019_, v___x_2020_);
v___x_2022_ = lean_float_of_nat(v___x_2018_);
v___x_2023_ = lean_float_div(v___x_2022_, v___x_2020_);
v___x_2024_ = lean_box_float(v___x_2021_);
v___x_2025_ = lean_box_float(v___x_2023_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_a_2017_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
lean_inc_ref(v___y_2016_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2028_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2012_, v___x_1779_, v___y_2010_, v___y_2015_, v___y_2008_, v___y_2016_, v___x_2027_, v___y_2009_, v___y_2014_, v___y_2006_, v___y_2001_, v___y_2011_, v___y_2000_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2013_, v___y_2002_);
v___y_1977_ = v___y_2000_;
v___y_1978_ = v___y_2006_;
v___y_1979_ = v___y_2009_;
v___y_1980_ = v___y_2001_;
v___y_1981_ = v___y_2002_;
v___y_1982_ = v___y_2011_;
v___y_1983_ = v___y_2003_;
v___y_1984_ = v___y_2004_;
v___y_1985_ = v___y_2013_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2005_;
v___y_1988_ = v___x_2028_;
goto v___jp_1976_;
}
v___jp_2029_:
{
lean_object* v___x_2048_; double v___x_2049_; double v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2048_ = lean_io_get_num_heartbeats();
v___x_2049_ = lean_float_of_nat(v___y_2030_);
v___x_2050_ = lean_float_of_nat(v___x_2048_);
v___x_2051_ = lean_box_float(v___x_2049_);
v___x_2052_ = lean_box_float(v___x_2050_);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_a_2047_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_inc_ref(v___y_2046_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2055_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2042_, v___x_1779_, v___y_2040_, v___y_2045_, v___y_2038_, v___y_2046_, v___x_2054_, v___y_2039_, v___y_2044_, v___y_2037_, v___y_2032_, v___y_2041_, v___y_2031_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2043_, v___y_2033_);
v___y_1977_ = v___y_2031_;
v___y_1978_ = v___y_2037_;
v___y_1979_ = v___y_2039_;
v___y_1980_ = v___y_2032_;
v___y_1981_ = v___y_2033_;
v___y_1982_ = v___y_2041_;
v___y_1983_ = v___y_2034_;
v___y_1984_ = v___y_2035_;
v___y_1985_ = v___y_2043_;
v___y_1986_ = v___y_2044_;
v___y_1987_ = v___y_2036_;
v___y_1988_ = v___x_2055_;
goto v___jp_1976_;
}
v___jp_2056_:
{
lean_object* v___x_2073_; lean_object* v_a_2074_; uint8_t v___x_2075_; 
v___x_2073_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2059_);
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2073_);
v___x_2075_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2066_, v___x_1780_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_io_mono_nanos_now();
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2062_);
lean_inc_ref(v___y_2061_);
lean_inc(v___y_2060_);
lean_inc_ref(v___y_2057_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2064_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2065_);
v___x_2077_ = lean_apply_12(v___y_2063_, v___y_2065_, v___y_2070_, v___y_2064_, v___y_2058_, v___y_2067_, v___y_2057_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2069_, v___y_2059_, lean_box(0));
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 1);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
v___y_2000_ = v___y_2057_;
v___y_2001_ = v___y_2058_;
v___y_2002_ = v___y_2059_;
v___y_2003_ = v___y_2060_;
v___y_2004_ = v___y_2061_;
v___y_2005_ = v___y_2062_;
v___y_2006_ = v___y_2064_;
v___y_2007_ = v___x_2076_;
v___y_2008_ = v_a_2074_;
v___y_2009_ = v___y_2065_;
v___y_2010_ = v___y_2066_;
v___y_2011_ = v___y_2067_;
v___y_2012_ = v___y_2068_;
v___y_2013_ = v___y_2069_;
v___y_2014_ = v___y_2070_;
v___y_2015_ = v___y_2071_;
v___y_2016_ = v___y_2072_;
v_a_2017_ = v___x_2083_;
goto v___jp_1999_;
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
v_a_2086_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2077_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2077_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 0);
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
v___y_2000_ = v___y_2057_;
v___y_2001_ = v___y_2058_;
v___y_2002_ = v___y_2059_;
v___y_2003_ = v___y_2060_;
v___y_2004_ = v___y_2061_;
v___y_2005_ = v___y_2062_;
v___y_2006_ = v___y_2064_;
v___y_2007_ = v___x_2076_;
v___y_2008_ = v_a_2074_;
v___y_2009_ = v___y_2065_;
v___y_2010_ = v___y_2066_;
v___y_2011_ = v___y_2067_;
v___y_2012_ = v___y_2068_;
v___y_2013_ = v___y_2069_;
v___y_2014_ = v___y_2070_;
v___y_2015_ = v___y_2071_;
v___y_2016_ = v___y_2072_;
v_a_2017_ = v___x_2091_;
goto v___jp_1999_;
}
}
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2062_);
lean_inc_ref(v___y_2061_);
lean_inc(v___y_2060_);
lean_inc_ref(v___y_2057_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2064_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2065_);
v___x_2095_ = lean_apply_12(v___y_2063_, v___y_2065_, v___y_2070_, v___y_2064_, v___y_2058_, v___y_2067_, v___y_2057_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2069_, v___y_2059_, lean_box(0));
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 1);
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
v___y_2030_ = v___x_2094_;
v___y_2031_ = v___y_2057_;
v___y_2032_ = v___y_2058_;
v___y_2033_ = v___y_2059_;
v___y_2034_ = v___y_2060_;
v___y_2035_ = v___y_2061_;
v___y_2036_ = v___y_2062_;
v___y_2037_ = v___y_2064_;
v___y_2038_ = v_a_2074_;
v___y_2039_ = v___y_2065_;
v___y_2040_ = v___y_2066_;
v___y_2041_ = v___y_2067_;
v___y_2042_ = v___y_2068_;
v___y_2043_ = v___y_2069_;
v___y_2044_ = v___y_2070_;
v___y_2045_ = v___y_2071_;
v___y_2046_ = v___y_2072_;
v_a_2047_ = v___x_2101_;
goto v___jp_2029_;
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
v_a_2104_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2095_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2095_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 0);
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
v___y_2030_ = v___x_2094_;
v___y_2031_ = v___y_2057_;
v___y_2032_ = v___y_2058_;
v___y_2033_ = v___y_2059_;
v___y_2034_ = v___y_2060_;
v___y_2035_ = v___y_2061_;
v___y_2036_ = v___y_2062_;
v___y_2037_ = v___y_2064_;
v___y_2038_ = v_a_2074_;
v___y_2039_ = v___y_2065_;
v___y_2040_ = v___y_2066_;
v___y_2041_ = v___y_2067_;
v___y_2042_ = v___y_2068_;
v___y_2043_ = v___y_2069_;
v___y_2044_ = v___y_2070_;
v___y_2045_ = v___y_2071_;
v___y_2046_ = v___y_2072_;
v_a_2047_ = v___x_2109_;
goto v___jp_2029_;
}
}
}
}
}
v___jp_2112_:
{
if (v_fixedInt_1929_ == 0)
{
v___y_1933_ = v___y_2113_;
v___y_1934_ = v___y_2114_;
v___y_1935_ = v___y_2115_;
v___y_1936_ = v___y_2116_;
v___y_1937_ = v___y_2117_;
v___y_1938_ = v___y_2118_;
v___y_1939_ = v___y_2119_;
v___y_1940_ = v___y_2120_;
v___y_1941_ = v___y_2121_;
v___y_1942_ = v___y_2122_;
v___y_1943_ = v___y_2123_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_2124_; lean_object* v_options_2125_; uint8_t v_hasTrace_2126_; 
v___x_2124_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_options_2125_ = lean_ctor_get(v___y_2122_, 2);
v_hasTrace_2126_ = lean_ctor_get_uint8(v_options_2125_, sizeof(void*)*1);
if (v_hasTrace_2126_ == 0)
{
lean_object* v_run_x27_2127_; lean_object* v___x_2128_; 
v_run_x27_2127_ = lean_ctor_get(v___x_2124_, 1);
lean_inc_ref(v_run_x27_2127_);
lean_inc(v___y_2123_);
lean_inc_ref(v___y_2122_);
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
v___x_2128_ = lean_apply_12(v_run_x27_2127_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, lean_box(0));
v___y_1977_ = v___y_2118_;
v___y_1978_ = v___y_2115_;
v___y_1979_ = v___y_2113_;
v___y_1980_ = v___y_2116_;
v___y_1981_ = v___y_2123_;
v___y_1982_ = v___y_2117_;
v___y_1983_ = v___y_2119_;
v___y_1984_ = v___y_2120_;
v___y_1985_ = v___y_2122_;
v___y_1986_ = v___y_2114_;
v___y_1987_ = v___y_2121_;
v___y_1988_ = v___x_2128_;
goto v___jp_1976_;
}
else
{
lean_object* v_run_x27_2129_; lean_object* v_inheritedTraceOptions_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v_run_x27_2129_ = lean_ctor_get(v___x_2124_, 1);
v_inheritedTraceOptions_2130_ = lean_ctor_get(v___y_2122_, 13);
v___f_2131_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4);
v___x_2132_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1778_);
v___x_2133_ = l_Lean_Name_append(v___x_2132_, v_cls_1778_);
v___x_2134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2130_, v_options_2125_, v___x_2133_);
lean_dec(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = l_Lean_trace_profiler;
v___x_2136_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2125_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_inc_ref(v_run_x27_2129_);
lean_inc(v___y_2123_);
lean_inc_ref(v___y_2122_);
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___y_2117_);
lean_inc_ref(v___y_2116_);
lean_inc(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
v___x_2137_ = lean_apply_12(v_run_x27_2129_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, lean_box(0));
v___y_1977_ = v___y_2118_;
v___y_1978_ = v___y_2115_;
v___y_1979_ = v___y_2113_;
v___y_1980_ = v___y_2116_;
v___y_1981_ = v___y_2123_;
v___y_1982_ = v___y_2117_;
v___y_1983_ = v___y_2119_;
v___y_1984_ = v___y_2120_;
v___y_1985_ = v___y_2122_;
v___y_1986_ = v___y_2114_;
v___y_1987_ = v___y_2121_;
v___y_1988_ = v___x_2137_;
goto v___jp_1976_;
}
else
{
lean_inc_ref(v_run_x27_2129_);
v___y_2057_ = v___y_2118_;
v___y_2058_ = v___y_2116_;
v___y_2059_ = v___y_2123_;
v___y_2060_ = v___y_2119_;
v___y_2061_ = v___y_2120_;
v___y_2062_ = v___y_2121_;
v___y_2063_ = v_run_x27_2129_;
v___y_2064_ = v___y_2115_;
v___y_2065_ = v___y_2113_;
v___y_2066_ = v_options_2125_;
v___y_2067_ = v___y_2117_;
v___y_2068_ = v_hasTrace_2126_;
v___y_2069_ = v___y_2122_;
v___y_2070_ = v___y_2114_;
v___y_2071_ = v___x_2134_;
v___y_2072_ = v___f_2131_;
goto v___jp_2056_;
}
}
else
{
lean_inc_ref(v_run_x27_2129_);
v___y_2057_ = v___y_2118_;
v___y_2058_ = v___y_2116_;
v___y_2059_ = v___y_2123_;
v___y_2060_ = v___y_2119_;
v___y_2061_ = v___y_2120_;
v___y_2062_ = v___y_2121_;
v___y_2063_ = v_run_x27_2129_;
v___y_2064_ = v___y_2115_;
v___y_2065_ = v___y_2113_;
v___y_2066_ = v_options_2125_;
v___y_2067_ = v___y_2117_;
v___y_2068_ = v_hasTrace_2126_;
v___y_2069_ = v___y_2122_;
v___y_2070_ = v___y_2114_;
v___y_2071_ = v___x_2134_;
v___y_2072_ = v___f_2131_;
goto v___jp_2056_;
}
}
}
}
v___jp_2138_:
{
if (lean_obj_tag(v___y_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2160_; 
v_a_2151_ = lean_ctor_get(v___y_2150_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___y_2150_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2153_ = v___y_2150_;
v_isShared_2154_ = v_isSharedCheck_2160_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___y_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2160_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_unbox(v_a_2151_);
lean_dec(v_a_2151_);
if (v___x_2155_ == 0)
{
lean_del_object(v___x_2153_);
v___y_2113_ = v___y_2140_;
v___y_2114_ = v___y_2139_;
v___y_2115_ = v___y_2142_;
v___y_2116_ = v___y_2143_;
v___y_2117_ = v___y_2145_;
v___y_2118_ = v___y_2147_;
v___y_2119_ = v___y_2141_;
v___y_2120_ = v___y_2144_;
v___y_2121_ = v___y_2146_;
v___y_2122_ = v___y_2149_;
v___y_2123_ = v___y_2148_;
goto v___jp_2112_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
v___x_2156_ = lean_box(v___x_1777_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2156_);
v___x_2158_ = v___x_2153_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
return v___y_2150_;
}
}
v___jp_2161_:
{
lean_object* v___x_2180_; double v___x_2181_; double v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2180_ = lean_io_get_num_heartbeats();
v___x_2181_ = lean_float_of_nat(v___y_2162_);
v___x_2182_ = lean_float_of_nat(v___x_2180_);
v___x_2183_ = lean_box_float(v___x_2181_);
v___x_2184_ = lean_box_float(v___x_2182_);
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2179_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
lean_inc_ref(v___y_2163_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2187_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2168_, v___x_1779_, v___y_2174_, v___y_2172_, v___y_2173_, v___y_2163_, v___x_2186_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2175_, v___y_2167_, v___y_2169_, v___y_2171_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2170_);
v___y_2139_ = v___y_2165_;
v___y_2140_ = v___y_2164_;
v___y_2141_ = v___y_2171_;
v___y_2142_ = v___y_2166_;
v___y_2143_ = v___y_2175_;
v___y_2144_ = v___y_2176_;
v___y_2145_ = v___y_2167_;
v___y_2146_ = v___y_2177_;
v___y_2147_ = v___y_2169_;
v___y_2148_ = v___y_2170_;
v___y_2149_ = v___y_2178_;
v___y_2150_ = v___x_2187_;
goto v___jp_2138_;
}
v___jp_2188_:
{
lean_object* v___x_2207_; double v___x_2208_; double v___x_2209_; double v___x_2210_; double v___x_2211_; double v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2207_ = lean_io_mono_nanos_now();
v___x_2208_ = lean_float_of_nat(v___y_2192_);
v___x_2209_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2210_ = lean_float_div(v___x_2208_, v___x_2209_);
v___x_2211_ = lean_float_of_nat(v___x_2207_);
v___x_2212_ = lean_float_div(v___x_2211_, v___x_2209_);
v___x_2213_ = lean_box_float(v___x_2210_);
v___x_2214_ = lean_box_float(v___x_2212_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_a_2206_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
lean_inc_ref(v___y_2189_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2217_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2195_, v___x_1779_, v___y_2201_, v___y_2199_, v___y_2200_, v___y_2189_, v___x_2216_, v___y_2190_, v___y_2191_, v___y_2193_, v___y_2202_, v___y_2194_, v___y_2196_, v___y_2198_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2197_);
v___y_2139_ = v___y_2191_;
v___y_2140_ = v___y_2190_;
v___y_2141_ = v___y_2198_;
v___y_2142_ = v___y_2193_;
v___y_2143_ = v___y_2202_;
v___y_2144_ = v___y_2203_;
v___y_2145_ = v___y_2194_;
v___y_2146_ = v___y_2204_;
v___y_2147_ = v___y_2196_;
v___y_2148_ = v___y_2197_;
v___y_2149_ = v___y_2205_;
v___y_2150_ = v___x_2217_;
goto v___jp_2138_;
}
v___jp_2218_:
{
lean_object* v___x_2235_; lean_object* v_a_2236_; uint8_t v___x_2237_; 
v___x_2235_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2226_);
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2230_, v___x_1780_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_io_mono_nanos_now();
lean_inc(v___y_2226_);
lean_inc_ref(v___y_2234_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
lean_inc(v___y_2228_);
lean_inc_ref(v___y_2225_);
lean_inc(v___y_2223_);
lean_inc_ref(v___y_2231_);
lean_inc(v___y_2222_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
v___x_2239_ = lean_apply_12(v___y_2227_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2231_, v___y_2223_, v___y_2225_, v___y_2228_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2226_, lean_box(0));
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 1);
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
v___y_2189_ = v___y_2219_;
v___y_2190_ = v___y_2220_;
v___y_2191_ = v___y_2221_;
v___y_2192_ = v___x_2238_;
v___y_2193_ = v___y_2222_;
v___y_2194_ = v___y_2223_;
v___y_2195_ = v___y_2224_;
v___y_2196_ = v___y_2225_;
v___y_2197_ = v___y_2226_;
v___y_2198_ = v___y_2228_;
v___y_2199_ = v___y_2229_;
v___y_2200_ = v_a_2236_;
v___y_2201_ = v___y_2230_;
v___y_2202_ = v___y_2231_;
v___y_2203_ = v___y_2232_;
v___y_2204_ = v___y_2233_;
v___y_2205_ = v___y_2234_;
v_a_2206_ = v___x_2245_;
goto v___jp_2188_;
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_a_2248_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2239_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2239_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set_tag(v___x_2250_, 0);
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
v___y_2189_ = v___y_2219_;
v___y_2190_ = v___y_2220_;
v___y_2191_ = v___y_2221_;
v___y_2192_ = v___x_2238_;
v___y_2193_ = v___y_2222_;
v___y_2194_ = v___y_2223_;
v___y_2195_ = v___y_2224_;
v___y_2196_ = v___y_2225_;
v___y_2197_ = v___y_2226_;
v___y_2198_ = v___y_2228_;
v___y_2199_ = v___y_2229_;
v___y_2200_ = v_a_2236_;
v___y_2201_ = v___y_2230_;
v___y_2202_ = v___y_2231_;
v___y_2203_ = v___y_2232_;
v___y_2204_ = v___y_2233_;
v___y_2205_ = v___y_2234_;
v_a_2206_ = v___x_2253_;
goto v___jp_2188_;
}
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2226_);
lean_inc_ref(v___y_2234_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
lean_inc(v___y_2228_);
lean_inc_ref(v___y_2225_);
lean_inc(v___y_2223_);
lean_inc_ref(v___y_2231_);
lean_inc(v___y_2222_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
v___x_2257_ = lean_apply_12(v___y_2227_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2231_, v___y_2223_, v___y_2225_, v___y_2228_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2226_, lean_box(0));
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
lean_ctor_set_tag(v___x_2260_, 1);
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
v___y_2162_ = v___x_2256_;
v___y_2163_ = v___y_2219_;
v___y_2164_ = v___y_2220_;
v___y_2165_ = v___y_2221_;
v___y_2166_ = v___y_2222_;
v___y_2167_ = v___y_2223_;
v___y_2168_ = v___y_2224_;
v___y_2169_ = v___y_2225_;
v___y_2170_ = v___y_2226_;
v___y_2171_ = v___y_2228_;
v___y_2172_ = v___y_2229_;
v___y_2173_ = v_a_2236_;
v___y_2174_ = v___y_2230_;
v___y_2175_ = v___y_2231_;
v___y_2176_ = v___y_2232_;
v___y_2177_ = v___y_2233_;
v___y_2178_ = v___y_2234_;
v_a_2179_ = v___x_2263_;
goto v___jp_2161_;
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_a_2266_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2257_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2257_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set_tag(v___x_2268_, 0);
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
v___y_2162_ = v___x_2256_;
v___y_2163_ = v___y_2219_;
v___y_2164_ = v___y_2220_;
v___y_2165_ = v___y_2221_;
v___y_2166_ = v___y_2222_;
v___y_2167_ = v___y_2223_;
v___y_2168_ = v___y_2224_;
v___y_2169_ = v___y_2225_;
v___y_2170_ = v___y_2226_;
v___y_2171_ = v___y_2228_;
v___y_2172_ = v___y_2229_;
v___y_2173_ = v_a_2236_;
v___y_2174_ = v___y_2230_;
v___y_2175_ = v___y_2231_;
v___y_2176_ = v___y_2232_;
v___y_2177_ = v___y_2233_;
v___y_2178_ = v___y_2234_;
v_a_2179_ = v___x_2271_;
goto v___jp_2161_;
}
}
}
}
}
v___jp_2274_:
{
if (v_enums_1930_ == 0)
{
v___y_2113_ = v___y_2275_;
v___y_2114_ = v___y_2276_;
v___y_2115_ = v___y_2277_;
v___y_2116_ = v___y_2278_;
v___y_2117_ = v___y_2279_;
v___y_2118_ = v___y_2280_;
v___y_2119_ = v___y_2281_;
v___y_2120_ = v___y_2282_;
v___y_2121_ = v___y_2283_;
v___y_2122_ = v___y_2284_;
v___y_2123_ = v___y_2285_;
goto v___jp_2112_;
}
else
{
lean_object* v___x_2286_; lean_object* v_options_2287_; uint8_t v_hasTrace_2288_; 
v___x_2286_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_options_2287_ = lean_ctor_get(v___y_2284_, 2);
v_hasTrace_2288_ = lean_ctor_get_uint8(v_options_2287_, sizeof(void*)*1);
if (v_hasTrace_2288_ == 0)
{
lean_object* v_run_x27_2289_; lean_object* v___x_2290_; 
v_run_x27_2289_ = lean_ctor_get(v___x_2286_, 1);
lean_inc_ref(v_run_x27_2289_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2284_);
lean_inc(v___y_2283_);
lean_inc_ref(v___y_2282_);
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc(v___y_2276_);
lean_inc_ref(v___y_2275_);
v___x_2290_ = lean_apply_12(v_run_x27_2289_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, lean_box(0));
v___y_2139_ = v___y_2276_;
v___y_2140_ = v___y_2275_;
v___y_2141_ = v___y_2281_;
v___y_2142_ = v___y_2277_;
v___y_2143_ = v___y_2278_;
v___y_2144_ = v___y_2282_;
v___y_2145_ = v___y_2279_;
v___y_2146_ = v___y_2283_;
v___y_2147_ = v___y_2280_;
v___y_2148_ = v___y_2285_;
v___y_2149_ = v___y_2284_;
v___y_2150_ = v___x_2290_;
goto v___jp_2138_;
}
else
{
lean_object* v_run_x27_2291_; lean_object* v_inheritedTraceOptions_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v_run_x27_2291_ = lean_ctor_get(v___x_2286_, 1);
v_inheritedTraceOptions_2292_ = lean_ctor_get(v___y_2284_, 13);
v___f_2293_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5);
v___x_2294_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1778_);
v___x_2295_ = l_Lean_Name_append(v___x_2294_, v_cls_1778_);
v___x_2296_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2292_, v_options_2287_, v___x_2295_);
lean_dec(v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = l_Lean_trace_profiler;
v___x_2298_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2287_, v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; 
lean_inc_ref(v_run_x27_2291_);
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2284_);
lean_inc(v___y_2283_);
lean_inc_ref(v___y_2282_);
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc(v___y_2276_);
lean_inc_ref(v___y_2275_);
v___x_2299_ = lean_apply_12(v_run_x27_2291_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, lean_box(0));
v___y_2139_ = v___y_2276_;
v___y_2140_ = v___y_2275_;
v___y_2141_ = v___y_2281_;
v___y_2142_ = v___y_2277_;
v___y_2143_ = v___y_2278_;
v___y_2144_ = v___y_2282_;
v___y_2145_ = v___y_2279_;
v___y_2146_ = v___y_2283_;
v___y_2147_ = v___y_2280_;
v___y_2148_ = v___y_2285_;
v___y_2149_ = v___y_2284_;
v___y_2150_ = v___x_2299_;
goto v___jp_2138_;
}
else
{
lean_inc_ref(v_run_x27_2291_);
v___y_2219_ = v___f_2293_;
v___y_2220_ = v___y_2275_;
v___y_2221_ = v___y_2276_;
v___y_2222_ = v___y_2277_;
v___y_2223_ = v___y_2279_;
v___y_2224_ = v_hasTrace_2288_;
v___y_2225_ = v___y_2280_;
v___y_2226_ = v___y_2285_;
v___y_2227_ = v_run_x27_2291_;
v___y_2228_ = v___y_2281_;
v___y_2229_ = v___x_2296_;
v___y_2230_ = v_options_2287_;
v___y_2231_ = v___y_2278_;
v___y_2232_ = v___y_2282_;
v___y_2233_ = v___y_2283_;
v___y_2234_ = v___y_2284_;
goto v___jp_2218_;
}
}
else
{
lean_inc_ref(v_run_x27_2291_);
v___y_2219_ = v___f_2293_;
v___y_2220_ = v___y_2275_;
v___y_2221_ = v___y_2276_;
v___y_2222_ = v___y_2277_;
v___y_2223_ = v___y_2279_;
v___y_2224_ = v_hasTrace_2288_;
v___y_2225_ = v___y_2280_;
v___y_2226_ = v___y_2285_;
v___y_2227_ = v_run_x27_2291_;
v___y_2228_ = v___y_2281_;
v___y_2229_ = v___x_2296_;
v___y_2230_ = v_options_2287_;
v___y_2231_ = v___y_2278_;
v___y_2232_ = v___y_2282_;
v___y_2233_ = v___y_2283_;
v___y_2234_ = v___y_2284_;
goto v___jp_2218_;
}
}
}
}
v___jp_2300_:
{
if (lean_obj_tag(v___y_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
v_a_2313_ = lean_ctor_get(v___y_2312_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___y_2312_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2315_ = v___y_2312_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___y_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
uint8_t v___x_2317_; 
v___x_2317_ = lean_unbox(v_a_2313_);
lean_dec(v_a_2313_);
if (v___x_2317_ == 0)
{
lean_del_object(v___x_2315_);
v___y_2275_ = v___y_2302_;
v___y_2276_ = v___y_2306_;
v___y_2277_ = v___y_2305_;
v___y_2278_ = v___y_2308_;
v___y_2279_ = v___y_2303_;
v___y_2280_ = v___y_2307_;
v___y_2281_ = v___y_2311_;
v___y_2282_ = v___y_2304_;
v___y_2283_ = v___y_2301_;
v___y_2284_ = v___y_2309_;
v___y_2285_ = v___y_2310_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
v___x_2318_ = lean_box(v___x_1777_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2318_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
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
else
{
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
return v___y_2312_;
}
}
v___jp_2323_:
{
lean_object* v___x_2342_; double v___x_2343_; double v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2342_ = lean_io_get_num_heartbeats();
v___x_2343_ = lean_float_of_nat(v___y_2331_);
v___x_2344_ = lean_float_of_nat(v___x_2342_);
v___x_2345_ = lean_box_float(v___x_2343_);
v___x_2346_ = lean_box_float(v___x_2344_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_a_2341_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
lean_inc_ref(v___y_2325_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2349_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2324_, v___x_1779_, v___y_2327_, v___y_2339_, v___y_2329_, v___y_2325_, v___x_2348_, v___y_2334_, v___y_2337_, v___y_2338_, v___y_2326_, v___y_2335_, v___y_2340_, v___y_2332_, v___y_2336_, v___y_2333_, v___y_2328_, v___y_2330_);
v___y_2301_ = v___y_2333_;
v___y_2302_ = v___y_2334_;
v___y_2303_ = v___y_2335_;
v___y_2304_ = v___y_2336_;
v___y_2305_ = v___y_2338_;
v___y_2306_ = v___y_2337_;
v___y_2307_ = v___y_2340_;
v___y_2308_ = v___y_2326_;
v___y_2309_ = v___y_2328_;
v___y_2310_ = v___y_2330_;
v___y_2311_ = v___y_2332_;
v___y_2312_ = v___x_2349_;
goto v___jp_2300_;
}
v___jp_2350_:
{
lean_object* v___x_2369_; double v___x_2370_; double v___x_2371_; double v___x_2372_; double v___x_2373_; double v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2369_ = lean_io_mono_nanos_now();
v___x_2370_ = lean_float_of_nat(v___y_2361_);
v___x_2371_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2372_ = lean_float_div(v___x_2370_, v___x_2371_);
v___x_2373_ = lean_float_of_nat(v___x_2369_);
v___x_2374_ = lean_float_div(v___x_2373_, v___x_2371_);
v___x_2375_ = lean_box_float(v___x_2372_);
v___x_2376_ = lean_box_float(v___x_2374_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_a_2368_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
lean_inc_ref(v___y_2352_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2379_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2351_, v___x_1779_, v___y_2354_, v___y_2366_, v___y_2356_, v___y_2352_, v___x_2378_, v___y_2360_, v___y_2364_, v___y_2365_, v___y_2353_, v___y_2362_, v___y_2367_, v___y_2358_, v___y_2363_, v___y_2359_, v___y_2355_, v___y_2357_);
v___y_2301_ = v___y_2359_;
v___y_2302_ = v___y_2360_;
v___y_2303_ = v___y_2362_;
v___y_2304_ = v___y_2363_;
v___y_2305_ = v___y_2365_;
v___y_2306_ = v___y_2364_;
v___y_2307_ = v___y_2367_;
v___y_2308_ = v___y_2353_;
v___y_2309_ = v___y_2355_;
v___y_2310_ = v___y_2357_;
v___y_2311_ = v___y_2358_;
v___y_2312_ = v___x_2379_;
goto v___jp_2300_;
}
v___jp_2380_:
{
lean_object* v___x_2397_; lean_object* v_a_2398_; uint8_t v___x_2399_; 
v___x_2397_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2386_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2384_, v___x_1780_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_io_mono_nanos_now();
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2393_);
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2395_);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2392_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2388_);
v___x_2401_ = lean_apply_12(v___y_2396_, v___y_2388_, v___y_2391_, v___y_2392_, v___y_2383_, v___y_2390_, v___y_2395_, v___y_2387_, v___y_2393_, v___y_2389_, v___y_2385_, v___y_2386_, lean_box(0));
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
v___y_2351_ = v___y_2381_;
v___y_2352_ = v___y_2382_;
v___y_2353_ = v___y_2383_;
v___y_2354_ = v___y_2384_;
v___y_2355_ = v___y_2385_;
v___y_2356_ = v_a_2398_;
v___y_2357_ = v___y_2386_;
v___y_2358_ = v___y_2387_;
v___y_2359_ = v___y_2389_;
v___y_2360_ = v___y_2388_;
v___y_2361_ = v___x_2400_;
v___y_2362_ = v___y_2390_;
v___y_2363_ = v___y_2393_;
v___y_2364_ = v___y_2391_;
v___y_2365_ = v___y_2392_;
v___y_2366_ = v___y_2394_;
v___y_2367_ = v___y_2395_;
v_a_2368_ = v___x_2407_;
goto v___jp_2350_;
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
v_a_2410_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2401_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2401_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 0);
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
v___y_2351_ = v___y_2381_;
v___y_2352_ = v___y_2382_;
v___y_2353_ = v___y_2383_;
v___y_2354_ = v___y_2384_;
v___y_2355_ = v___y_2385_;
v___y_2356_ = v_a_2398_;
v___y_2357_ = v___y_2386_;
v___y_2358_ = v___y_2387_;
v___y_2359_ = v___y_2389_;
v___y_2360_ = v___y_2388_;
v___y_2361_ = v___x_2400_;
v___y_2362_ = v___y_2390_;
v___y_2363_ = v___y_2393_;
v___y_2364_ = v___y_2391_;
v___y_2365_ = v___y_2392_;
v___y_2366_ = v___y_2394_;
v___y_2367_ = v___y_2395_;
v_a_2368_ = v___x_2415_;
goto v___jp_2350_;
}
}
}
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2393_);
lean_inc(v___y_2387_);
lean_inc_ref(v___y_2395_);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2392_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2388_);
v___x_2419_ = lean_apply_12(v___y_2396_, v___y_2388_, v___y_2391_, v___y_2392_, v___y_2383_, v___y_2390_, v___y_2395_, v___y_2387_, v___y_2393_, v___y_2389_, v___y_2385_, v___y_2386_, lean_box(0));
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 1);
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
v___y_2324_ = v___y_2381_;
v___y_2325_ = v___y_2382_;
v___y_2326_ = v___y_2383_;
v___y_2327_ = v___y_2384_;
v___y_2328_ = v___y_2385_;
v___y_2329_ = v_a_2398_;
v___y_2330_ = v___y_2386_;
v___y_2331_ = v___x_2418_;
v___y_2332_ = v___y_2387_;
v___y_2333_ = v___y_2389_;
v___y_2334_ = v___y_2388_;
v___y_2335_ = v___y_2390_;
v___y_2336_ = v___y_2393_;
v___y_2337_ = v___y_2391_;
v___y_2338_ = v___y_2392_;
v___y_2339_ = v___y_2394_;
v___y_2340_ = v___y_2395_;
v_a_2341_ = v___x_2425_;
goto v___jp_2323_;
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_a_2428_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2419_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2419_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 0);
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
v___y_2324_ = v___y_2381_;
v___y_2325_ = v___y_2382_;
v___y_2326_ = v___y_2383_;
v___y_2327_ = v___y_2384_;
v___y_2328_ = v___y_2385_;
v___y_2329_ = v_a_2398_;
v___y_2330_ = v___y_2386_;
v___y_2331_ = v___x_2418_;
v___y_2332_ = v___y_2387_;
v___y_2333_ = v___y_2389_;
v___y_2334_ = v___y_2388_;
v___y_2335_ = v___y_2390_;
v___y_2336_ = v___y_2393_;
v___y_2337_ = v___y_2391_;
v___y_2338_ = v___y_2392_;
v___y_2339_ = v___y_2394_;
v___y_2340_ = v___y_2395_;
v_a_2341_ = v___x_2433_;
goto v___jp_2323_;
}
}
}
}
}
v___jp_2436_:
{
if (lean_obj_tag(v___y_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2472_; 
v_a_2449_ = lean_ctor_get(v___y_2448_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___y_2448_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2451_ = v___y_2448_;
v_isShared_2452_ = v_isSharedCheck_2472_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___y_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2472_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
uint8_t v___x_2453_; 
v___x_2453_ = lean_unbox(v_a_2449_);
lean_dec(v_a_2449_);
if (v___x_2453_ == 0)
{
lean_del_object(v___x_2451_);
if (v_structures_1928_ == 0)
{
v___y_2275_ = v___y_2438_;
v___y_2276_ = v___y_2442_;
v___y_2277_ = v___y_2441_;
v___y_2278_ = v___y_2444_;
v___y_2279_ = v___y_2439_;
v___y_2280_ = v___y_2443_;
v___y_2281_ = v___y_2447_;
v___y_2282_ = v___y_2440_;
v___y_2283_ = v___y_2437_;
v___y_2284_ = v___y_2445_;
v___y_2285_ = v___y_2446_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2454_; lean_object* v_options_2455_; uint8_t v_hasTrace_2456_; 
v___x_2454_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_options_2455_ = lean_ctor_get(v___y_2445_, 2);
v_hasTrace_2456_ = lean_ctor_get_uint8(v_options_2455_, sizeof(void*)*1);
if (v_hasTrace_2456_ == 0)
{
lean_object* v_run_x27_2457_; lean_object* v___x_2458_; 
v_run_x27_2457_ = lean_ctor_get(v___x_2454_, 1);
lean_inc_ref(v_run_x27_2457_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2437_);
lean_inc_ref(v___y_2440_);
lean_inc(v___y_2447_);
lean_inc_ref(v___y_2443_);
lean_inc(v___y_2439_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2441_);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2438_);
v___x_2458_ = lean_apply_12(v_run_x27_2457_, v___y_2438_, v___y_2442_, v___y_2441_, v___y_2444_, v___y_2439_, v___y_2443_, v___y_2447_, v___y_2440_, v___y_2437_, v___y_2445_, v___y_2446_, lean_box(0));
v___y_2301_ = v___y_2437_;
v___y_2302_ = v___y_2438_;
v___y_2303_ = v___y_2439_;
v___y_2304_ = v___y_2440_;
v___y_2305_ = v___y_2441_;
v___y_2306_ = v___y_2442_;
v___y_2307_ = v___y_2443_;
v___y_2308_ = v___y_2444_;
v___y_2309_ = v___y_2445_;
v___y_2310_ = v___y_2446_;
v___y_2311_ = v___y_2447_;
v___y_2312_ = v___x_2458_;
goto v___jp_2300_;
}
else
{
lean_object* v_run_x27_2459_; lean_object* v_inheritedTraceOptions_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v_run_x27_2459_ = lean_ctor_get(v___x_2454_, 1);
v_inheritedTraceOptions_2460_ = lean_ctor_get(v___y_2445_, 13);
v___f_2461_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6);
v___x_2462_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1778_);
v___x_2463_ = l_Lean_Name_append(v___x_2462_, v_cls_1778_);
v___x_2464_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2460_, v_options_2455_, v___x_2463_);
lean_dec(v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = l_Lean_trace_profiler;
v___x_2466_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2455_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; 
lean_inc_ref(v_run_x27_2459_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2437_);
lean_inc_ref(v___y_2440_);
lean_inc(v___y_2447_);
lean_inc_ref(v___y_2443_);
lean_inc(v___y_2439_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2441_);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2438_);
v___x_2467_ = lean_apply_12(v_run_x27_2459_, v___y_2438_, v___y_2442_, v___y_2441_, v___y_2444_, v___y_2439_, v___y_2443_, v___y_2447_, v___y_2440_, v___y_2437_, v___y_2445_, v___y_2446_, lean_box(0));
v___y_2301_ = v___y_2437_;
v___y_2302_ = v___y_2438_;
v___y_2303_ = v___y_2439_;
v___y_2304_ = v___y_2440_;
v___y_2305_ = v___y_2441_;
v___y_2306_ = v___y_2442_;
v___y_2307_ = v___y_2443_;
v___y_2308_ = v___y_2444_;
v___y_2309_ = v___y_2445_;
v___y_2310_ = v___y_2446_;
v___y_2311_ = v___y_2447_;
v___y_2312_ = v___x_2467_;
goto v___jp_2300_;
}
else
{
lean_inc_ref(v_run_x27_2459_);
v___y_2381_ = v_hasTrace_2456_;
v___y_2382_ = v___f_2461_;
v___y_2383_ = v___y_2444_;
v___y_2384_ = v_options_2455_;
v___y_2385_ = v___y_2445_;
v___y_2386_ = v___y_2446_;
v___y_2387_ = v___y_2447_;
v___y_2388_ = v___y_2438_;
v___y_2389_ = v___y_2437_;
v___y_2390_ = v___y_2439_;
v___y_2391_ = v___y_2442_;
v___y_2392_ = v___y_2441_;
v___y_2393_ = v___y_2440_;
v___y_2394_ = v___x_2464_;
v___y_2395_ = v___y_2443_;
v___y_2396_ = v_run_x27_2459_;
goto v___jp_2380_;
}
}
else
{
lean_inc_ref(v_run_x27_2459_);
v___y_2381_ = v_hasTrace_2456_;
v___y_2382_ = v___f_2461_;
v___y_2383_ = v___y_2444_;
v___y_2384_ = v_options_2455_;
v___y_2385_ = v___y_2445_;
v___y_2386_ = v___y_2446_;
v___y_2387_ = v___y_2447_;
v___y_2388_ = v___y_2438_;
v___y_2389_ = v___y_2437_;
v___y_2390_ = v___y_2439_;
v___y_2391_ = v___y_2442_;
v___y_2392_ = v___y_2441_;
v___y_2393_ = v___y_2440_;
v___y_2394_ = v___x_2464_;
v___y_2395_ = v___y_2443_;
v___y_2396_ = v_run_x27_2459_;
goto v___jp_2380_;
}
}
}
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
v___x_2468_ = lean_box(v___x_1777_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v___x_2468_);
v___x_2470_ = v___x_2451_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
return v___y_2448_;
}
}
v___jp_2473_:
{
lean_object* v___x_2492_; double v___x_2493_; double v___x_2494_; double v___x_2495_; double v___x_2496_; double v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2492_ = lean_io_mono_nanos_now();
v___x_2493_ = lean_float_of_nat(v___y_2474_);
v___x_2494_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2495_ = lean_float_div(v___x_2493_, v___x_2494_);
v___x_2496_ = lean_float_of_nat(v___x_2492_);
v___x_2497_ = lean_float_div(v___x_2496_, v___x_2494_);
v___x_2498_ = lean_box_float(v___x_2495_);
v___x_2499_ = lean_box_float(v___x_2497_);
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2491_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
lean_inc_ref(v___y_2490_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2502_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2487_, v___x_1779_, v___y_2489_, v___y_2488_, v___y_2481_, v___y_2490_, v___x_2501_, v___y_2480_, v___y_2484_, v___y_2485_, v___y_2475_, v___y_2482_, v___y_2486_, v___y_2478_, v___y_2483_, v___y_2479_, v___y_2476_, v___y_2477_);
v___y_2437_ = v___y_2479_;
v___y_2438_ = v___y_2480_;
v___y_2439_ = v___y_2482_;
v___y_2440_ = v___y_2483_;
v___y_2441_ = v___y_2485_;
v___y_2442_ = v___y_2484_;
v___y_2443_ = v___y_2486_;
v___y_2444_ = v___y_2475_;
v___y_2445_ = v___y_2476_;
v___y_2446_ = v___y_2477_;
v___y_2447_ = v___y_2478_;
v___y_2448_ = v___x_2502_;
goto v___jp_2436_;
}
v___jp_2503_:
{
lean_object* v___x_2522_; double v___x_2523_; double v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2522_ = lean_io_get_num_heartbeats();
v___x_2523_ = lean_float_of_nat(v___y_2517_);
v___x_2524_ = lean_float_of_nat(v___x_2522_);
v___x_2525_ = lean_box_float(v___x_2523_);
v___x_2526_ = lean_box_float(v___x_2524_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v_a_2521_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
lean_inc_ref(v___y_2520_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2529_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2516_, v___x_1779_, v___y_2519_, v___y_2518_, v___y_2510_, v___y_2520_, v___x_2528_, v___y_2509_, v___y_2513_, v___y_2514_, v___y_2504_, v___y_2511_, v___y_2515_, v___y_2507_, v___y_2512_, v___y_2508_, v___y_2505_, v___y_2506_);
v___y_2437_ = v___y_2508_;
v___y_2438_ = v___y_2509_;
v___y_2439_ = v___y_2511_;
v___y_2440_ = v___y_2512_;
v___y_2441_ = v___y_2514_;
v___y_2442_ = v___y_2513_;
v___y_2443_ = v___y_2515_;
v___y_2444_ = v___y_2504_;
v___y_2445_ = v___y_2505_;
v___y_2446_ = v___y_2506_;
v___y_2447_ = v___y_2507_;
v___y_2448_ = v___x_2529_;
goto v___jp_2436_;
}
v___jp_2530_:
{
lean_object* v___x_2547_; lean_object* v_a_2548_; uint8_t v___x_2549_; 
v___x_2547_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2534_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2547_);
v___x_2549_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2546_, v___x_1780_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_io_mono_nanos_now();
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2537_);
lean_inc_ref(v___y_2541_);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2542_);
lean_inc(v___y_2538_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2540_);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2536_);
v___x_2551_ = lean_apply_12(v___y_2531_, v___y_2536_, v___y_2539_, v___y_2540_, v___y_2532_, v___y_2538_, v___y_2542_, v___y_2535_, v___y_2541_, v___y_2537_, v___y_2533_, v___y_2534_, lean_box(0));
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set_tag(v___x_2554_, 1);
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
v___y_2474_ = v___x_2550_;
v___y_2475_ = v___y_2532_;
v___y_2476_ = v___y_2533_;
v___y_2477_ = v___y_2534_;
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___y_2537_;
v___y_2480_ = v___y_2536_;
v___y_2481_ = v_a_2548_;
v___y_2482_ = v___y_2538_;
v___y_2483_ = v___y_2541_;
v___y_2484_ = v___y_2539_;
v___y_2485_ = v___y_2540_;
v___y_2486_ = v___y_2542_;
v___y_2487_ = v___y_2543_;
v___y_2488_ = v___y_2544_;
v___y_2489_ = v___y_2546_;
v___y_2490_ = v___y_2545_;
v_a_2491_ = v___x_2557_;
goto v___jp_2473_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2551_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2551_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 0);
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
v___y_2474_ = v___x_2550_;
v___y_2475_ = v___y_2532_;
v___y_2476_ = v___y_2533_;
v___y_2477_ = v___y_2534_;
v___y_2478_ = v___y_2535_;
v___y_2479_ = v___y_2537_;
v___y_2480_ = v___y_2536_;
v___y_2481_ = v_a_2548_;
v___y_2482_ = v___y_2538_;
v___y_2483_ = v___y_2541_;
v___y_2484_ = v___y_2539_;
v___y_2485_ = v___y_2540_;
v___y_2486_ = v___y_2542_;
v___y_2487_ = v___y_2543_;
v___y_2488_ = v___y_2544_;
v___y_2489_ = v___y_2546_;
v___y_2490_ = v___y_2545_;
v_a_2491_ = v___x_2565_;
goto v___jp_2473_;
}
}
}
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2537_);
lean_inc_ref(v___y_2541_);
lean_inc(v___y_2535_);
lean_inc_ref(v___y_2542_);
lean_inc(v___y_2538_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2540_);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2536_);
v___x_2569_ = lean_apply_12(v___y_2531_, v___y_2536_, v___y_2539_, v___y_2540_, v___y_2532_, v___y_2538_, v___y_2542_, v___y_2535_, v___y_2541_, v___y_2537_, v___y_2533_, v___y_2534_, lean_box(0));
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 1);
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
v___y_2504_ = v___y_2532_;
v___y_2505_ = v___y_2533_;
v___y_2506_ = v___y_2534_;
v___y_2507_ = v___y_2535_;
v___y_2508_ = v___y_2537_;
v___y_2509_ = v___y_2536_;
v___y_2510_ = v_a_2548_;
v___y_2511_ = v___y_2538_;
v___y_2512_ = v___y_2541_;
v___y_2513_ = v___y_2539_;
v___y_2514_ = v___y_2540_;
v___y_2515_ = v___y_2542_;
v___y_2516_ = v___y_2543_;
v___y_2517_ = v___x_2568_;
v___y_2518_ = v___y_2544_;
v___y_2519_ = v___y_2546_;
v___y_2520_ = v___y_2545_;
v_a_2521_ = v___x_2575_;
goto v___jp_2503_;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
v_a_2578_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2569_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2569_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 0);
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
v___y_2504_ = v___y_2532_;
v___y_2505_ = v___y_2533_;
v___y_2506_ = v___y_2534_;
v___y_2507_ = v___y_2535_;
v___y_2508_ = v___y_2537_;
v___y_2509_ = v___y_2536_;
v___y_2510_ = v_a_2548_;
v___y_2511_ = v___y_2538_;
v___y_2512_ = v___y_2541_;
v___y_2513_ = v___y_2539_;
v___y_2514_ = v___y_2540_;
v___y_2515_ = v___y_2542_;
v___y_2516_ = v___y_2543_;
v___y_2517_ = v___x_2568_;
v___y_2518_ = v___y_2544_;
v___y_2519_ = v___y_2546_;
v___y_2520_ = v___y_2545_;
v_a_2521_ = v___x_2583_;
goto v___jp_2503_;
}
}
}
}
}
v___jp_2586_:
{
lean_object* v___x_2598_; lean_object* v_options_2599_; uint8_t v_hasTrace_2600_; 
v___x_2598_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v_options_2599_ = lean_ctor_get(v___y_2596_, 2);
v_hasTrace_2600_ = lean_ctor_get_uint8(v_options_2599_, sizeof(void*)*1);
if (v_hasTrace_2600_ == 0)
{
lean_object* v_run_x27_2601_; lean_object* v___x_2602_; 
v_run_x27_2601_ = lean_ctor_get(v___x_2598_, 1);
lean_inc_ref(v_run_x27_2601_);
lean_inc(v___y_2597_);
lean_inc_ref(v___y_2596_);
lean_inc(v___y_2595_);
lean_inc_ref(v___y_2594_);
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc(v___y_2588_);
lean_inc_ref(v___y_2587_);
v___x_2602_ = lean_apply_12(v_run_x27_2601_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, lean_box(0));
v___y_2437_ = v___y_2595_;
v___y_2438_ = v___y_2587_;
v___y_2439_ = v___y_2591_;
v___y_2440_ = v___y_2594_;
v___y_2441_ = v___y_2589_;
v___y_2442_ = v___y_2588_;
v___y_2443_ = v___y_2592_;
v___y_2444_ = v___y_2590_;
v___y_2445_ = v___y_2596_;
v___y_2446_ = v___y_2597_;
v___y_2447_ = v___y_2593_;
v___y_2448_ = v___x_2602_;
goto v___jp_2436_;
}
else
{
lean_object* v_run_x27_2603_; lean_object* v_inheritedTraceOptions_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_run_x27_2603_ = lean_ctor_get(v___x_2598_, 1);
v_inheritedTraceOptions_2604_ = lean_ctor_get(v___y_2596_, 13);
v___f_2605_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7);
v___x_2606_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1778_);
v___x_2607_ = l_Lean_Name_append(v___x_2606_, v_cls_1778_);
v___x_2608_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2604_, v_options_2599_, v___x_2607_);
lean_dec(v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = l_Lean_trace_profiler;
v___x_2610_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2599_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
lean_inc_ref(v_run_x27_2603_);
lean_inc(v___y_2597_);
lean_inc_ref(v___y_2596_);
lean_inc(v___y_2595_);
lean_inc_ref(v___y_2594_);
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc(v___y_2588_);
lean_inc_ref(v___y_2587_);
v___x_2611_ = lean_apply_12(v_run_x27_2603_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, lean_box(0));
v___y_2437_ = v___y_2595_;
v___y_2438_ = v___y_2587_;
v___y_2439_ = v___y_2591_;
v___y_2440_ = v___y_2594_;
v___y_2441_ = v___y_2589_;
v___y_2442_ = v___y_2588_;
v___y_2443_ = v___y_2592_;
v___y_2444_ = v___y_2590_;
v___y_2445_ = v___y_2596_;
v___y_2446_ = v___y_2597_;
v___y_2447_ = v___y_2593_;
v___y_2448_ = v___x_2611_;
goto v___jp_2436_;
}
else
{
lean_inc_ref(v_run_x27_2603_);
v___y_2531_ = v_run_x27_2603_;
v___y_2532_ = v___y_2590_;
v___y_2533_ = v___y_2596_;
v___y_2534_ = v___y_2597_;
v___y_2535_ = v___y_2593_;
v___y_2536_ = v___y_2587_;
v___y_2537_ = v___y_2595_;
v___y_2538_ = v___y_2591_;
v___y_2539_ = v___y_2588_;
v___y_2540_ = v___y_2589_;
v___y_2541_ = v___y_2594_;
v___y_2542_ = v___y_2592_;
v___y_2543_ = v_hasTrace_2600_;
v___y_2544_ = v___x_2608_;
v___y_2545_ = v___f_2605_;
v___y_2546_ = v_options_2599_;
goto v___jp_2530_;
}
}
else
{
lean_inc_ref(v_run_x27_2603_);
v___y_2531_ = v_run_x27_2603_;
v___y_2532_ = v___y_2590_;
v___y_2533_ = v___y_2596_;
v___y_2534_ = v___y_2597_;
v___y_2535_ = v___y_2593_;
v___y_2536_ = v___y_2587_;
v___y_2537_ = v___y_2595_;
v___y_2538_ = v___y_2591_;
v___y_2539_ = v___y_2588_;
v___y_2540_ = v___y_2589_;
v___y_2541_ = v___y_2594_;
v___y_2542_ = v___y_2592_;
v___y_2543_ = v_hasTrace_2600_;
v___y_2544_ = v___x_2608_;
v___y_2545_ = v___f_2605_;
v___y_2546_ = v_options_2599_;
goto v___jp_2530_;
}
}
}
v___jp_2612_:
{
if (lean_obj_tag(v___y_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2623_; 
v_a_2614_ = lean_ctor_get(v___y_2613_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___y_2613_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2616_ = v___y_2613_;
v_isShared_2617_ = v_isSharedCheck_2623_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___y_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2623_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
uint8_t v___x_2618_; 
v___x_2618_ = lean_unbox(v_a_2614_);
lean_dec(v_a_2614_);
if (v___x_2618_ == 0)
{
lean_del_object(v___x_2616_);
v___y_2587_ = v___y_1782_;
v___y_2588_ = v___y_1783_;
v___y_2589_ = v___y_1784_;
v___y_2590_ = v___y_1785_;
v___y_2591_ = v___y_1786_;
v___y_2592_ = v___y_1787_;
v___y_2593_ = v___y_1788_;
v___y_2594_ = v___y_1789_;
v___y_2595_ = v___y_1790_;
v___y_2596_ = v___y_1791_;
v___y_2597_ = v___y_1792_;
goto v___jp_2586_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
v___x_2619_ = lean_box(v___x_1777_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_dec_ref(v___x_1779_);
lean_dec(v_cls_1778_);
return v___y_2613_;
}
}
v___jp_2624_:
{
lean_object* v___x_2632_; double v___x_2633_; double v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2632_ = lean_io_get_num_heartbeats();
v___x_2633_ = lean_float_of_nat(v___y_2630_);
v___x_2634_ = lean_float_of_nat(v___x_2632_);
v___x_2635_ = lean_box_float(v___x_2633_);
v___x_2636_ = lean_box_float(v___x_2634_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v_a_2631_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
lean_inc_ref(v___y_2625_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2639_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2629_, v___x_1779_, v___y_2626_, v___y_2628_, v___y_2627_, v___y_2625_, v___x_2638_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
v___y_2613_ = v___x_2639_;
goto v___jp_2612_;
}
v___jp_2640_:
{
lean_object* v___x_2648_; double v___x_2649_; double v___x_2650_; double v___x_2651_; double v___x_2652_; double v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2648_ = lean_io_mono_nanos_now();
v___x_2649_ = lean_float_of_nat(v___y_2641_);
v___x_2650_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2651_ = lean_float_div(v___x_2649_, v___x_2650_);
v___x_2652_ = lean_float_of_nat(v___x_2648_);
v___x_2653_ = lean_float_div(v___x_2652_, v___x_2650_);
v___x_2654_ = lean_box_float(v___x_2651_);
v___x_2655_ = lean_box_float(v___x_2653_);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2654_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2647_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
lean_inc_ref(v___y_2642_);
lean_inc_ref(v___x_1779_);
lean_inc(v_cls_1778_);
v___x_2658_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_1778_, v___y_2646_, v___x_1779_, v___y_2643_, v___y_2645_, v___y_2644_, v___y_2642_, v___x_2657_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
v___y_2613_ = v___x_2658_;
goto v___jp_2612_;
}
v___jp_2659_:
{
lean_object* v___x_2665_; lean_object* v_a_2666_; uint8_t v___x_2667_; 
v___x_2665_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_1792_);
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref(v___x_2665_);
v___x_2667_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2662_, v___x_1780_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_io_mono_nanos_now();
lean_inc(v___y_1792_);
lean_inc_ref(v___y_1791_);
lean_inc(v___y_1790_);
lean_inc_ref(v___y_1789_);
lean_inc(v___y_1788_);
lean_inc_ref(v___y_1787_);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
v___x_2669_ = lean_apply_12(v___y_2661_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, lean_box(0));
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 1);
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
v___y_2641_ = v___x_2668_;
v___y_2642_ = v___y_2660_;
v___y_2643_ = v___y_2662_;
v___y_2644_ = v_a_2666_;
v___y_2645_ = v___y_2664_;
v___y_2646_ = v___y_2663_;
v_a_2647_ = v___x_2675_;
goto v___jp_2640_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_a_2678_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2669_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2669_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 0);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
v___y_2641_ = v___x_2668_;
v___y_2642_ = v___y_2660_;
v___y_2643_ = v___y_2662_;
v___y_2644_ = v_a_2666_;
v___y_2645_ = v___y_2664_;
v___y_2646_ = v___y_2663_;
v_a_2647_ = v___x_2683_;
goto v___jp_2640_;
}
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_io_get_num_heartbeats();
lean_inc(v___y_1792_);
lean_inc_ref(v___y_1791_);
lean_inc(v___y_1790_);
lean_inc_ref(v___y_1789_);
lean_inc(v___y_1788_);
lean_inc_ref(v___y_1787_);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
v___x_2687_ = lean_apply_12(v___y_2661_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, lean_box(0));
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set_tag(v___x_2690_, 1);
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
v___y_2625_ = v___y_2660_;
v___y_2626_ = v___y_2662_;
v___y_2627_ = v_a_2666_;
v___y_2628_ = v___y_2664_;
v___y_2629_ = v___y_2663_;
v___y_2630_ = v___x_2686_;
v_a_2631_ = v___x_2693_;
goto v___jp_2624_;
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
v_a_2696_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2687_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2687_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 0);
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
v___y_2625_ = v___y_2660_;
v___y_2626_ = v___y_2662_;
v___y_2627_ = v_a_2666_;
v___y_2628_ = v___y_2664_;
v___y_2629_ = v___y_2663_;
v___y_2630_ = v___x_2686_;
v_a_2631_ = v___x_2701_;
goto v___jp_2624_;
}
}
}
}
}
v___jp_2704_:
{
if (v___y_2705_ == 0)
{
v___y_2587_ = v___y_1782_;
v___y_2588_ = v___y_1783_;
v___y_2589_ = v___y_1784_;
v___y_2590_ = v___y_1785_;
v___y_2591_ = v___y_1786_;
v___y_2592_ = v___y_1787_;
v___y_2593_ = v___y_1788_;
v___y_2594_ = v___y_1789_;
v___y_2595_ = v___y_1790_;
v___y_2596_ = v___y_1791_;
v___y_2597_ = v___y_1792_;
goto v___jp_2586_;
}
else
{
lean_object* v___x_2706_; lean_object* v_options_2707_; uint8_t v_hasTrace_2708_; 
v___x_2706_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_options_2707_ = lean_ctor_get(v___y_1791_, 2);
v_hasTrace_2708_ = lean_ctor_get_uint8(v_options_2707_, sizeof(void*)*1);
if (v_hasTrace_2708_ == 0)
{
lean_object* v_run_x27_2709_; lean_object* v___x_2710_; 
v_run_x27_2709_ = lean_ctor_get(v___x_2706_, 1);
lean_inc_ref(v_run_x27_2709_);
lean_inc(v___y_1792_);
lean_inc_ref(v___y_1791_);
lean_inc(v___y_1790_);
lean_inc_ref(v___y_1789_);
lean_inc(v___y_1788_);
lean_inc_ref(v___y_1787_);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
v___x_2710_ = lean_apply_12(v_run_x27_2709_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, lean_box(0));
v___y_2613_ = v___x_2710_;
goto v___jp_2612_;
}
else
{
lean_object* v_run_x27_2711_; lean_object* v_inheritedTraceOptions_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_run_x27_2711_ = lean_ctor_get(v___x_2706_, 1);
v_inheritedTraceOptions_2712_ = lean_ctor_get(v___y_1791_, 13);
v___f_2713_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8);
v___x_2714_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
lean_inc(v_cls_1778_);
v___x_2715_ = l_Lean_Name_append(v___x_2714_, v_cls_1778_);
v___x_2716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2712_, v_options_2707_, v___x_2715_);
lean_dec(v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = l_Lean_trace_profiler;
v___x_2718_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2707_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; 
lean_inc_ref(v_run_x27_2711_);
lean_inc(v___y_1792_);
lean_inc_ref(v___y_1791_);
lean_inc(v___y_1790_);
lean_inc_ref(v___y_1789_);
lean_inc(v___y_1788_);
lean_inc_ref(v___y_1787_);
lean_inc(v___y_1786_);
lean_inc_ref(v___y_1785_);
lean_inc(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
v___x_2719_ = lean_apply_12(v_run_x27_2711_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, lean_box(0));
v___y_2613_ = v___x_2719_;
goto v___jp_2612_;
}
else
{
lean_inc_ref(v_run_x27_2711_);
v___y_2660_ = v___f_2713_;
v___y_2661_ = v_run_x27_2711_;
v___y_2662_ = v_options_2707_;
v___y_2663_ = v_hasTrace_2708_;
v___y_2664_ = v___x_2716_;
goto v___jp_2659_;
}
}
else
{
lean_inc_ref(v_run_x27_2711_);
v___y_2660_ = v___f_2713_;
v___y_2661_ = v_run_x27_2711_;
v___y_2662_ = v_options_2707_;
v___y_2663_ = v_hasTrace_2708_;
v___y_2664_ = v___x_2716_;
goto v___jp_2659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9___boxed(lean_object** _args){
lean_object* v___x_2720_ = _args[0];
lean_object* v_cls_2721_ = _args[1];
lean_object* v___x_2722_ = _args[2];
lean_object* v___x_2723_ = _args[3];
lean_object* v_____r_2724_ = _args[4];
lean_object* v___y_2725_ = _args[5];
lean_object* v___y_2726_ = _args[6];
lean_object* v___y_2727_ = _args[7];
lean_object* v___y_2728_ = _args[8];
lean_object* v___y_2729_ = _args[9];
lean_object* v___y_2730_ = _args[10];
lean_object* v___y_2731_ = _args[11];
lean_object* v___y_2732_ = _args[12];
lean_object* v___y_2733_ = _args[13];
lean_object* v___y_2734_ = _args[14];
lean_object* v___y_2735_ = _args[15];
lean_object* v___y_2736_ = _args[16];
_start:
{
uint8_t v___x_858353__boxed_2737_; lean_object* v_res_2738_; 
v___x_858353__boxed_2737_ = lean_unbox(v___x_2720_);
v_res_2738_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9(v___x_858353__boxed_2737_, v_cls_2721_, v___x_2722_, v___x_2723_, v_____r_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v___x_2723_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(lean_object* v_cls_2742_, lean_object* v_msg_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_ref_2749_; lean_object* v___x_2750_; lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2795_; 
v_ref_2749_ = lean_ctor_get(v___y_2746_, 5);
v___x_2750_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget_spec__0_spec__0(v_msg_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2795_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2795_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v_traceState_2756_; lean_object* v_env_2757_; lean_object* v_nextMacroScope_2758_; lean_object* v_ngen_2759_; lean_object* v_auxDeclNGen_2760_; lean_object* v_cache_2761_; lean_object* v_messages_2762_; lean_object* v_infoState_2763_; lean_object* v_snapshotTasks_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2794_; 
v___x_2755_ = lean_st_ref_take(v___y_2747_);
v_traceState_2756_ = lean_ctor_get(v___x_2755_, 4);
v_env_2757_ = lean_ctor_get(v___x_2755_, 0);
v_nextMacroScope_2758_ = lean_ctor_get(v___x_2755_, 1);
v_ngen_2759_ = lean_ctor_get(v___x_2755_, 2);
v_auxDeclNGen_2760_ = lean_ctor_get(v___x_2755_, 3);
v_cache_2761_ = lean_ctor_get(v___x_2755_, 5);
v_messages_2762_ = lean_ctor_get(v___x_2755_, 6);
v_infoState_2763_ = lean_ctor_get(v___x_2755_, 7);
v_snapshotTasks_2764_ = lean_ctor_get(v___x_2755_, 8);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2766_ = v___x_2755_;
v_isShared_2767_ = v_isSharedCheck_2794_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_snapshotTasks_2764_);
lean_inc(v_infoState_2763_);
lean_inc(v_messages_2762_);
lean_inc(v_cache_2761_);
lean_inc(v_traceState_2756_);
lean_inc(v_auxDeclNGen_2760_);
lean_inc(v_ngen_2759_);
lean_inc(v_nextMacroScope_2758_);
lean_inc(v_env_2757_);
lean_dec(v___x_2755_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2794_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint64_t v_tid_2768_; lean_object* v_traces_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2793_; 
v_tid_2768_ = lean_ctor_get_uint64(v_traceState_2756_, sizeof(void*)*1);
v_traces_2769_ = lean_ctor_get(v_traceState_2756_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_traceState_2756_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2771_ = v_traceState_2756_;
v_isShared_2772_ = v_isSharedCheck_2793_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_traces_2769_);
lean_dec(v_traceState_2756_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2793_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; double v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2___closed__0);
v___x_2775_ = 0;
v___x_2776_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_2777_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2777_, 0, v_cls_2742_);
lean_ctor_set(v___x_2777_, 1, v___x_2773_);
lean_ctor_set(v___x_2777_, 2, v___x_2776_);
lean_ctor_set_float(v___x_2777_, sizeof(void*)*3, v___x_2774_);
lean_ctor_set_float(v___x_2777_, sizeof(void*)*3 + 8, v___x_2774_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*3 + 16, v___x_2775_);
v___x_2778_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__1));
v___x_2779_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v_a_2751_);
lean_ctor_set(v___x_2779_, 2, v___x_2778_);
lean_inc(v_ref_2749_);
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_ref_2749_);
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
lean_ctor_set(v___x_2766_, 4, v___x_2783_);
v___x_2785_ = v___x_2766_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_env_2757_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_nextMacroScope_2758_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_ngen_2759_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_auxDeclNGen_2760_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2791_, 5, v_cache_2761_);
lean_ctor_set(v_reuseFailAlloc_2791_, 6, v_messages_2762_);
lean_ctor_set(v_reuseFailAlloc_2791_, 7, v_infoState_2763_);
lean_ctor_set(v_reuseFailAlloc_2791_, 8, v_snapshotTasks_2764_);
v___x_2785_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2786_ = lean_st_ref_set(v___y_2747_, v___x_2785_);
v___x_2787_ = lean_box(0);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2787_);
v___x_2789_ = v___x_2753_;
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
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___boxed(lean_object* v_cls_2796_, lean_object* v_msg_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_2796_, v_msg_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
return v_res_2803_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4(void){
_start:
{
lean_object* v_cls_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_cls_2811_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3));
v___x_2812_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__3));
v___x_2813_ = l_Lean_Name_append(v___x_2812_, v_cls_2811_);
return v___x_2813_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__5));
v___x_2816_ = l_Lean_stringToMessageData(v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
uint8_t v___y_2831_; uint8_t v___y_2832_; lean_object* v___y_2833_; lean_object* v_options_2848_; lean_object* v_inheritedTraceOptions_2849_; uint8_t v_hasTrace_2850_; lean_object* v_cls_2851_; uint8_t v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; uint8_t v___y_2856_; lean_object* v___y_2857_; uint8_t v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; uint8_t v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v_a_2873_; uint8_t v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; uint8_t v___y_2886_; lean_object* v___y_2887_; uint8_t v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; uint8_t v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v_a_2903_; uint8_t v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; uint8_t v___y_2919_; uint8_t v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; uint8_t v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2976_; uint8_t v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; uint8_t v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; uint8_t v___y_3058_; uint8_t v___y_3059_; uint8_t v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v_a_3068_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; uint8_t v___y_3089_; uint8_t v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v_a_3098_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; uint8_t v___y_3120_; uint8_t v___y_3121_; uint8_t v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3171_; uint8_t v_fixedInt_3172_; uint8_t v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; uint8_t v___y_3238_; uint8_t v___y_3239_; uint8_t v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v_a_3246_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; uint8_t v___y_3269_; uint8_t v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v_a_3276_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; uint8_t v___y_3302_; uint8_t v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3349_; uint8_t v_fixedInt_3350_; uint8_t v_enums_3351_; uint8_t v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; uint8_t v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; uint8_t v___y_3418_; lean_object* v___y_3419_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v_a_3426_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; uint8_t v___y_3450_; lean_object* v___y_3451_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v_a_3459_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; uint8_t v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; uint8_t v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; uint8_t v___y_3585_; lean_object* v___y_3586_; uint8_t v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v_a_3591_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; uint8_t v___y_3615_; lean_object* v___y_3616_; uint8_t v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v_a_3621_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; uint8_t v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; uint8_t v___y_3648_; uint8_t v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3694_; uint8_t v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; uint8_t v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; uint8_t v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; uint8_t v___y_3762_; uint8_t v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v_a_3767_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; uint8_t v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; uint8_t v___y_3791_; uint8_t v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v_a_3797_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; uint8_t v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; uint8_t v___y_3824_; uint8_t v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; uint8_t v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; uint8_t v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; uint8_t v_____do__lift_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; 
v_options_2848_ = lean_ctor_get(v_a_2827_, 2);
v_inheritedTraceOptions_2849_ = lean_ctor_get(v_a_2827_, 13);
v_hasTrace_2850_ = lean_ctor_get_uint8(v_options_2848_, sizeof(void*)*1);
v_cls_2851_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__3));
if (v_hasTrace_2850_ == 0)
{
lean_object* v___x_3953_; 
v___x_3953_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; uint8_t v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = lean_unbox(v_a_3954_);
lean_dec(v_a_3954_);
v_____do__lift_3914_ = v___x_3955_;
v___y_3915_ = v_a_2818_;
v___y_3916_ = v_a_2819_;
v___y_3917_ = v_a_2820_;
v___y_3918_ = v_a_2821_;
v___y_3919_ = v_a_2822_;
v___y_3920_ = v_a_2823_;
v___y_3921_ = v_a_2824_;
v___y_3922_ = v_a_2825_;
v___y_3923_ = v_a_2826_;
v___y_3924_ = v_a_2827_;
v___y_3925_ = v_a_2828_;
goto v___jp_3913_;
}
else
{
return v___x_3953_;
}
}
else
{
lean_object* v___f_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v_a_3963_; lean_object* v___y_3973_; lean_object* v___y_3974_; uint8_t v_a_3975_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v_a_3981_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v_a_3993_; lean_object* v___y_4006_; lean_object* v___y_4007_; uint8_t v_a_4008_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v_a_4014_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; 
v___f_3956_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__7));
v___x_3957_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3958_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2849_, v_options_2848_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4054_ = l_Lean_trace_profiler;
v___x_4055_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2848_, v___x_4054_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; 
v___x_4056_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; uint8_t v___x_4058_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref_known(v___x_4056_, 1);
v___x_4058_ = lean_unbox(v_a_4057_);
lean_dec(v_a_4057_);
v_____do__lift_3914_ = v___x_4058_;
v___y_3915_ = v_a_2818_;
v___y_3916_ = v_a_2819_;
v___y_3917_ = v_a_2820_;
v___y_3918_ = v_a_2821_;
v___y_3919_ = v_a_2822_;
v___y_3920_ = v_a_2823_;
v___y_3921_ = v_a_2824_;
v___y_3922_ = v_a_2825_;
v___y_3923_ = v_a_2826_;
v___y_3924_ = v_a_2827_;
v___y_3925_ = v_a_2828_;
goto v___jp_3913_;
}
else
{
return v___x_4056_;
}
}
else
{
goto v___jp_4023_;
}
}
else
{
goto v___jp_4023_;
}
v___jp_3960_:
{
lean_object* v___x_3964_; double v___x_3965_; double v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3964_ = lean_io_get_num_heartbeats();
v___x_3965_ = lean_float_of_nat(v___y_3961_);
v___x_3966_ = lean_float_of_nat(v___x_3964_);
v___x_3967_ = lean_box_float(v___x_3965_);
v___x_3968_ = lean_box_float(v___x_3966_);
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3970_, 0, v_a_3963_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
v___x_3971_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v_hasTrace_2850_, v___x_3957_, v_options_2848_, v___x_3959_, v___y_3962_, v___f_3956_, v___x_3970_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
return v___x_3971_;
}
v___jp_3972_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = lean_box(v_a_3975_);
v___x_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
v___y_3961_ = v___y_3973_;
v___y_3962_ = v___y_3974_;
v_a_3963_ = v___x_3977_;
goto v___jp_3960_;
}
v___jp_3978_:
{
lean_object* v___x_3982_; 
v___x_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3982_, 0, v_a_3981_);
v___y_3961_ = v___y_3979_;
v___y_3962_ = v___y_3980_;
v_a_3963_ = v___x_3982_;
goto v___jp_3960_;
}
v___jp_3983_:
{
if (lean_obj_tag(v___y_3986_) == 0)
{
lean_object* v_a_3987_; uint8_t v___x_3988_; 
v_a_3987_ = lean_ctor_get(v___y_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref_known(v___y_3986_, 1);
v___x_3988_ = lean_unbox(v_a_3987_);
lean_dec(v_a_3987_);
v___y_3973_ = v___y_3984_;
v___y_3974_ = v___y_3985_;
v_a_3975_ = v___x_3988_;
goto v___jp_3972_;
}
else
{
lean_object* v_a_3989_; 
v_a_3989_ = lean_ctor_get(v___y_3986_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___y_3986_, 1);
v___y_3979_ = v___y_3984_;
v___y_3980_ = v___y_3985_;
v_a_3981_ = v_a_3989_;
goto v___jp_3978_;
}
}
v___jp_3990_:
{
lean_object* v___x_3994_; double v___x_3995_; double v___x_3996_; double v___x_3997_; double v___x_3998_; double v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_3994_ = lean_io_mono_nanos_now();
v___x_3995_ = lean_float_of_nat(v___y_3991_);
v___x_3996_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3997_ = lean_float_div(v___x_3995_, v___x_3996_);
v___x_3998_ = lean_float_of_nat(v___x_3994_);
v___x_3999_ = lean_float_div(v___x_3998_, v___x_3996_);
v___x_4000_ = lean_box_float(v___x_3997_);
v___x_4001_ = lean_box_float(v___x_3999_);
v___x_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4000_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v_a_3993_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v___x_4004_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v_hasTrace_2850_, v___x_3957_, v_options_2848_, v___x_3959_, v___y_3992_, v___f_3956_, v___x_4003_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
return v___x_4004_;
}
v___jp_4005_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = lean_box(v_a_4008_);
v___x_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
v___y_3991_ = v___y_4006_;
v___y_3992_ = v___y_4007_;
v_a_3993_ = v___x_4010_;
goto v___jp_3990_;
}
v___jp_4011_:
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v_a_4014_);
v___y_3991_ = v___y_4012_;
v___y_3992_ = v___y_4013_;
v_a_3993_ = v___x_4015_;
goto v___jp_3990_;
}
v___jp_4016_:
{
if (lean_obj_tag(v___y_4019_) == 0)
{
lean_object* v_a_4020_; uint8_t v___x_4021_; 
v_a_4020_ = lean_ctor_get(v___y_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___y_4019_, 1);
v___x_4021_ = lean_unbox(v_a_4020_);
lean_dec(v_a_4020_);
v___y_4006_ = v___y_4017_;
v___y_4007_ = v___y_4018_;
v_a_4008_ = v___x_4021_;
goto v___jp_4005_;
}
else
{
lean_object* v_a_4022_; 
v_a_4022_ = lean_ctor_get(v___y_4019_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___y_4019_, 1);
v___y_4012_ = v___y_4017_;
v___y_4013_ = v___y_4018_;
v_a_4014_ = v_a_4022_;
goto v___jp_4011_;
}
}
v___jp_4023_:
{
lean_object* v___x_4024_; lean_object* v_a_4025_; lean_object* v___x_4026_; uint8_t v___x_4027_; 
v___x_4024_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v_a_2828_);
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v___x_4024_);
v___x_4026_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4027_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2848_, v___x_4026_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = lean_io_mono_nanos_now();
v___x_4029_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; uint8_t v___x_4031_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = lean_unbox(v_a_4030_);
lean_dec(v_a_4030_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_dec_ref_known(v___x_4032_, 1);
if (v___x_3959_ == 0)
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4033_ = lean_box(0);
v___x_4034_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8(v___x_4027_, v_hasTrace_2850_, v_cls_2851_, v___x_3957_, v___x_4026_, v___x_4033_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
v___y_4017_ = v___x_4028_;
v___y_4018_ = v_a_4025_;
v___y_4019_ = v___x_4034_;
goto v___jp_4016_;
}
else
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6);
v___x_4036_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_2851_, v___x_4035_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4038_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8(v___x_4027_, v_hasTrace_2850_, v_cls_2851_, v___x_3957_, v___x_4026_, v_a_4037_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
v___y_4017_ = v___x_4028_;
v___y_4018_ = v_a_4025_;
v___y_4019_ = v___x_4038_;
goto v___jp_4016_;
}
else
{
lean_object* v_a_4039_; 
v_a_4039_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v___x_4036_, 1);
v___y_4012_ = v___x_4028_;
v___y_4013_ = v_a_4025_;
v_a_4014_ = v_a_4039_;
goto v___jp_4011_;
}
}
}
else
{
lean_object* v_a_4040_; 
v_a_4040_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4032_, 1);
v___y_4012_ = v___x_4028_;
v___y_4013_ = v_a_4025_;
v_a_4014_ = v_a_4040_;
goto v___jp_4011_;
}
}
else
{
v___y_4006_ = v___x_4028_;
v___y_4007_ = v_a_4025_;
v_a_4008_ = v_hasTrace_2850_;
goto v___jp_4005_;
}
}
else
{
v___y_4017_ = v___x_4028_;
v___y_4018_ = v_a_4025_;
v___y_4019_ = v___x_4029_;
goto v___jp_4016_;
}
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = lean_io_get_num_heartbeats();
v___x_4042_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_setupTarget(v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; uint8_t v___x_4044_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4042_, 1);
v___x_4044_ = lean_unbox(v_a_4043_);
lean_dec(v_a_4043_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_dec_ref_known(v___x_4045_, 1);
if (v___x_3959_ == 0)
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = lean_box(0);
v___x_4047_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9(v___x_4027_, v_cls_2851_, v___x_3957_, v___x_4026_, v___x_4046_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
v___y_3984_ = v___x_4041_;
v___y_3985_ = v_a_4025_;
v___y_3986_ = v___x_4047_;
goto v___jp_3983_;
}
else
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6);
v___x_4049_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_2851_, v___x_4048_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v___x_4051_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__9(v___x_4027_, v_cls_2851_, v___x_3957_, v___x_4026_, v_a_4050_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
v___y_3984_ = v___x_4041_;
v___y_3985_ = v_a_4025_;
v___y_3986_ = v___x_4051_;
goto v___jp_3983_;
}
else
{
lean_object* v_a_4052_; 
v_a_4052_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4052_);
lean_dec_ref_known(v___x_4049_, 1);
v___y_3979_ = v___x_4041_;
v___y_3980_ = v_a_4025_;
v_a_3981_ = v_a_4052_;
goto v___jp_3978_;
}
}
}
else
{
lean_object* v_a_4053_; 
v_a_4053_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_a_4053_);
lean_dec_ref_known(v___x_4045_, 1);
v___y_3979_ = v___x_4041_;
v___y_3980_ = v_a_4025_;
v_a_3981_ = v_a_4053_;
goto v___jp_3978_;
}
}
else
{
v___y_3973_ = v___x_4041_;
v___y_3974_ = v_a_4025_;
v_a_3975_ = v___x_4027_;
goto v___jp_3972_;
}
}
else
{
v___y_3984_ = v___x_4041_;
v___y_3985_ = v_a_4025_;
v___y_3986_ = v___x_4042_;
goto v___jp_3983_;
}
}
}
}
v___jp_2830_:
{
if (lean_obj_tag(v___y_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2847_; 
v_a_2834_ = lean_ctor_get(v___y_2833_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___y_2833_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2836_ = v___y_2833_;
v_isShared_2837_ = v_isSharedCheck_2847_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___y_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2847_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
uint8_t v___x_2838_; 
v___x_2838_ = lean_unbox(v_a_2834_);
lean_dec(v_a_2834_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = lean_box(v___y_2831_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2839_);
v___x_2841_ = v___x_2836_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2843_ = lean_box(v___y_2832_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2843_);
v___x_2845_ = v___x_2836_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
return v___y_2833_;
}
}
v___jp_2852_:
{
lean_object* v___x_2874_; double v___x_2875_; double v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2874_ = lean_io_get_num_heartbeats();
v___x_2875_ = lean_float_of_nat(v___y_2871_);
v___x_2876_ = lean_float_of_nat(v___x_2874_);
v___x_2877_ = lean_box_float(v___x_2875_);
v___x_2878_ = lean_box_float(v___x_2876_);
v___x_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v_a_2873_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
lean_inc_ref(v___y_2868_);
lean_inc_ref(v___y_2866_);
v___x_2881_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_2856_, v___y_2866_, v___y_2861_, v___y_2858_, v___y_2867_, v___y_2868_, v___x_2880_, v___y_2865_, v___y_2862_, v___y_2872_, v___y_2860_, v___y_2870_, v___y_2854_, v___y_2864_, v___y_2855_, v___y_2859_, v___y_2869_, v___y_2857_);
v___y_2831_ = v___y_2853_;
v___y_2832_ = v___y_2863_;
v___y_2833_ = v___x_2881_;
goto v___jp_2830_;
}
v___jp_2882_:
{
lean_object* v___x_2904_; double v___x_2905_; double v___x_2906_; double v___x_2907_; double v___x_2908_; double v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2904_ = lean_io_mono_nanos_now();
v___x_2905_ = lean_float_of_nat(v___y_2896_);
v___x_2906_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_2907_ = lean_float_div(v___x_2905_, v___x_2906_);
v___x_2908_ = lean_float_of_nat(v___x_2904_);
v___x_2909_ = lean_float_div(v___x_2908_, v___x_2906_);
v___x_2910_ = lean_box_float(v___x_2907_);
v___x_2911_ = lean_box_float(v___x_2909_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_a_2903_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
lean_inc_ref(v___y_2899_);
lean_inc_ref(v___y_2897_);
v___x_2914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_2886_, v___y_2897_, v___y_2891_, v___y_2888_, v___y_2898_, v___y_2899_, v___x_2913_, v___y_2895_, v___y_2892_, v___y_2902_, v___y_2890_, v___y_2901_, v___y_2884_, v___y_2894_, v___y_2885_, v___y_2889_, v___y_2900_, v___y_2887_);
v___y_2831_ = v___y_2883_;
v___y_2832_ = v___y_2893_;
v___y_2833_ = v___x_2914_;
goto v___jp_2830_;
}
v___jp_2915_:
{
lean_object* v___x_2935_; lean_object* v_a_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2935_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_2921_);
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref(v___x_2935_);
v___x_2937_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2938_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_2925_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_io_mono_nanos_now();
lean_inc(v___y_2921_);
lean_inc_ref(v___y_2932_);
lean_inc(v___y_2922_);
lean_inc_ref(v___y_2918_);
lean_inc(v___y_2928_);
lean_inc_ref(v___y_2917_);
lean_inc(v___y_2933_);
lean_inc_ref(v___y_2923_);
lean_inc(v___y_2934_);
lean_inc(v___y_2924_);
lean_inc_ref(v___y_2929_);
v___x_2940_ = lean_apply_12(v___y_2926_, v___y_2929_, v___y_2924_, v___y_2934_, v___y_2923_, v___y_2933_, v___y_2917_, v___y_2928_, v___y_2918_, v___y_2922_, v___y_2932_, v___y_2921_, lean_box(0));
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set_tag(v___x_2943_, 1);
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
v___y_2883_ = v___y_2916_;
v___y_2884_ = v___y_2917_;
v___y_2885_ = v___y_2918_;
v___y_2886_ = v___y_2919_;
v___y_2887_ = v___y_2921_;
v___y_2888_ = v___y_2920_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v___y_2923_;
v___y_2891_ = v___y_2925_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2927_;
v___y_2894_ = v___y_2928_;
v___y_2895_ = v___y_2929_;
v___y_2896_ = v___x_2939_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v_a_2936_;
v___y_2899_ = v___y_2931_;
v___y_2900_ = v___y_2932_;
v___y_2901_ = v___y_2933_;
v___y_2902_ = v___y_2934_;
v_a_2903_ = v___x_2946_;
goto v___jp_2882_;
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_a_2949_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2940_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2940_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 0);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
v___y_2883_ = v___y_2916_;
v___y_2884_ = v___y_2917_;
v___y_2885_ = v___y_2918_;
v___y_2886_ = v___y_2919_;
v___y_2887_ = v___y_2921_;
v___y_2888_ = v___y_2920_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v___y_2923_;
v___y_2891_ = v___y_2925_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2927_;
v___y_2894_ = v___y_2928_;
v___y_2895_ = v___y_2929_;
v___y_2896_ = v___x_2939_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v_a_2936_;
v___y_2899_ = v___y_2931_;
v___y_2900_ = v___y_2932_;
v___y_2901_ = v___y_2933_;
v___y_2902_ = v___y_2934_;
v_a_2903_ = v___x_2954_;
goto v___jp_2882_;
}
}
}
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = lean_io_get_num_heartbeats();
lean_inc(v___y_2921_);
lean_inc_ref(v___y_2932_);
lean_inc(v___y_2922_);
lean_inc_ref(v___y_2918_);
lean_inc(v___y_2928_);
lean_inc_ref(v___y_2917_);
lean_inc(v___y_2933_);
lean_inc_ref(v___y_2923_);
lean_inc(v___y_2934_);
lean_inc(v___y_2924_);
lean_inc_ref(v___y_2929_);
v___x_2958_ = lean_apply_12(v___y_2926_, v___y_2929_, v___y_2924_, v___y_2934_, v___y_2923_, v___y_2933_, v___y_2917_, v___y_2928_, v___y_2918_, v___y_2922_, v___y_2932_, v___y_2921_, lean_box(0));
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set_tag(v___x_2961_, 1);
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
v___y_2853_ = v___y_2916_;
v___y_2854_ = v___y_2917_;
v___y_2855_ = v___y_2918_;
v___y_2856_ = v___y_2919_;
v___y_2857_ = v___y_2921_;
v___y_2858_ = v___y_2920_;
v___y_2859_ = v___y_2922_;
v___y_2860_ = v___y_2923_;
v___y_2861_ = v___y_2925_;
v___y_2862_ = v___y_2924_;
v___y_2863_ = v___y_2927_;
v___y_2864_ = v___y_2928_;
v___y_2865_ = v___y_2929_;
v___y_2866_ = v___y_2930_;
v___y_2867_ = v_a_2936_;
v___y_2868_ = v___y_2931_;
v___y_2869_ = v___y_2932_;
v___y_2870_ = v___y_2933_;
v___y_2871_ = v___x_2957_;
v___y_2872_ = v___y_2934_;
v_a_2873_ = v___x_2964_;
goto v___jp_2852_;
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
v_a_2967_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2958_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2958_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 0);
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
v___y_2853_ = v___y_2916_;
v___y_2854_ = v___y_2917_;
v___y_2855_ = v___y_2918_;
v___y_2856_ = v___y_2919_;
v___y_2857_ = v___y_2921_;
v___y_2858_ = v___y_2920_;
v___y_2859_ = v___y_2922_;
v___y_2860_ = v___y_2923_;
v___y_2861_ = v___y_2925_;
v___y_2862_ = v___y_2924_;
v___y_2863_ = v___y_2927_;
v___y_2864_ = v___y_2928_;
v___y_2865_ = v___y_2929_;
v___y_2866_ = v___y_2930_;
v___y_2867_ = v_a_2936_;
v___y_2868_ = v___y_2931_;
v___y_2869_ = v___y_2932_;
v___y_2870_ = v___y_2933_;
v___y_2871_ = v___x_2957_;
v___y_2872_ = v___y_2934_;
v_a_2873_ = v___x_2972_;
goto v___jp_2852_;
}
}
}
}
}
v___jp_2975_:
{
lean_object* v___x_2989_; lean_object* v_a_2990_; lean_object* v___x_2991_; 
v___x_2989_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_0__Lean_Meta_Tactic_BVDecide_Normalize_passPipeline___redArg(v___y_2978_);
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_a_2990_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
lean_dec(v_a_2990_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; uint8_t v___x_2993_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
v___x_2993_ = lean_unbox(v_a_2992_);
if (v___x_2993_ == 0)
{
uint8_t v_shortCircuit_2994_; 
v_shortCircuit_2994_ = lean_ctor_get_uint8(v___y_2976_, sizeof(void*)*2 + 9);
if (v_shortCircuit_2994_ == 0)
{
lean_dec(v_a_2992_);
return v___x_2991_;
}
else
{
lean_object* v___x_2995_; lean_object* v_options_2996_; uint8_t v_hasTrace_2997_; 
lean_dec_ref_known(v___x_2991_, 1);
v___x_2995_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass;
v_options_2996_ = lean_ctor_get(v___y_2987_, 2);
v_hasTrace_2997_ = lean_ctor_get_uint8(v_options_2996_, sizeof(void*)*1);
if (v_hasTrace_2997_ == 0)
{
lean_object* v_run_x27_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v_run_x27_2998_ = lean_ctor_get(v___x_2995_, 1);
lean_inc_ref(v_run_x27_2998_);
lean_inc(v___y_2988_);
lean_inc_ref(v___y_2987_);
lean_inc(v___y_2986_);
lean_inc_ref(v___y_2985_);
lean_inc(v___y_2984_);
lean_inc_ref(v___y_2983_);
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2981_);
lean_inc(v___y_2980_);
lean_inc(v___y_2979_);
lean_inc_ref(v___y_2978_);
v___x_2999_ = lean_apply_12(v_run_x27_2998_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, lean_box(0));
v___x_3000_ = lean_unbox(v_a_2992_);
lean_dec(v_a_2992_);
v___y_2831_ = v___x_3000_;
v___y_2832_ = v___y_2977_;
v___y_2833_ = v___x_2999_;
goto v___jp_2830_;
}
else
{
lean_object* v_run_x27_3001_; lean_object* v_inheritedTraceOptions_3002_; lean_object* v___f_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v_run_x27_3001_ = lean_ctor_get(v___x_2995_, 1);
v_inheritedTraceOptions_3002_ = lean_ctor_get(v___y_2987_, 13);
v___f_3003_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__1);
v___x_3004_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3005_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3006_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3002_, v_options_2996_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = l_Lean_trace_profiler;
v___x_3008_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_2996_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
lean_inc_ref(v_run_x27_3001_);
lean_inc(v___y_2988_);
lean_inc_ref(v___y_2987_);
lean_inc(v___y_2986_);
lean_inc_ref(v___y_2985_);
lean_inc(v___y_2984_);
lean_inc_ref(v___y_2983_);
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2981_);
lean_inc(v___y_2980_);
lean_inc(v___y_2979_);
lean_inc_ref(v___y_2978_);
v___x_3009_ = lean_apply_12(v_run_x27_3001_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, lean_box(0));
v___x_3010_ = lean_unbox(v_a_2992_);
lean_dec(v_a_2992_);
v___y_2831_ = v___x_3010_;
v___y_2832_ = v___y_2977_;
v___y_2833_ = v___x_3009_;
goto v___jp_2830_;
}
else
{
uint8_t v___x_3011_; 
v___x_3011_ = lean_unbox(v_a_2992_);
lean_dec(v_a_2992_);
lean_inc_ref(v_run_x27_3001_);
v___y_2916_ = v___x_3011_;
v___y_2917_ = v___y_2983_;
v___y_2918_ = v___y_2985_;
v___y_2919_ = v_hasTrace_2997_;
v___y_2920_ = v___x_3006_;
v___y_2921_ = v___y_2988_;
v___y_2922_ = v___y_2986_;
v___y_2923_ = v___y_2981_;
v___y_2924_ = v___y_2979_;
v___y_2925_ = v_options_2996_;
v___y_2926_ = v_run_x27_3001_;
v___y_2927_ = v___y_2977_;
v___y_2928_ = v___y_2984_;
v___y_2929_ = v___y_2978_;
v___y_2930_ = v___x_3004_;
v___y_2931_ = v___f_3003_;
v___y_2932_ = v___y_2987_;
v___y_2933_ = v___y_2982_;
v___y_2934_ = v___y_2980_;
goto v___jp_2915_;
}
}
else
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_unbox(v_a_2992_);
lean_dec(v_a_2992_);
lean_inc_ref(v_run_x27_3001_);
v___y_2916_ = v___x_3012_;
v___y_2917_ = v___y_2983_;
v___y_2918_ = v___y_2985_;
v___y_2919_ = v_hasTrace_2997_;
v___y_2920_ = v___x_3006_;
v___y_2921_ = v___y_2988_;
v___y_2922_ = v___y_2986_;
v___y_2923_ = v___y_2981_;
v___y_2924_ = v___y_2979_;
v___y_2925_ = v_options_2996_;
v___y_2926_ = v_run_x27_3001_;
v___y_2927_ = v___y_2977_;
v___y_2928_ = v___y_2984_;
v___y_2929_ = v___y_2978_;
v___y_2930_ = v___x_3004_;
v___y_2931_ = v___f_3003_;
v___y_2932_ = v___y_2987_;
v___y_2933_ = v___y_2982_;
v___y_2934_ = v___y_2980_;
goto v___jp_2915_;
}
}
}
}
else
{
lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v_a_2992_);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; 
v_unused_3021_ = lean_ctor_get(v___x_2991_, 0);
lean_dec(v_unused_3021_);
v___x_3014_ = v___x_2991_;
v_isShared_3015_ = v_isSharedCheck_3020_;
goto v_resetjp_3013_;
}
else
{
lean_dec(v___x_2991_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3020_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3016_ = lean_box(v___y_2977_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3016_);
v___x_3018_ = v___x_3014_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
return v___x_2991_;
}
}
v___jp_3022_:
{
if (lean_obj_tag(v___y_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3046_; 
v_a_3037_ = lean_ctor_get(v___y_3036_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___y_3036_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3039_ = v___y_3036_;
v_isShared_3040_ = v_isSharedCheck_3046_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___y_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3046_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
uint8_t v___x_3041_; 
v___x_3041_ = lean_unbox(v_a_3037_);
lean_dec(v_a_3037_);
if (v___x_3041_ == 0)
{
lean_del_object(v___x_3039_);
v___y_2976_ = v___y_3028_;
v___y_2977_ = v___y_3029_;
v___y_2978_ = v___y_3023_;
v___y_2979_ = v___y_3032_;
v___y_2980_ = v___y_3030_;
v___y_2981_ = v___y_3035_;
v___y_2982_ = v___y_3031_;
v___y_2983_ = v___y_3033_;
v___y_2984_ = v___y_3024_;
v___y_2985_ = v___y_3025_;
v___y_2986_ = v___y_3026_;
v___y_2987_ = v___y_3027_;
v___y_2988_ = v___y_3034_;
goto v___jp_2975_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3042_ = lean_box(v___y_3029_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3042_);
v___x_3044_ = v___x_3039_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
return v___y_3036_;
}
}
v___jp_3047_:
{
lean_object* v___x_3069_; double v___x_3070_; double v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3069_ = lean_io_get_num_heartbeats();
v___x_3070_ = lean_float_of_nat(v___y_3048_);
v___x_3071_ = lean_float_of_nat(v___x_3069_);
v___x_3072_ = lean_box_float(v___x_3070_);
v___x_3073_ = lean_box_float(v___x_3071_);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3072_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v_a_3068_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
lean_inc_ref(v___y_3056_);
lean_inc_ref(v___y_3050_);
v___x_3076_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3060_, v___y_3050_, v___y_3051_, v___y_3059_, v___y_3062_, v___y_3056_, v___x_3075_, v___y_3049_, v___y_3065_, v___y_3061_, v___y_3067_, v___y_3063_, v___y_3066_, v___y_3052_, v___y_3054_, v___y_3053_, v___y_3055_, v___y_3064_);
v___y_3023_ = v___y_3049_;
v___y_3024_ = v___y_3052_;
v___y_3025_ = v___y_3054_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v___y_3055_;
v___y_3028_ = v___y_3057_;
v___y_3029_ = v___y_3058_;
v___y_3030_ = v___y_3061_;
v___y_3031_ = v___y_3063_;
v___y_3032_ = v___y_3065_;
v___y_3033_ = v___y_3066_;
v___y_3034_ = v___y_3064_;
v___y_3035_ = v___y_3067_;
v___y_3036_ = v___x_3076_;
goto v___jp_3022_;
}
v___jp_3077_:
{
lean_object* v___x_3099_; double v___x_3100_; double v___x_3101_; double v___x_3102_; double v___x_3103_; double v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3099_ = lean_io_mono_nanos_now();
v___x_3100_ = lean_float_of_nat(v___y_3081_);
v___x_3101_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3102_ = lean_float_div(v___x_3100_, v___x_3101_);
v___x_3103_ = lean_float_of_nat(v___x_3099_);
v___x_3104_ = lean_float_div(v___x_3103_, v___x_3101_);
v___x_3105_ = lean_box_float(v___x_3102_);
v___x_3106_ = lean_box_float(v___x_3104_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_a_3098_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
lean_inc_ref(v___y_3086_);
lean_inc_ref(v___y_3079_);
v___x_3109_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3090_, v___y_3079_, v___y_3080_, v___y_3089_, v___y_3092_, v___y_3086_, v___x_3108_, v___y_3078_, v___y_3095_, v___y_3091_, v___y_3097_, v___y_3093_, v___y_3096_, v___y_3082_, v___y_3084_, v___y_3083_, v___y_3085_, v___y_3094_);
v___y_3023_ = v___y_3078_;
v___y_3024_ = v___y_3082_;
v___y_3025_ = v___y_3084_;
v___y_3026_ = v___y_3083_;
v___y_3027_ = v___y_3085_;
v___y_3028_ = v___y_3087_;
v___y_3029_ = v___y_3088_;
v___y_3030_ = v___y_3091_;
v___y_3031_ = v___y_3093_;
v___y_3032_ = v___y_3095_;
v___y_3033_ = v___y_3096_;
v___y_3034_ = v___y_3094_;
v___y_3035_ = v___y_3097_;
v___y_3036_ = v___x_3109_;
goto v___jp_3022_;
}
v___jp_3110_:
{
lean_object* v___x_3130_; lean_object* v_a_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3130_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_3127_);
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref(v___x_3130_);
v___x_3132_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3133_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3113_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_io_mono_nanos_now();
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3117_);
lean_inc(v___y_3116_);
lean_inc_ref(v___y_3115_);
lean_inc(v___y_3114_);
lean_inc_ref(v___y_3126_);
lean_inc(v___y_3124_);
lean_inc_ref(v___y_3129_);
lean_inc(v___y_3123_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3111_);
v___x_3135_ = lean_apply_12(v___y_3128_, v___y_3111_, v___y_3125_, v___y_3123_, v___y_3129_, v___y_3124_, v___y_3126_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3127_, lean_box(0));
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set_tag(v___x_3138_, 1);
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
v___y_3078_ = v___y_3111_;
v___y_3079_ = v___y_3112_;
v___y_3080_ = v___y_3113_;
v___y_3081_ = v___x_3134_;
v___y_3082_ = v___y_3114_;
v___y_3083_ = v___y_3116_;
v___y_3084_ = v___y_3115_;
v___y_3085_ = v___y_3117_;
v___y_3086_ = v___y_3118_;
v___y_3087_ = v___y_3119_;
v___y_3088_ = v___y_3121_;
v___y_3089_ = v___y_3120_;
v___y_3090_ = v___y_3122_;
v___y_3091_ = v___y_3123_;
v___y_3092_ = v_a_3131_;
v___y_3093_ = v___y_3124_;
v___y_3094_ = v___y_3127_;
v___y_3095_ = v___y_3125_;
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3129_;
v_a_3098_ = v___x_3141_;
goto v___jp_3077_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_a_3144_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3135_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3135_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set_tag(v___x_3146_, 0);
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
v___y_3078_ = v___y_3111_;
v___y_3079_ = v___y_3112_;
v___y_3080_ = v___y_3113_;
v___y_3081_ = v___x_3134_;
v___y_3082_ = v___y_3114_;
v___y_3083_ = v___y_3116_;
v___y_3084_ = v___y_3115_;
v___y_3085_ = v___y_3117_;
v___y_3086_ = v___y_3118_;
v___y_3087_ = v___y_3119_;
v___y_3088_ = v___y_3121_;
v___y_3089_ = v___y_3120_;
v___y_3090_ = v___y_3122_;
v___y_3091_ = v___y_3123_;
v___y_3092_ = v_a_3131_;
v___y_3093_ = v___y_3124_;
v___y_3094_ = v___y_3127_;
v___y_3095_ = v___y_3125_;
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3129_;
v_a_3098_ = v___x_3149_;
goto v___jp_3077_;
}
}
}
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3117_);
lean_inc(v___y_3116_);
lean_inc_ref(v___y_3115_);
lean_inc(v___y_3114_);
lean_inc_ref(v___y_3126_);
lean_inc(v___y_3124_);
lean_inc_ref(v___y_3129_);
lean_inc(v___y_3123_);
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3111_);
v___x_3153_ = lean_apply_12(v___y_3128_, v___y_3111_, v___y_3125_, v___y_3123_, v___y_3129_, v___y_3124_, v___y_3126_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3127_, lean_box(0));
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 1);
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
v___y_3048_ = v___x_3152_;
v___y_3049_ = v___y_3111_;
v___y_3050_ = v___y_3112_;
v___y_3051_ = v___y_3113_;
v___y_3052_ = v___y_3114_;
v___y_3053_ = v___y_3116_;
v___y_3054_ = v___y_3115_;
v___y_3055_ = v___y_3117_;
v___y_3056_ = v___y_3118_;
v___y_3057_ = v___y_3119_;
v___y_3058_ = v___y_3121_;
v___y_3059_ = v___y_3120_;
v___y_3060_ = v___y_3122_;
v___y_3061_ = v___y_3123_;
v___y_3062_ = v_a_3131_;
v___y_3063_ = v___y_3124_;
v___y_3064_ = v___y_3127_;
v___y_3065_ = v___y_3125_;
v___y_3066_ = v___y_3126_;
v___y_3067_ = v___y_3129_;
v_a_3068_ = v___x_3159_;
goto v___jp_3047_;
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3153_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3153_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set_tag(v___x_3164_, 0);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
v___y_3048_ = v___x_3152_;
v___y_3049_ = v___y_3111_;
v___y_3050_ = v___y_3112_;
v___y_3051_ = v___y_3113_;
v___y_3052_ = v___y_3114_;
v___y_3053_ = v___y_3116_;
v___y_3054_ = v___y_3115_;
v___y_3055_ = v___y_3117_;
v___y_3056_ = v___y_3118_;
v___y_3057_ = v___y_3119_;
v___y_3058_ = v___y_3121_;
v___y_3059_ = v___y_3120_;
v___y_3060_ = v___y_3122_;
v___y_3061_ = v___y_3123_;
v___y_3062_ = v_a_3131_;
v___y_3063_ = v___y_3124_;
v___y_3064_ = v___y_3127_;
v___y_3065_ = v___y_3125_;
v___y_3066_ = v___y_3126_;
v___y_3067_ = v___y_3129_;
v_a_3068_ = v___x_3167_;
goto v___jp_3047_;
}
}
}
}
}
v___jp_3170_:
{
if (v_fixedInt_3172_ == 0)
{
v___y_2976_ = v___y_3171_;
v___y_2977_ = v___y_3173_;
v___y_2978_ = v___y_3174_;
v___y_2979_ = v___y_3175_;
v___y_2980_ = v___y_3176_;
v___y_2981_ = v___y_3177_;
v___y_2982_ = v___y_3178_;
v___y_2983_ = v___y_3179_;
v___y_2984_ = v___y_3180_;
v___y_2985_ = v___y_3181_;
v___y_2986_ = v___y_3182_;
v___y_2987_ = v___y_3183_;
v___y_2988_ = v___y_3184_;
goto v___jp_2975_;
}
else
{
lean_object* v___x_3185_; lean_object* v_options_3186_; uint8_t v_hasTrace_3187_; 
v___x_3185_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass;
v_options_3186_ = lean_ctor_get(v___y_3183_, 2);
v_hasTrace_3187_ = lean_ctor_get_uint8(v_options_3186_, sizeof(void*)*1);
if (v_hasTrace_3187_ == 0)
{
lean_object* v_run_x27_3188_; lean_object* v___x_3189_; 
v_run_x27_3188_ = lean_ctor_get(v___x_3185_, 1);
lean_inc_ref(v_run_x27_3188_);
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc(v___y_3175_);
lean_inc_ref(v___y_3174_);
v___x_3189_ = lean_apply_12(v_run_x27_3188_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, lean_box(0));
v___y_3023_ = v___y_3174_;
v___y_3024_ = v___y_3180_;
v___y_3025_ = v___y_3181_;
v___y_3026_ = v___y_3182_;
v___y_3027_ = v___y_3183_;
v___y_3028_ = v___y_3171_;
v___y_3029_ = v___y_3173_;
v___y_3030_ = v___y_3176_;
v___y_3031_ = v___y_3178_;
v___y_3032_ = v___y_3175_;
v___y_3033_ = v___y_3179_;
v___y_3034_ = v___y_3184_;
v___y_3035_ = v___y_3177_;
v___y_3036_ = v___x_3189_;
goto v___jp_3022_;
}
else
{
lean_object* v_run_x27_3190_; lean_object* v_inheritedTraceOptions_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v_run_x27_3190_ = lean_ctor_get(v___x_3185_, 1);
v_inheritedTraceOptions_3191_ = lean_ctor_get(v___y_3183_, 13);
v___f_3192_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__4);
v___x_3193_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3194_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3195_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3191_, v_options_3186_, v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; uint8_t v___x_3197_; 
v___x_3196_ = l_Lean_trace_profiler;
v___x_3197_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_3186_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; 
lean_inc_ref(v_run_x27_3190_);
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc(v___y_3175_);
lean_inc_ref(v___y_3174_);
v___x_3198_ = lean_apply_12(v_run_x27_3190_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, lean_box(0));
v___y_3023_ = v___y_3174_;
v___y_3024_ = v___y_3180_;
v___y_3025_ = v___y_3181_;
v___y_3026_ = v___y_3182_;
v___y_3027_ = v___y_3183_;
v___y_3028_ = v___y_3171_;
v___y_3029_ = v___y_3173_;
v___y_3030_ = v___y_3176_;
v___y_3031_ = v___y_3178_;
v___y_3032_ = v___y_3175_;
v___y_3033_ = v___y_3179_;
v___y_3034_ = v___y_3184_;
v___y_3035_ = v___y_3177_;
v___y_3036_ = v___x_3198_;
goto v___jp_3022_;
}
else
{
lean_inc_ref(v_run_x27_3190_);
v___y_3111_ = v___y_3174_;
v___y_3112_ = v___x_3193_;
v___y_3113_ = v_options_3186_;
v___y_3114_ = v___y_3180_;
v___y_3115_ = v___y_3181_;
v___y_3116_ = v___y_3182_;
v___y_3117_ = v___y_3183_;
v___y_3118_ = v___f_3192_;
v___y_3119_ = v___y_3171_;
v___y_3120_ = v___x_3195_;
v___y_3121_ = v___y_3173_;
v___y_3122_ = v_hasTrace_3187_;
v___y_3123_ = v___y_3176_;
v___y_3124_ = v___y_3178_;
v___y_3125_ = v___y_3175_;
v___y_3126_ = v___y_3179_;
v___y_3127_ = v___y_3184_;
v___y_3128_ = v_run_x27_3190_;
v___y_3129_ = v___y_3177_;
goto v___jp_3110_;
}
}
else
{
lean_inc_ref(v_run_x27_3190_);
v___y_3111_ = v___y_3174_;
v___y_3112_ = v___x_3193_;
v___y_3113_ = v_options_3186_;
v___y_3114_ = v___y_3180_;
v___y_3115_ = v___y_3181_;
v___y_3116_ = v___y_3182_;
v___y_3117_ = v___y_3183_;
v___y_3118_ = v___f_3192_;
v___y_3119_ = v___y_3171_;
v___y_3120_ = v___x_3195_;
v___y_3121_ = v___y_3173_;
v___y_3122_ = v_hasTrace_3187_;
v___y_3123_ = v___y_3176_;
v___y_3124_ = v___y_3178_;
v___y_3125_ = v___y_3175_;
v___y_3126_ = v___y_3179_;
v___y_3127_ = v___y_3184_;
v___y_3128_ = v_run_x27_3190_;
v___y_3129_ = v___y_3177_;
goto v___jp_3110_;
}
}
}
}
v___jp_3199_:
{
if (lean_obj_tag(v___y_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3224_; 
v_a_3214_ = lean_ctor_get(v___y_3213_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___y_3213_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3216_ = v___y_3213_;
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___y_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
uint8_t v___x_3218_; 
v___x_3218_ = lean_unbox(v_a_3214_);
lean_dec(v_a_3214_);
if (v___x_3218_ == 0)
{
uint8_t v_fixedInt_3219_; 
lean_del_object(v___x_3216_);
v_fixedInt_3219_ = lean_ctor_get_uint8(v___y_3209_, sizeof(void*)*2 + 6);
v___y_3171_ = v___y_3209_;
v_fixedInt_3172_ = v_fixedInt_3219_;
v___y_3173_ = v___y_3210_;
v___y_3174_ = v___y_3207_;
v___y_3175_ = v___y_3203_;
v___y_3176_ = v___y_3202_;
v___y_3177_ = v___y_3212_;
v___y_3178_ = v___y_3206_;
v___y_3179_ = v___y_3200_;
v___y_3180_ = v___y_3211_;
v___y_3181_ = v___y_3205_;
v___y_3182_ = v___y_3201_;
v___y_3183_ = v___y_3208_;
v___y_3184_ = v___y_3204_;
goto v___jp_3170_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3220_ = lean_box(v___y_3210_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3220_);
v___x_3222_ = v___x_3216_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
return v___y_3213_;
}
}
v___jp_3225_:
{
lean_object* v___x_3247_; double v___x_3248_; double v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3247_ = lean_io_get_num_heartbeats();
v___x_3248_ = lean_float_of_nat(v___y_3242_);
v___x_3249_ = lean_float_of_nat(v___x_3247_);
v___x_3250_ = lean_box_float(v___x_3248_);
v___x_3251_ = lean_box_float(v___x_3249_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v_a_3246_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
lean_inc_ref(v___y_3228_);
lean_inc_ref(v___y_3243_);
v___x_3254_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3238_, v___y_3243_, v___y_3230_, v___y_3240_, v___y_3244_, v___y_3228_, v___x_3253_, v___y_3235_, v___y_3232_, v___y_3229_, v___y_3245_, v___y_3234_, v___y_3227_, v___y_3241_, v___y_3233_, v___y_3226_, v___y_3237_, v___y_3231_);
v___y_3200_ = v___y_3227_;
v___y_3201_ = v___y_3226_;
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3232_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3233_;
v___y_3206_ = v___y_3234_;
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3237_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3239_;
v___y_3211_ = v___y_3241_;
v___y_3212_ = v___y_3245_;
v___y_3213_ = v___x_3254_;
goto v___jp_3199_;
}
v___jp_3255_:
{
lean_object* v___x_3277_; double v___x_3278_; double v___x_3279_; double v___x_3280_; double v___x_3281_; double v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3277_ = lean_io_mono_nanos_now();
v___x_3278_ = lean_float_of_nat(v___y_3272_);
v___x_3279_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3280_ = lean_float_div(v___x_3278_, v___x_3279_);
v___x_3281_ = lean_float_of_nat(v___x_3277_);
v___x_3282_ = lean_float_div(v___x_3281_, v___x_3279_);
v___x_3283_ = lean_box_float(v___x_3280_);
v___x_3284_ = lean_box_float(v___x_3282_);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v_a_3276_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
lean_inc_ref(v___y_3258_);
lean_inc_ref(v___y_3273_);
v___x_3287_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3268_, v___y_3273_, v___y_3260_, v___y_3270_, v___y_3274_, v___y_3258_, v___x_3286_, v___y_3265_, v___y_3262_, v___y_3259_, v___y_3275_, v___y_3264_, v___y_3257_, v___y_3271_, v___y_3263_, v___y_3256_, v___y_3267_, v___y_3261_);
v___y_3200_ = v___y_3257_;
v___y_3201_ = v___y_3256_;
v___y_3202_ = v___y_3259_;
v___y_3203_ = v___y_3262_;
v___y_3204_ = v___y_3261_;
v___y_3205_ = v___y_3263_;
v___y_3206_ = v___y_3264_;
v___y_3207_ = v___y_3265_;
v___y_3208_ = v___y_3267_;
v___y_3209_ = v___y_3266_;
v___y_3210_ = v___y_3269_;
v___y_3211_ = v___y_3271_;
v___y_3212_ = v___y_3275_;
v___y_3213_ = v___x_3287_;
goto v___jp_3199_;
}
v___jp_3288_:
{
lean_object* v___x_3308_; lean_object* v_a_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3308_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_3296_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref(v___x_3308_);
v___x_3310_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3311_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3294_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_io_mono_nanos_now();
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3301_);
lean_inc(v___y_3290_);
lean_inc_ref(v___y_3297_);
lean_inc(v___y_3305_);
lean_inc_ref(v___y_3289_);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3307_);
lean_inc(v___y_3292_);
lean_inc(v___y_3295_);
lean_inc_ref(v___y_3299_);
v___x_3313_ = lean_apply_12(v___y_3293_, v___y_3299_, v___y_3295_, v___y_3292_, v___y_3307_, v___y_3298_, v___y_3289_, v___y_3305_, v___y_3297_, v___y_3290_, v___y_3301_, v___y_3296_, lean_box(0));
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set_tag(v___x_3316_, 1);
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
v___y_3256_ = v___y_3290_;
v___y_3257_ = v___y_3289_;
v___y_3258_ = v___y_3291_;
v___y_3259_ = v___y_3292_;
v___y_3260_ = v___y_3294_;
v___y_3261_ = v___y_3296_;
v___y_3262_ = v___y_3295_;
v___y_3263_ = v___y_3297_;
v___y_3264_ = v___y_3298_;
v___y_3265_ = v___y_3299_;
v___y_3266_ = v___y_3300_;
v___y_3267_ = v___y_3301_;
v___y_3268_ = v___y_3302_;
v___y_3269_ = v___y_3303_;
v___y_3270_ = v___y_3304_;
v___y_3271_ = v___y_3305_;
v___y_3272_ = v___x_3312_;
v___y_3273_ = v___y_3306_;
v___y_3274_ = v_a_3309_;
v___y_3275_ = v___y_3307_;
v_a_3276_ = v___x_3319_;
goto v___jp_3255_;
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
v_a_3322_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3313_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3313_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 0);
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
v___y_3256_ = v___y_3290_;
v___y_3257_ = v___y_3289_;
v___y_3258_ = v___y_3291_;
v___y_3259_ = v___y_3292_;
v___y_3260_ = v___y_3294_;
v___y_3261_ = v___y_3296_;
v___y_3262_ = v___y_3295_;
v___y_3263_ = v___y_3297_;
v___y_3264_ = v___y_3298_;
v___y_3265_ = v___y_3299_;
v___y_3266_ = v___y_3300_;
v___y_3267_ = v___y_3301_;
v___y_3268_ = v___y_3302_;
v___y_3269_ = v___y_3303_;
v___y_3270_ = v___y_3304_;
v___y_3271_ = v___y_3305_;
v___y_3272_ = v___x_3312_;
v___y_3273_ = v___y_3306_;
v___y_3274_ = v_a_3309_;
v___y_3275_ = v___y_3307_;
v_a_3276_ = v___x_3327_;
goto v___jp_3255_;
}
}
}
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3301_);
lean_inc(v___y_3290_);
lean_inc_ref(v___y_3297_);
lean_inc(v___y_3305_);
lean_inc_ref(v___y_3289_);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3307_);
lean_inc(v___y_3292_);
lean_inc(v___y_3295_);
lean_inc_ref(v___y_3299_);
v___x_3331_ = lean_apply_12(v___y_3293_, v___y_3299_, v___y_3295_, v___y_3292_, v___y_3307_, v___y_3298_, v___y_3289_, v___y_3305_, v___y_3297_, v___y_3290_, v___y_3301_, v___y_3296_, lean_box(0));
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
lean_ctor_set_tag(v___x_3334_, 1);
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
v___y_3226_ = v___y_3290_;
v___y_3227_ = v___y_3289_;
v___y_3228_ = v___y_3291_;
v___y_3229_ = v___y_3292_;
v___y_3230_ = v___y_3294_;
v___y_3231_ = v___y_3296_;
v___y_3232_ = v___y_3295_;
v___y_3233_ = v___y_3297_;
v___y_3234_ = v___y_3298_;
v___y_3235_ = v___y_3299_;
v___y_3236_ = v___y_3300_;
v___y_3237_ = v___y_3301_;
v___y_3238_ = v___y_3302_;
v___y_3239_ = v___y_3303_;
v___y_3240_ = v___y_3304_;
v___y_3241_ = v___y_3305_;
v___y_3242_ = v___x_3330_;
v___y_3243_ = v___y_3306_;
v___y_3244_ = v_a_3309_;
v___y_3245_ = v___y_3307_;
v_a_3246_ = v___x_3337_;
goto v___jp_3225_;
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
v_a_3340_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3331_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3331_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set_tag(v___x_3342_, 0);
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
v___y_3226_ = v___y_3290_;
v___y_3227_ = v___y_3289_;
v___y_3228_ = v___y_3291_;
v___y_3229_ = v___y_3292_;
v___y_3230_ = v___y_3294_;
v___y_3231_ = v___y_3296_;
v___y_3232_ = v___y_3295_;
v___y_3233_ = v___y_3297_;
v___y_3234_ = v___y_3298_;
v___y_3235_ = v___y_3299_;
v___y_3236_ = v___y_3300_;
v___y_3237_ = v___y_3301_;
v___y_3238_ = v___y_3302_;
v___y_3239_ = v___y_3303_;
v___y_3240_ = v___y_3304_;
v___y_3241_ = v___y_3305_;
v___y_3242_ = v___x_3330_;
v___y_3243_ = v___y_3306_;
v___y_3244_ = v_a_3309_;
v___y_3245_ = v___y_3307_;
v_a_3246_ = v___x_3345_;
goto v___jp_3225_;
}
}
}
}
}
v___jp_3348_:
{
if (v_enums_3351_ == 0)
{
v___y_3171_ = v___y_3349_;
v_fixedInt_3172_ = v_fixedInt_3350_;
v___y_3173_ = v___y_3352_;
v___y_3174_ = v___y_3353_;
v___y_3175_ = v___y_3354_;
v___y_3176_ = v___y_3355_;
v___y_3177_ = v___y_3356_;
v___y_3178_ = v___y_3357_;
v___y_3179_ = v___y_3358_;
v___y_3180_ = v___y_3359_;
v___y_3181_ = v___y_3360_;
v___y_3182_ = v___y_3361_;
v___y_3183_ = v___y_3362_;
v___y_3184_ = v___y_3363_;
goto v___jp_3170_;
}
else
{
lean_object* v___x_3364_; lean_object* v_options_3365_; uint8_t v_hasTrace_3366_; 
v___x_3364_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumsPass;
v_options_3365_ = lean_ctor_get(v___y_3362_, 2);
v_hasTrace_3366_ = lean_ctor_get_uint8(v_options_3365_, sizeof(void*)*1);
if (v_hasTrace_3366_ == 0)
{
lean_object* v_run_x27_3367_; lean_object* v___x_3368_; 
v_run_x27_3367_ = lean_ctor_get(v___x_3364_, 1);
lean_inc_ref(v_run_x27_3367_);
lean_inc(v___y_3363_);
lean_inc_ref(v___y_3362_);
lean_inc(v___y_3361_);
lean_inc_ref(v___y_3360_);
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
lean_inc(v___y_3355_);
lean_inc(v___y_3354_);
lean_inc_ref(v___y_3353_);
v___x_3368_ = lean_apply_12(v_run_x27_3367_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, lean_box(0));
v___y_3200_ = v___y_3358_;
v___y_3201_ = v___y_3361_;
v___y_3202_ = v___y_3355_;
v___y_3203_ = v___y_3354_;
v___y_3204_ = v___y_3363_;
v___y_3205_ = v___y_3360_;
v___y_3206_ = v___y_3357_;
v___y_3207_ = v___y_3353_;
v___y_3208_ = v___y_3362_;
v___y_3209_ = v___y_3349_;
v___y_3210_ = v___y_3352_;
v___y_3211_ = v___y_3359_;
v___y_3212_ = v___y_3356_;
v___y_3213_ = v___x_3368_;
goto v___jp_3199_;
}
else
{
lean_object* v_run_x27_3369_; lean_object* v_inheritedTraceOptions_3370_; lean_object* v___f_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v_run_x27_3369_ = lean_ctor_get(v___x_3364_, 1);
v_inheritedTraceOptions_3370_ = lean_ctor_get(v___y_3362_, 13);
v___f_3371_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__5);
v___x_3372_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3373_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3374_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3370_, v_options_3365_, v___x_3373_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; uint8_t v___x_3376_; 
v___x_3375_ = l_Lean_trace_profiler;
v___x_3376_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_3365_, v___x_3375_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; 
lean_inc_ref(v_run_x27_3369_);
lean_inc(v___y_3363_);
lean_inc_ref(v___y_3362_);
lean_inc(v___y_3361_);
lean_inc_ref(v___y_3360_);
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
lean_inc(v___y_3355_);
lean_inc(v___y_3354_);
lean_inc_ref(v___y_3353_);
v___x_3377_ = lean_apply_12(v_run_x27_3369_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, lean_box(0));
v___y_3200_ = v___y_3358_;
v___y_3201_ = v___y_3361_;
v___y_3202_ = v___y_3355_;
v___y_3203_ = v___y_3354_;
v___y_3204_ = v___y_3363_;
v___y_3205_ = v___y_3360_;
v___y_3206_ = v___y_3357_;
v___y_3207_ = v___y_3353_;
v___y_3208_ = v___y_3362_;
v___y_3209_ = v___y_3349_;
v___y_3210_ = v___y_3352_;
v___y_3211_ = v___y_3359_;
v___y_3212_ = v___y_3356_;
v___y_3213_ = v___x_3377_;
goto v___jp_3199_;
}
else
{
lean_inc_ref(v_run_x27_3369_);
v___y_3289_ = v___y_3358_;
v___y_3290_ = v___y_3361_;
v___y_3291_ = v___f_3371_;
v___y_3292_ = v___y_3355_;
v___y_3293_ = v_run_x27_3369_;
v___y_3294_ = v_options_3365_;
v___y_3295_ = v___y_3354_;
v___y_3296_ = v___y_3363_;
v___y_3297_ = v___y_3360_;
v___y_3298_ = v___y_3357_;
v___y_3299_ = v___y_3353_;
v___y_3300_ = v___y_3349_;
v___y_3301_ = v___y_3362_;
v___y_3302_ = v_hasTrace_3366_;
v___y_3303_ = v___y_3352_;
v___y_3304_ = v___x_3374_;
v___y_3305_ = v___y_3359_;
v___y_3306_ = v___x_3372_;
v___y_3307_ = v___y_3356_;
goto v___jp_3288_;
}
}
else
{
lean_inc_ref(v_run_x27_3369_);
v___y_3289_ = v___y_3358_;
v___y_3290_ = v___y_3361_;
v___y_3291_ = v___f_3371_;
v___y_3292_ = v___y_3355_;
v___y_3293_ = v_run_x27_3369_;
v___y_3294_ = v_options_3365_;
v___y_3295_ = v___y_3354_;
v___y_3296_ = v___y_3363_;
v___y_3297_ = v___y_3360_;
v___y_3298_ = v___y_3357_;
v___y_3299_ = v___y_3353_;
v___y_3300_ = v___y_3349_;
v___y_3301_ = v___y_3362_;
v___y_3302_ = v_hasTrace_3366_;
v___y_3303_ = v___y_3352_;
v___y_3304_ = v___x_3374_;
v___y_3305_ = v___y_3359_;
v___y_3306_ = v___x_3372_;
v___y_3307_ = v___y_3356_;
goto v___jp_3288_;
}
}
}
}
v___jp_3378_:
{
if (lean_obj_tag(v___y_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3404_; 
v_a_3393_ = lean_ctor_get(v___y_3392_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___y_3392_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3395_ = v___y_3392_;
v_isShared_3396_ = v_isSharedCheck_3404_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___y_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3404_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
uint8_t v___x_3397_; 
v___x_3397_ = lean_unbox(v_a_3393_);
lean_dec(v_a_3393_);
if (v___x_3397_ == 0)
{
uint8_t v_fixedInt_3398_; uint8_t v_enums_3399_; 
lean_del_object(v___x_3395_);
v_fixedInt_3398_ = lean_ctor_get_uint8(v___y_3386_, sizeof(void*)*2 + 6);
v_enums_3399_ = lean_ctor_get_uint8(v___y_3386_, sizeof(void*)*2 + 7);
v___y_3349_ = v___y_3386_;
v_fixedInt_3350_ = v_fixedInt_3398_;
v_enums_3351_ = v_enums_3399_;
v___y_3352_ = v___y_3388_;
v___y_3353_ = v___y_3387_;
v___y_3354_ = v___y_3384_;
v___y_3355_ = v___y_3379_;
v___y_3356_ = v___y_3382_;
v___y_3357_ = v___y_3380_;
v___y_3358_ = v___y_3385_;
v___y_3359_ = v___y_3389_;
v___y_3360_ = v___y_3381_;
v___y_3361_ = v___y_3391_;
v___y_3362_ = v___y_3390_;
v___y_3363_ = v___y_3383_;
goto v___jp_3348_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3400_ = lean_box(v___y_3388_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3400_);
v___x_3402_ = v___x_3395_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
return v___y_3392_;
}
}
v___jp_3405_:
{
lean_object* v___x_3427_; double v___x_3428_; double v___x_3429_; double v___x_3430_; double v___x_3431_; double v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3427_ = lean_io_mono_nanos_now();
v___x_3428_ = lean_float_of_nat(v___y_3413_);
v___x_3429_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3430_ = lean_float_div(v___x_3428_, v___x_3429_);
v___x_3431_ = lean_float_of_nat(v___x_3427_);
v___x_3432_ = lean_float_div(v___x_3431_, v___x_3429_);
v___x_3433_ = lean_box_float(v___x_3430_);
v___x_3434_ = lean_box_float(v___x_3432_);
v___x_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3433_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_a_3426_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
lean_inc_ref(v___y_3421_);
lean_inc_ref(v___y_3408_);
v___x_3437_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3423_, v___y_3408_, v___y_3410_, v___y_3418_, v___y_3415_, v___y_3421_, v___x_3436_, v___y_3419_, v___y_3414_, v___y_3406_, v___y_3411_, v___y_3409_, v___y_3416_, v___y_3422_, v___y_3407_, v___y_3425_, v___y_3424_, v___y_3412_);
v___y_3379_ = v___y_3406_;
v___y_3380_ = v___y_3409_;
v___y_3381_ = v___y_3407_;
v___y_3382_ = v___y_3411_;
v___y_3383_ = v___y_3412_;
v___y_3384_ = v___y_3414_;
v___y_3385_ = v___y_3416_;
v___y_3386_ = v___y_3417_;
v___y_3387_ = v___y_3419_;
v___y_3388_ = v___y_3420_;
v___y_3389_ = v___y_3422_;
v___y_3390_ = v___y_3424_;
v___y_3391_ = v___y_3425_;
v___y_3392_ = v___x_3437_;
goto v___jp_3378_;
}
v___jp_3438_:
{
lean_object* v___x_3460_; double v___x_3461_; double v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3460_ = lean_io_get_num_heartbeats();
v___x_3461_ = lean_float_of_nat(v___y_3455_);
v___x_3462_ = lean_float_of_nat(v___x_3460_);
v___x_3463_ = lean_box_float(v___x_3461_);
v___x_3464_ = lean_box_float(v___x_3462_);
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3463_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v_a_3459_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
lean_inc_ref(v___y_3453_);
lean_inc_ref(v___y_3441_);
v___x_3467_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3456_, v___y_3441_, v___y_3443_, v___y_3450_, v___y_3447_, v___y_3453_, v___x_3466_, v___y_3451_, v___y_3446_, v___y_3439_, v___y_3444_, v___y_3442_, v___y_3448_, v___y_3454_, v___y_3440_, v___y_3458_, v___y_3457_, v___y_3445_);
v___y_3379_ = v___y_3439_;
v___y_3380_ = v___y_3442_;
v___y_3381_ = v___y_3440_;
v___y_3382_ = v___y_3444_;
v___y_3383_ = v___y_3445_;
v___y_3384_ = v___y_3446_;
v___y_3385_ = v___y_3448_;
v___y_3386_ = v___y_3449_;
v___y_3387_ = v___y_3451_;
v___y_3388_ = v___y_3452_;
v___y_3389_ = v___y_3454_;
v___y_3390_ = v___y_3457_;
v___y_3391_ = v___y_3458_;
v___y_3392_ = v___x_3467_;
goto v___jp_3378_;
}
v___jp_3468_:
{
lean_object* v___x_3488_; lean_object* v_a_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3488_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_3476_);
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v___x_3488_);
v___x_3490_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3491_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3473_, v___x_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_io_mono_nanos_now();
lean_inc(v___y_3476_);
lean_inc_ref(v___y_3486_);
lean_inc(v___y_3487_);
lean_inc_ref(v___y_3472_);
lean_inc(v___y_3484_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3474_);
lean_inc(v___y_3469_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3481_);
v___x_3493_ = lean_apply_12(v___y_3475_, v___y_3481_, v___y_3477_, v___y_3469_, v___y_3474_, v___y_3471_, v___y_3478_, v___y_3484_, v___y_3472_, v___y_3487_, v___y_3486_, v___y_3476_, lean_box(0));
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set_tag(v___x_3496_, 1);
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
v___y_3406_ = v___y_3469_;
v___y_3407_ = v___y_3472_;
v___y_3408_ = v___y_3470_;
v___y_3409_ = v___y_3471_;
v___y_3410_ = v___y_3473_;
v___y_3411_ = v___y_3474_;
v___y_3412_ = v___y_3476_;
v___y_3413_ = v___x_3492_;
v___y_3414_ = v___y_3477_;
v___y_3415_ = v_a_3489_;
v___y_3416_ = v___y_3478_;
v___y_3417_ = v___y_3480_;
v___y_3418_ = v___y_3479_;
v___y_3419_ = v___y_3481_;
v___y_3420_ = v___y_3483_;
v___y_3421_ = v___y_3482_;
v___y_3422_ = v___y_3484_;
v___y_3423_ = v___y_3485_;
v___y_3424_ = v___y_3486_;
v___y_3425_ = v___y_3487_;
v_a_3426_ = v___x_3499_;
goto v___jp_3405_;
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
v_a_3502_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3493_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3493_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set_tag(v___x_3504_, 0);
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
v___y_3406_ = v___y_3469_;
v___y_3407_ = v___y_3472_;
v___y_3408_ = v___y_3470_;
v___y_3409_ = v___y_3471_;
v___y_3410_ = v___y_3473_;
v___y_3411_ = v___y_3474_;
v___y_3412_ = v___y_3476_;
v___y_3413_ = v___x_3492_;
v___y_3414_ = v___y_3477_;
v___y_3415_ = v_a_3489_;
v___y_3416_ = v___y_3478_;
v___y_3417_ = v___y_3480_;
v___y_3418_ = v___y_3479_;
v___y_3419_ = v___y_3481_;
v___y_3420_ = v___y_3483_;
v___y_3421_ = v___y_3482_;
v___y_3422_ = v___y_3484_;
v___y_3423_ = v___y_3485_;
v___y_3424_ = v___y_3486_;
v___y_3425_ = v___y_3487_;
v_a_3426_ = v___x_3507_;
goto v___jp_3405_;
}
}
}
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3476_);
lean_inc_ref(v___y_3486_);
lean_inc(v___y_3487_);
lean_inc_ref(v___y_3472_);
lean_inc(v___y_3484_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3474_);
lean_inc(v___y_3469_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3481_);
v___x_3511_ = lean_apply_12(v___y_3475_, v___y_3481_, v___y_3477_, v___y_3469_, v___y_3474_, v___y_3471_, v___y_3478_, v___y_3484_, v___y_3472_, v___y_3487_, v___y_3486_, v___y_3476_, lean_box(0));
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
lean_ctor_set_tag(v___x_3514_, 1);
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
v___y_3439_ = v___y_3469_;
v___y_3440_ = v___y_3472_;
v___y_3441_ = v___y_3470_;
v___y_3442_ = v___y_3471_;
v___y_3443_ = v___y_3473_;
v___y_3444_ = v___y_3474_;
v___y_3445_ = v___y_3476_;
v___y_3446_ = v___y_3477_;
v___y_3447_ = v_a_3489_;
v___y_3448_ = v___y_3478_;
v___y_3449_ = v___y_3480_;
v___y_3450_ = v___y_3479_;
v___y_3451_ = v___y_3481_;
v___y_3452_ = v___y_3483_;
v___y_3453_ = v___y_3482_;
v___y_3454_ = v___y_3484_;
v___y_3455_ = v___x_3510_;
v___y_3456_ = v___y_3485_;
v___y_3457_ = v___y_3486_;
v___y_3458_ = v___y_3487_;
v_a_3459_ = v___x_3517_;
goto v___jp_3438_;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
v_a_3520_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3511_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3511_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set_tag(v___x_3522_, 0);
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
v___y_3439_ = v___y_3469_;
v___y_3440_ = v___y_3472_;
v___y_3441_ = v___y_3470_;
v___y_3442_ = v___y_3471_;
v___y_3443_ = v___y_3473_;
v___y_3444_ = v___y_3474_;
v___y_3445_ = v___y_3476_;
v___y_3446_ = v___y_3477_;
v___y_3447_ = v_a_3489_;
v___y_3448_ = v___y_3478_;
v___y_3449_ = v___y_3480_;
v___y_3450_ = v___y_3479_;
v___y_3451_ = v___y_3481_;
v___y_3452_ = v___y_3483_;
v___y_3453_ = v___y_3482_;
v___y_3454_ = v___y_3484_;
v___y_3455_ = v___x_3510_;
v___y_3456_ = v___y_3485_;
v___y_3457_ = v___y_3486_;
v___y_3458_ = v___y_3487_;
v_a_3459_ = v___x_3525_;
goto v___jp_3438_;
}
}
}
}
}
v___jp_3528_:
{
if (lean_obj_tag(v___y_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3569_; 
v_a_3543_ = lean_ctor_get(v___y_3542_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___y_3542_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3545_ = v___y_3542_;
v_isShared_3546_ = v_isSharedCheck_3569_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___y_3542_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3569_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
uint8_t v___x_3547_; 
v___x_3547_ = lean_unbox(v_a_3543_);
lean_dec(v_a_3543_);
if (v___x_3547_ == 0)
{
uint8_t v_structures_3548_; 
lean_del_object(v___x_3545_);
v_structures_3548_ = lean_ctor_get_uint8(v___y_3536_, sizeof(void*)*2 + 5);
if (v_structures_3548_ == 0)
{
uint8_t v_fixedInt_3549_; uint8_t v_enums_3550_; 
v_fixedInt_3549_ = lean_ctor_get_uint8(v___y_3536_, sizeof(void*)*2 + 6);
v_enums_3550_ = lean_ctor_get_uint8(v___y_3536_, sizeof(void*)*2 + 7);
v___y_3349_ = v___y_3536_;
v_fixedInt_3350_ = v_fixedInt_3549_;
v_enums_3351_ = v_enums_3550_;
v___y_3352_ = v___y_3538_;
v___y_3353_ = v___y_3537_;
v___y_3354_ = v___y_3534_;
v___y_3355_ = v___y_3529_;
v___y_3356_ = v___y_3532_;
v___y_3357_ = v___y_3530_;
v___y_3358_ = v___y_3535_;
v___y_3359_ = v___y_3539_;
v___y_3360_ = v___y_3531_;
v___y_3361_ = v___y_3541_;
v___y_3362_ = v___y_3540_;
v___y_3363_ = v___y_3533_;
goto v___jp_3348_;
}
else
{
lean_object* v___x_3551_; lean_object* v_options_3552_; uint8_t v_hasTrace_3553_; 
v___x_3551_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass;
v_options_3552_ = lean_ctor_get(v___y_3540_, 2);
v_hasTrace_3553_ = lean_ctor_get_uint8(v_options_3552_, sizeof(void*)*1);
if (v_hasTrace_3553_ == 0)
{
lean_object* v_run_x27_3554_; lean_object* v___x_3555_; 
v_run_x27_3554_ = lean_ctor_get(v___x_3551_, 1);
lean_inc_ref(v_run_x27_3554_);
lean_inc(v___y_3533_);
lean_inc_ref(v___y_3540_);
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3531_);
lean_inc(v___y_3539_);
lean_inc_ref(v___y_3535_);
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3532_);
lean_inc(v___y_3529_);
lean_inc(v___y_3534_);
lean_inc_ref(v___y_3537_);
v___x_3555_ = lean_apply_12(v_run_x27_3554_, v___y_3537_, v___y_3534_, v___y_3529_, v___y_3532_, v___y_3530_, v___y_3535_, v___y_3539_, v___y_3531_, v___y_3541_, v___y_3540_, v___y_3533_, lean_box(0));
v___y_3379_ = v___y_3529_;
v___y_3380_ = v___y_3530_;
v___y_3381_ = v___y_3531_;
v___y_3382_ = v___y_3532_;
v___y_3383_ = v___y_3533_;
v___y_3384_ = v___y_3534_;
v___y_3385_ = v___y_3535_;
v___y_3386_ = v___y_3536_;
v___y_3387_ = v___y_3537_;
v___y_3388_ = v___y_3538_;
v___y_3389_ = v___y_3539_;
v___y_3390_ = v___y_3540_;
v___y_3391_ = v___y_3541_;
v___y_3392_ = v___x_3555_;
goto v___jp_3378_;
}
else
{
lean_object* v_run_x27_3556_; lean_object* v_inheritedTraceOptions_3557_; lean_object* v___f_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v_run_x27_3556_ = lean_ctor_get(v___x_3551_, 1);
v_inheritedTraceOptions_3557_ = lean_ctor_get(v___y_3540_, 13);
v___f_3558_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__6);
v___x_3559_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3560_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3561_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3557_, v_options_3552_, v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = l_Lean_trace_profiler;
v___x_3563_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_3552_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
lean_inc_ref(v_run_x27_3556_);
lean_inc(v___y_3533_);
lean_inc_ref(v___y_3540_);
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3531_);
lean_inc(v___y_3539_);
lean_inc_ref(v___y_3535_);
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3532_);
lean_inc(v___y_3529_);
lean_inc(v___y_3534_);
lean_inc_ref(v___y_3537_);
v___x_3564_ = lean_apply_12(v_run_x27_3556_, v___y_3537_, v___y_3534_, v___y_3529_, v___y_3532_, v___y_3530_, v___y_3535_, v___y_3539_, v___y_3531_, v___y_3541_, v___y_3540_, v___y_3533_, lean_box(0));
v___y_3379_ = v___y_3529_;
v___y_3380_ = v___y_3530_;
v___y_3381_ = v___y_3531_;
v___y_3382_ = v___y_3532_;
v___y_3383_ = v___y_3533_;
v___y_3384_ = v___y_3534_;
v___y_3385_ = v___y_3535_;
v___y_3386_ = v___y_3536_;
v___y_3387_ = v___y_3537_;
v___y_3388_ = v___y_3538_;
v___y_3389_ = v___y_3539_;
v___y_3390_ = v___y_3540_;
v___y_3391_ = v___y_3541_;
v___y_3392_ = v___x_3564_;
goto v___jp_3378_;
}
else
{
lean_inc_ref(v_run_x27_3556_);
v___y_3469_ = v___y_3529_;
v___y_3470_ = v___x_3559_;
v___y_3471_ = v___y_3530_;
v___y_3472_ = v___y_3531_;
v___y_3473_ = v_options_3552_;
v___y_3474_ = v___y_3532_;
v___y_3475_ = v_run_x27_3556_;
v___y_3476_ = v___y_3533_;
v___y_3477_ = v___y_3534_;
v___y_3478_ = v___y_3535_;
v___y_3479_ = v___x_3561_;
v___y_3480_ = v___y_3536_;
v___y_3481_ = v___y_3537_;
v___y_3482_ = v___f_3558_;
v___y_3483_ = v___y_3538_;
v___y_3484_ = v___y_3539_;
v___y_3485_ = v_hasTrace_3553_;
v___y_3486_ = v___y_3540_;
v___y_3487_ = v___y_3541_;
goto v___jp_3468_;
}
}
else
{
lean_inc_ref(v_run_x27_3556_);
v___y_3469_ = v___y_3529_;
v___y_3470_ = v___x_3559_;
v___y_3471_ = v___y_3530_;
v___y_3472_ = v___y_3531_;
v___y_3473_ = v_options_3552_;
v___y_3474_ = v___y_3532_;
v___y_3475_ = v_run_x27_3556_;
v___y_3476_ = v___y_3533_;
v___y_3477_ = v___y_3534_;
v___y_3478_ = v___y_3535_;
v___y_3479_ = v___x_3561_;
v___y_3480_ = v___y_3536_;
v___y_3481_ = v___y_3537_;
v___y_3482_ = v___f_3558_;
v___y_3483_ = v___y_3538_;
v___y_3484_ = v___y_3539_;
v___y_3485_ = v_hasTrace_3553_;
v___y_3486_ = v___y_3540_;
v___y_3487_ = v___y_3541_;
goto v___jp_3468_;
}
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3565_ = lean_box(v___y_3538_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3565_);
v___x_3567_ = v___x_3545_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
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
else
{
return v___y_3542_;
}
}
v___jp_3570_:
{
lean_object* v___x_3592_; double v___x_3593_; double v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3592_ = lean_io_get_num_heartbeats();
v___x_3593_ = lean_float_of_nat(v___y_3576_);
v___x_3594_ = lean_float_of_nat(v___x_3592_);
v___x_3595_ = lean_box_float(v___x_3593_);
v___x_3596_ = lean_box_float(v___x_3594_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v_a_3591_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
lean_inc_ref(v___y_3571_);
lean_inc_ref(v___y_3573_);
v___x_3599_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3578_, v___y_3573_, v___y_3580_, v___y_3587_, v___y_3588_, v___y_3571_, v___x_3598_, v___y_3584_, v___y_3581_, v___y_3572_, v___y_3577_, v___y_3575_, v___y_3582_, v___y_3586_, v___y_3574_, v___y_3590_, v___y_3589_, v___y_3579_);
v___y_3529_ = v___y_3572_;
v___y_3530_ = v___y_3575_;
v___y_3531_ = v___y_3574_;
v___y_3532_ = v___y_3577_;
v___y_3533_ = v___y_3579_;
v___y_3534_ = v___y_3581_;
v___y_3535_ = v___y_3582_;
v___y_3536_ = v___y_3583_;
v___y_3537_ = v___y_3584_;
v___y_3538_ = v___y_3585_;
v___y_3539_ = v___y_3586_;
v___y_3540_ = v___y_3589_;
v___y_3541_ = v___y_3590_;
v___y_3542_ = v___x_3599_;
goto v___jp_3528_;
}
v___jp_3600_:
{
lean_object* v___x_3622_; double v___x_3623_; double v___x_3624_; double v___x_3625_; double v___x_3626_; double v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3622_ = lean_io_mono_nanos_now();
v___x_3623_ = lean_float_of_nat(v___y_3613_);
v___x_3624_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3625_ = lean_float_div(v___x_3623_, v___x_3624_);
v___x_3626_ = lean_float_of_nat(v___x_3622_);
v___x_3627_ = lean_float_div(v___x_3626_, v___x_3624_);
v___x_3628_ = lean_box_float(v___x_3625_);
v___x_3629_ = lean_box_float(v___x_3627_);
v___x_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3628_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_a_3621_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
lean_inc_ref(v___y_3601_);
lean_inc_ref(v___y_3603_);
v___x_3632_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3607_, v___y_3603_, v___y_3609_, v___y_3617_, v___y_3618_, v___y_3601_, v___x_3631_, v___y_3614_, v___y_3610_, v___y_3602_, v___y_3606_, v___y_3605_, v___y_3611_, v___y_3616_, v___y_3604_, v___y_3620_, v___y_3619_, v___y_3608_);
v___y_3529_ = v___y_3602_;
v___y_3530_ = v___y_3605_;
v___y_3531_ = v___y_3604_;
v___y_3532_ = v___y_3606_;
v___y_3533_ = v___y_3608_;
v___y_3534_ = v___y_3610_;
v___y_3535_ = v___y_3611_;
v___y_3536_ = v___y_3612_;
v___y_3537_ = v___y_3614_;
v___y_3538_ = v___y_3615_;
v___y_3539_ = v___y_3616_;
v___y_3540_ = v___y_3619_;
v___y_3541_ = v___y_3620_;
v___y_3542_ = v___x_3632_;
goto v___jp_3528_;
}
v___jp_3633_:
{
lean_object* v___x_3653_; lean_object* v_a_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3653_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_3642_);
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref(v___x_3653_);
v___x_3655_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3656_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3643_, v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = lean_io_mono_nanos_now();
lean_inc(v___y_3642_);
lean_inc_ref(v___y_3651_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3638_);
lean_inc(v___y_3650_);
lean_inc_ref(v___y_3645_);
lean_inc(v___y_3637_);
lean_inc_ref(v___y_3639_);
lean_inc(v___y_3635_);
lean_inc(v___y_3644_);
lean_inc_ref(v___y_3647_);
v___x_3658_ = lean_apply_12(v___y_3641_, v___y_3647_, v___y_3644_, v___y_3635_, v___y_3639_, v___y_3637_, v___y_3645_, v___y_3650_, v___y_3638_, v___y_3652_, v___y_3651_, v___y_3642_, lean_box(0));
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 1);
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
v___y_3601_ = v___y_3634_;
v___y_3602_ = v___y_3635_;
v___y_3603_ = v___y_3636_;
v___y_3604_ = v___y_3638_;
v___y_3605_ = v___y_3637_;
v___y_3606_ = v___y_3639_;
v___y_3607_ = v___y_3640_;
v___y_3608_ = v___y_3642_;
v___y_3609_ = v___y_3643_;
v___y_3610_ = v___y_3644_;
v___y_3611_ = v___y_3645_;
v___y_3612_ = v___y_3646_;
v___y_3613_ = v___x_3657_;
v___y_3614_ = v___y_3647_;
v___y_3615_ = v___y_3648_;
v___y_3616_ = v___y_3650_;
v___y_3617_ = v___y_3649_;
v___y_3618_ = v_a_3654_;
v___y_3619_ = v___y_3651_;
v___y_3620_ = v___y_3652_;
v_a_3621_ = v___x_3664_;
goto v___jp_3600_;
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
v_a_3667_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3658_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3658_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set_tag(v___x_3669_, 0);
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
v___y_3601_ = v___y_3634_;
v___y_3602_ = v___y_3635_;
v___y_3603_ = v___y_3636_;
v___y_3604_ = v___y_3638_;
v___y_3605_ = v___y_3637_;
v___y_3606_ = v___y_3639_;
v___y_3607_ = v___y_3640_;
v___y_3608_ = v___y_3642_;
v___y_3609_ = v___y_3643_;
v___y_3610_ = v___y_3644_;
v___y_3611_ = v___y_3645_;
v___y_3612_ = v___y_3646_;
v___y_3613_ = v___x_3657_;
v___y_3614_ = v___y_3647_;
v___y_3615_ = v___y_3648_;
v___y_3616_ = v___y_3650_;
v___y_3617_ = v___y_3649_;
v___y_3618_ = v_a_3654_;
v___y_3619_ = v___y_3651_;
v___y_3620_ = v___y_3652_;
v_a_3621_ = v___x_3672_;
goto v___jp_3600_;
}
}
}
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3642_);
lean_inc_ref(v___y_3651_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3638_);
lean_inc(v___y_3650_);
lean_inc_ref(v___y_3645_);
lean_inc(v___y_3637_);
lean_inc_ref(v___y_3639_);
lean_inc(v___y_3635_);
lean_inc(v___y_3644_);
lean_inc_ref(v___y_3647_);
v___x_3676_ = lean_apply_12(v___y_3641_, v___y_3647_, v___y_3644_, v___y_3635_, v___y_3639_, v___y_3637_, v___y_3645_, v___y_3650_, v___y_3638_, v___y_3652_, v___y_3651_, v___y_3642_, lean_box(0));
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set_tag(v___x_3679_, 1);
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
v___y_3571_ = v___y_3634_;
v___y_3572_ = v___y_3635_;
v___y_3573_ = v___y_3636_;
v___y_3574_ = v___y_3638_;
v___y_3575_ = v___y_3637_;
v___y_3576_ = v___x_3675_;
v___y_3577_ = v___y_3639_;
v___y_3578_ = v___y_3640_;
v___y_3579_ = v___y_3642_;
v___y_3580_ = v___y_3643_;
v___y_3581_ = v___y_3644_;
v___y_3582_ = v___y_3645_;
v___y_3583_ = v___y_3646_;
v___y_3584_ = v___y_3647_;
v___y_3585_ = v___y_3648_;
v___y_3586_ = v___y_3650_;
v___y_3587_ = v___y_3649_;
v___y_3588_ = v_a_3654_;
v___y_3589_ = v___y_3651_;
v___y_3590_ = v___y_3652_;
v_a_3591_ = v___x_3682_;
goto v___jp_3570_;
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
v_a_3685_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3676_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3676_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 0);
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
v___y_3571_ = v___y_3634_;
v___y_3572_ = v___y_3635_;
v___y_3573_ = v___y_3636_;
v___y_3574_ = v___y_3638_;
v___y_3575_ = v___y_3637_;
v___y_3576_ = v___x_3675_;
v___y_3577_ = v___y_3639_;
v___y_3578_ = v___y_3640_;
v___y_3579_ = v___y_3642_;
v___y_3580_ = v___y_3643_;
v___y_3581_ = v___y_3644_;
v___y_3582_ = v___y_3645_;
v___y_3583_ = v___y_3646_;
v___y_3584_ = v___y_3647_;
v___y_3585_ = v___y_3648_;
v___y_3586_ = v___y_3650_;
v___y_3587_ = v___y_3649_;
v___y_3588_ = v_a_3654_;
v___y_3589_ = v___y_3651_;
v___y_3590_ = v___y_3652_;
v_a_3591_ = v___x_3690_;
goto v___jp_3570_;
}
}
}
}
}
v___jp_3693_:
{
lean_object* v___x_3707_; lean_object* v_options_3708_; uint8_t v_hasTrace_3709_; 
v___x_3707_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass;
v_options_3708_ = lean_ctor_get(v___y_3705_, 2);
v_hasTrace_3709_ = lean_ctor_get_uint8(v_options_3708_, sizeof(void*)*1);
if (v_hasTrace_3709_ == 0)
{
lean_object* v_run_x27_3710_; lean_object* v___x_3711_; 
v_run_x27_3710_ = lean_ctor_get(v___x_3707_, 1);
lean_inc_ref(v_run_x27_3710_);
lean_inc(v___y_3706_);
lean_inc_ref(v___y_3705_);
lean_inc(v___y_3704_);
lean_inc_ref(v___y_3703_);
lean_inc(v___y_3702_);
lean_inc_ref(v___y_3701_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
lean_inc(v___y_3698_);
lean_inc(v___y_3697_);
lean_inc_ref(v___y_3696_);
v___x_3711_ = lean_apply_12(v_run_x27_3710_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, lean_box(0));
v___y_3529_ = v___y_3698_;
v___y_3530_ = v___y_3700_;
v___y_3531_ = v___y_3703_;
v___y_3532_ = v___y_3699_;
v___y_3533_ = v___y_3706_;
v___y_3534_ = v___y_3697_;
v___y_3535_ = v___y_3701_;
v___y_3536_ = v___y_3694_;
v___y_3537_ = v___y_3696_;
v___y_3538_ = v___y_3695_;
v___y_3539_ = v___y_3702_;
v___y_3540_ = v___y_3705_;
v___y_3541_ = v___y_3704_;
v___y_3542_ = v___x_3711_;
goto v___jp_3528_;
}
else
{
lean_object* v_run_x27_3712_; lean_object* v_inheritedTraceOptions_3713_; lean_object* v___f_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v_run_x27_3712_ = lean_ctor_get(v___x_3707_, 1);
v_inheritedTraceOptions_3713_ = lean_ctor_get(v___y_3705_, 13);
v___f_3714_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__7);
v___x_3715_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3716_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3713_, v_options_3708_, v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3718_ = l_Lean_trace_profiler;
v___x_3719_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_3708_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
lean_inc_ref(v_run_x27_3712_);
lean_inc(v___y_3706_);
lean_inc_ref(v___y_3705_);
lean_inc(v___y_3704_);
lean_inc_ref(v___y_3703_);
lean_inc(v___y_3702_);
lean_inc_ref(v___y_3701_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
lean_inc(v___y_3698_);
lean_inc(v___y_3697_);
lean_inc_ref(v___y_3696_);
v___x_3720_ = lean_apply_12(v_run_x27_3712_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, lean_box(0));
v___y_3529_ = v___y_3698_;
v___y_3530_ = v___y_3700_;
v___y_3531_ = v___y_3703_;
v___y_3532_ = v___y_3699_;
v___y_3533_ = v___y_3706_;
v___y_3534_ = v___y_3697_;
v___y_3535_ = v___y_3701_;
v___y_3536_ = v___y_3694_;
v___y_3537_ = v___y_3696_;
v___y_3538_ = v___y_3695_;
v___y_3539_ = v___y_3702_;
v___y_3540_ = v___y_3705_;
v___y_3541_ = v___y_3704_;
v___y_3542_ = v___x_3720_;
goto v___jp_3528_;
}
else
{
lean_inc_ref(v_run_x27_3712_);
v___y_3634_ = v___f_3714_;
v___y_3635_ = v___y_3698_;
v___y_3636_ = v___x_3715_;
v___y_3637_ = v___y_3700_;
v___y_3638_ = v___y_3703_;
v___y_3639_ = v___y_3699_;
v___y_3640_ = v_hasTrace_3709_;
v___y_3641_ = v_run_x27_3712_;
v___y_3642_ = v___y_3706_;
v___y_3643_ = v_options_3708_;
v___y_3644_ = v___y_3697_;
v___y_3645_ = v___y_3701_;
v___y_3646_ = v___y_3694_;
v___y_3647_ = v___y_3696_;
v___y_3648_ = v___y_3695_;
v___y_3649_ = v___x_3717_;
v___y_3650_ = v___y_3702_;
v___y_3651_ = v___y_3705_;
v___y_3652_ = v___y_3704_;
goto v___jp_3633_;
}
}
else
{
lean_inc_ref(v_run_x27_3712_);
v___y_3634_ = v___f_3714_;
v___y_3635_ = v___y_3698_;
v___y_3636_ = v___x_3715_;
v___y_3637_ = v___y_3700_;
v___y_3638_ = v___y_3703_;
v___y_3639_ = v___y_3699_;
v___y_3640_ = v_hasTrace_3709_;
v___y_3641_ = v_run_x27_3712_;
v___y_3642_ = v___y_3706_;
v___y_3643_ = v_options_3708_;
v___y_3644_ = v___y_3697_;
v___y_3645_ = v___y_3701_;
v___y_3646_ = v___y_3694_;
v___y_3647_ = v___y_3696_;
v___y_3648_ = v___y_3695_;
v___y_3649_ = v___x_3717_;
v___y_3650_ = v___y_3702_;
v___y_3651_ = v___y_3705_;
v___y_3652_ = v___y_3704_;
goto v___jp_3633_;
}
}
}
v___jp_3721_:
{
if (lean_obj_tag(v___y_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3745_; 
v_a_3736_ = lean_ctor_get(v___y_3735_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___y_3735_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3738_ = v___y_3735_;
v_isShared_3739_ = v_isSharedCheck_3745_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___y_3735_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3745_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
uint8_t v___x_3740_; 
v___x_3740_ = lean_unbox(v_a_3736_);
lean_dec(v_a_3736_);
if (v___x_3740_ == 0)
{
lean_del_object(v___x_3738_);
v___y_3694_ = v___y_3730_;
v___y_3695_ = v___y_3731_;
v___y_3696_ = v___y_3722_;
v___y_3697_ = v___y_3726_;
v___y_3698_ = v___y_3732_;
v___y_3699_ = v___y_3723_;
v___y_3700_ = v___y_3725_;
v___y_3701_ = v___y_3724_;
v___y_3702_ = v___y_3733_;
v___y_3703_ = v___y_3734_;
v___y_3704_ = v___y_3728_;
v___y_3705_ = v___y_3729_;
v___y_3706_ = v___y_3727_;
goto v___jp_3693_;
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3743_; 
v___x_3741_ = lean_box(v___y_3731_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 0, v___x_3741_);
v___x_3743_ = v___x_3738_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
return v___y_3735_;
}
}
v___jp_3746_:
{
lean_object* v___x_3768_; double v___x_3769_; double v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3768_ = lean_io_get_num_heartbeats();
v___x_3769_ = lean_float_of_nat(v___y_3755_);
v___x_3770_ = lean_float_of_nat(v___x_3768_);
v___x_3771_ = lean_box_float(v___x_3769_);
v___x_3772_ = lean_box_float(v___x_3770_);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_a_3767_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
lean_inc_ref(v___y_3757_);
lean_inc_ref(v___y_3752_);
v___x_3775_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3751_, v___y_3752_, v___y_3760_, v___y_3763_, v___y_3756_, v___y_3757_, v___x_3774_, v___y_3747_, v___y_3754_, v___y_3765_, v___y_3748_, v___y_3750_, v___y_3749_, v___y_3764_, v___y_3766_, v___y_3758_, v___y_3759_, v___y_3753_);
v___y_3722_ = v___y_3747_;
v___y_3723_ = v___y_3748_;
v___y_3724_ = v___y_3749_;
v___y_3725_ = v___y_3750_;
v___y_3726_ = v___y_3754_;
v___y_3727_ = v___y_3753_;
v___y_3728_ = v___y_3758_;
v___y_3729_ = v___y_3759_;
v___y_3730_ = v___y_3761_;
v___y_3731_ = v___y_3762_;
v___y_3732_ = v___y_3765_;
v___y_3733_ = v___y_3764_;
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___x_3775_;
goto v___jp_3721_;
}
v___jp_3776_:
{
lean_object* v___x_3798_; double v___x_3799_; double v___x_3800_; double v___x_3801_; double v___x_3802_; double v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3798_ = lean_io_mono_nanos_now();
v___x_3799_ = lean_float_of_nat(v___y_3796_);
v___x_3800_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__0);
v___x_3801_ = lean_float_div(v___x_3799_, v___x_3800_);
v___x_3802_ = lean_float_of_nat(v___x_3798_);
v___x_3803_ = lean_float_div(v___x_3802_, v___x_3800_);
v___x_3804_ = lean_box_float(v___x_3801_);
v___x_3805_ = lean_box_float(v___x_3803_);
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_a_3797_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
lean_inc_ref(v___y_3786_);
lean_inc_ref(v___y_3782_);
v___x_3808_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2(v_cls_2851_, v___y_3781_, v___y_3782_, v___y_3789_, v___y_3792_, v___y_3785_, v___y_3786_, v___x_3807_, v___y_3777_, v___y_3784_, v___y_3794_, v___y_3778_, v___y_3780_, v___y_3779_, v___y_3793_, v___y_3795_, v___y_3787_, v___y_3788_, v___y_3783_);
v___y_3722_ = v___y_3777_;
v___y_3723_ = v___y_3778_;
v___y_3724_ = v___y_3779_;
v___y_3725_ = v___y_3780_;
v___y_3726_ = v___y_3784_;
v___y_3727_ = v___y_3783_;
v___y_3728_ = v___y_3787_;
v___y_3729_ = v___y_3788_;
v___y_3730_ = v___y_3790_;
v___y_3731_ = v___y_3791_;
v___y_3732_ = v___y_3794_;
v___y_3733_ = v___y_3793_;
v___y_3734_ = v___y_3795_;
v___y_3735_ = v___x_3808_;
goto v___jp_3721_;
}
v___jp_3809_:
{
lean_object* v___x_3829_; lean_object* v_a_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v___x_3829_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__0___redArg(v___y_3817_);
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3832_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v___y_3821_, v___x_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = lean_io_mono_nanos_now();
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3820_);
lean_inc(v___y_3819_);
lean_inc_ref(v___y_3828_);
lean_inc(v___y_3827_);
lean_inc_ref(v___y_3812_);
lean_inc(v___y_3813_);
lean_inc_ref(v___y_3811_);
lean_inc(v___y_3826_);
lean_inc(v___y_3816_);
lean_inc_ref(v___y_3810_);
v___x_3834_ = lean_apply_12(v___y_3823_, v___y_3810_, v___y_3816_, v___y_3826_, v___y_3811_, v___y_3813_, v___y_3812_, v___y_3827_, v___y_3828_, v___y_3819_, v___y_3820_, v___y_3817_, lean_box(0));
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set_tag(v___x_3837_, 1);
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
v___y_3777_ = v___y_3810_;
v___y_3778_ = v___y_3811_;
v___y_3779_ = v___y_3812_;
v___y_3780_ = v___y_3813_;
v___y_3781_ = v___y_3815_;
v___y_3782_ = v___y_3814_;
v___y_3783_ = v___y_3817_;
v___y_3784_ = v___y_3816_;
v___y_3785_ = v_a_3830_;
v___y_3786_ = v___y_3818_;
v___y_3787_ = v___y_3819_;
v___y_3788_ = v___y_3820_;
v___y_3789_ = v___y_3821_;
v___y_3790_ = v___y_3822_;
v___y_3791_ = v___y_3824_;
v___y_3792_ = v___y_3825_;
v___y_3793_ = v___y_3827_;
v___y_3794_ = v___y_3826_;
v___y_3795_ = v___y_3828_;
v___y_3796_ = v___x_3833_;
v_a_3797_ = v___x_3840_;
goto v___jp_3776_;
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
v_a_3843_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3834_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3834_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set_tag(v___x_3845_, 0);
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
v___y_3777_ = v___y_3810_;
v___y_3778_ = v___y_3811_;
v___y_3779_ = v___y_3812_;
v___y_3780_ = v___y_3813_;
v___y_3781_ = v___y_3815_;
v___y_3782_ = v___y_3814_;
v___y_3783_ = v___y_3817_;
v___y_3784_ = v___y_3816_;
v___y_3785_ = v_a_3830_;
v___y_3786_ = v___y_3818_;
v___y_3787_ = v___y_3819_;
v___y_3788_ = v___y_3820_;
v___y_3789_ = v___y_3821_;
v___y_3790_ = v___y_3822_;
v___y_3791_ = v___y_3824_;
v___y_3792_ = v___y_3825_;
v___y_3793_ = v___y_3827_;
v___y_3794_ = v___y_3826_;
v___y_3795_ = v___y_3828_;
v___y_3796_ = v___x_3833_;
v_a_3797_ = v___x_3848_;
goto v___jp_3776_;
}
}
}
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3820_);
lean_inc(v___y_3819_);
lean_inc_ref(v___y_3828_);
lean_inc(v___y_3827_);
lean_inc_ref(v___y_3812_);
lean_inc(v___y_3813_);
lean_inc_ref(v___y_3811_);
lean_inc(v___y_3826_);
lean_inc(v___y_3816_);
lean_inc_ref(v___y_3810_);
v___x_3852_ = lean_apply_12(v___y_3823_, v___y_3810_, v___y_3816_, v___y_3826_, v___y_3811_, v___y_3813_, v___y_3812_, v___y_3827_, v___y_3828_, v___y_3819_, v___y_3820_, v___y_3817_, lean_box(0));
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set_tag(v___x_3855_, 1);
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
v___y_3747_ = v___y_3810_;
v___y_3748_ = v___y_3811_;
v___y_3749_ = v___y_3812_;
v___y_3750_ = v___y_3813_;
v___y_3751_ = v___y_3815_;
v___y_3752_ = v___y_3814_;
v___y_3753_ = v___y_3817_;
v___y_3754_ = v___y_3816_;
v___y_3755_ = v___x_3851_;
v___y_3756_ = v_a_3830_;
v___y_3757_ = v___y_3818_;
v___y_3758_ = v___y_3819_;
v___y_3759_ = v___y_3820_;
v___y_3760_ = v___y_3821_;
v___y_3761_ = v___y_3822_;
v___y_3762_ = v___y_3824_;
v___y_3763_ = v___y_3825_;
v___y_3764_ = v___y_3827_;
v___y_3765_ = v___y_3826_;
v___y_3766_ = v___y_3828_;
v_a_3767_ = v___x_3858_;
goto v___jp_3746_;
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
v_a_3861_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3852_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3852_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set_tag(v___x_3863_, 0);
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
v___y_3747_ = v___y_3810_;
v___y_3748_ = v___y_3811_;
v___y_3749_ = v___y_3812_;
v___y_3750_ = v___y_3813_;
v___y_3751_ = v___y_3815_;
v___y_3752_ = v___y_3814_;
v___y_3753_ = v___y_3817_;
v___y_3754_ = v___y_3816_;
v___y_3755_ = v___x_3851_;
v___y_3756_ = v_a_3830_;
v___y_3757_ = v___y_3818_;
v___y_3758_ = v___y_3819_;
v___y_3759_ = v___y_3820_;
v___y_3760_ = v___y_3821_;
v___y_3761_ = v___y_3822_;
v___y_3762_ = v___y_3824_;
v___y_3763_ = v___y_3825_;
v___y_3764_ = v___y_3827_;
v___y_3765_ = v___y_3826_;
v___y_3766_ = v___y_3828_;
v_a_3767_ = v___x_3866_;
goto v___jp_3746_;
}
}
}
}
}
v___jp_3869_:
{
lean_object* v___x_3883_; lean_object* v_options_3884_; uint8_t v_hasTrace_3885_; 
v___x_3883_ = l_Lean_Meta_Tactic_BVDecide_Normalize_typeAnalysisPass;
v_options_3884_ = lean_ctor_get(v___y_3877_, 2);
v_hasTrace_3885_ = lean_ctor_get_uint8(v_options_3884_, sizeof(void*)*1);
if (v_hasTrace_3885_ == 0)
{
lean_object* v_run_x27_3886_; lean_object* v___x_3887_; 
v_run_x27_3886_ = lean_ctor_get(v___x_3883_, 1);
lean_inc_ref(v_run_x27_3886_);
lean_inc(v___y_3875_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3876_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3872_);
lean_inc(v___y_3873_);
lean_inc_ref(v___y_3871_);
lean_inc(v___y_3880_);
lean_inc(v___y_3874_);
lean_inc_ref(v___y_3870_);
v___x_3887_ = lean_apply_12(v_run_x27_3886_, v___y_3870_, v___y_3874_, v___y_3880_, v___y_3871_, v___y_3873_, v___y_3872_, v___y_3881_, v___y_3882_, v___y_3876_, v___y_3877_, v___y_3875_, lean_box(0));
v___y_3722_ = v___y_3870_;
v___y_3723_ = v___y_3871_;
v___y_3724_ = v___y_3872_;
v___y_3725_ = v___y_3873_;
v___y_3726_ = v___y_3874_;
v___y_3727_ = v___y_3875_;
v___y_3728_ = v___y_3876_;
v___y_3729_ = v___y_3877_;
v___y_3730_ = v___y_3878_;
v___y_3731_ = v___y_3879_;
v___y_3732_ = v___y_3880_;
v___y_3733_ = v___y_3881_;
v___y_3734_ = v___y_3882_;
v___y_3735_ = v___x_3887_;
goto v___jp_3721_;
}
else
{
lean_object* v_run_x27_3888_; lean_object* v_inheritedTraceOptions_3889_; lean_object* v___f_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v_run_x27_3888_ = lean_ctor_get(v___x_3883_, 1);
v_inheritedTraceOptions_3889_ = lean_ctor_get(v___y_3877_, 13);
v___f_3890_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___lam__8___closed__8);
v___x_3891_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg___closed__0));
v___x_3892_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3893_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3889_, v_options_3884_, v___x_3892_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3894_ = l_Lean_trace_profiler;
v___x_3895_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__1(v_options_3884_, v___x_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; 
lean_inc_ref(v_run_x27_3888_);
lean_inc(v___y_3875_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3876_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3872_);
lean_inc(v___y_3873_);
lean_inc_ref(v___y_3871_);
lean_inc(v___y_3880_);
lean_inc(v___y_3874_);
lean_inc_ref(v___y_3870_);
v___x_3896_ = lean_apply_12(v_run_x27_3888_, v___y_3870_, v___y_3874_, v___y_3880_, v___y_3871_, v___y_3873_, v___y_3872_, v___y_3881_, v___y_3882_, v___y_3876_, v___y_3877_, v___y_3875_, lean_box(0));
v___y_3722_ = v___y_3870_;
v___y_3723_ = v___y_3871_;
v___y_3724_ = v___y_3872_;
v___y_3725_ = v___y_3873_;
v___y_3726_ = v___y_3874_;
v___y_3727_ = v___y_3875_;
v___y_3728_ = v___y_3876_;
v___y_3729_ = v___y_3877_;
v___y_3730_ = v___y_3878_;
v___y_3731_ = v___y_3879_;
v___y_3732_ = v___y_3880_;
v___y_3733_ = v___y_3881_;
v___y_3734_ = v___y_3882_;
v___y_3735_ = v___x_3896_;
goto v___jp_3721_;
}
else
{
lean_inc_ref(v_run_x27_3888_);
v___y_3810_ = v___y_3870_;
v___y_3811_ = v___y_3871_;
v___y_3812_ = v___y_3872_;
v___y_3813_ = v___y_3873_;
v___y_3814_ = v___x_3891_;
v___y_3815_ = v_hasTrace_3885_;
v___y_3816_ = v___y_3874_;
v___y_3817_ = v___y_3875_;
v___y_3818_ = v___f_3890_;
v___y_3819_ = v___y_3876_;
v___y_3820_ = v___y_3877_;
v___y_3821_ = v_options_3884_;
v___y_3822_ = v___y_3878_;
v___y_3823_ = v_run_x27_3888_;
v___y_3824_ = v___y_3879_;
v___y_3825_ = v___x_3893_;
v___y_3826_ = v___y_3880_;
v___y_3827_ = v___y_3881_;
v___y_3828_ = v___y_3882_;
goto v___jp_3809_;
}
}
else
{
lean_inc_ref(v_run_x27_3888_);
v___y_3810_ = v___y_3870_;
v___y_3811_ = v___y_3871_;
v___y_3812_ = v___y_3872_;
v___y_3813_ = v___y_3873_;
v___y_3814_ = v___x_3891_;
v___y_3815_ = v_hasTrace_3885_;
v___y_3816_ = v___y_3874_;
v___y_3817_ = v___y_3875_;
v___y_3818_ = v___f_3890_;
v___y_3819_ = v___y_3876_;
v___y_3820_ = v___y_3877_;
v___y_3821_ = v_options_3884_;
v___y_3822_ = v___y_3878_;
v___y_3823_ = v_run_x27_3888_;
v___y_3824_ = v___y_3879_;
v___y_3825_ = v___x_3893_;
v___y_3826_ = v___y_3880_;
v___y_3827_ = v___y_3881_;
v___y_3828_ = v___y_3882_;
goto v___jp_3809_;
}
}
}
v___jp_3897_:
{
lean_object* v_config_3910_; uint8_t v_structures_3911_; 
v_config_3910_ = lean_ctor_get(v___y_3899_, 0);
v_structures_3911_ = lean_ctor_get_uint8(v_config_3910_, sizeof(void*)*2 + 5);
if (v_structures_3911_ == 0)
{
uint8_t v_enums_3912_; 
v_enums_3912_ = lean_ctor_get_uint8(v_config_3910_, sizeof(void*)*2 + 7);
if (v_enums_3912_ == 0)
{
v___y_3694_ = v_config_3910_;
v___y_3695_ = v___y_3898_;
v___y_3696_ = v___y_3899_;
v___y_3697_ = v___y_3900_;
v___y_3698_ = v___y_3901_;
v___y_3699_ = v___y_3902_;
v___y_3700_ = v___y_3903_;
v___y_3701_ = v___y_3904_;
v___y_3702_ = v___y_3905_;
v___y_3703_ = v___y_3906_;
v___y_3704_ = v___y_3907_;
v___y_3705_ = v___y_3908_;
v___y_3706_ = v___y_3909_;
goto v___jp_3693_;
}
else
{
v___y_3870_ = v___y_3899_;
v___y_3871_ = v___y_3902_;
v___y_3872_ = v___y_3904_;
v___y_3873_ = v___y_3903_;
v___y_3874_ = v___y_3900_;
v___y_3875_ = v___y_3909_;
v___y_3876_ = v___y_3907_;
v___y_3877_ = v___y_3908_;
v___y_3878_ = v_config_3910_;
v___y_3879_ = v___y_3898_;
v___y_3880_ = v___y_3901_;
v___y_3881_ = v___y_3905_;
v___y_3882_ = v___y_3906_;
goto v___jp_3869_;
}
}
else
{
v___y_3870_ = v___y_3899_;
v___y_3871_ = v___y_3902_;
v___y_3872_ = v___y_3904_;
v___y_3873_ = v___y_3903_;
v___y_3874_ = v___y_3900_;
v___y_3875_ = v___y_3909_;
v___y_3876_ = v___y_3907_;
v___y_3877_ = v___y_3908_;
v___y_3878_ = v_config_3910_;
v___y_3879_ = v___y_3898_;
v___y_3880_ = v___y_3901_;
v___y_3881_ = v___y_3905_;
v___y_3882_ = v___y_3906_;
goto v___jp_3869_;
}
}
v___jp_3913_:
{
uint8_t v___x_3926_; 
v___x_3926_ = 1;
if (v_____do__lift_3914_ == 0)
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectTargetHyps(v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_options_3928_; uint8_t v_hasTrace_3929_; 
lean_dec_ref_known(v___x_3927_, 1);
v_options_3928_ = lean_ctor_get(v___y_3924_, 2);
v_hasTrace_3929_ = lean_ctor_get_uint8(v_options_3928_, sizeof(void*)*1);
if (v_hasTrace_3929_ == 0)
{
v___y_3898_ = v___x_3926_;
v___y_3899_ = v___y_3915_;
v___y_3900_ = v___y_3916_;
v___y_3901_ = v___y_3917_;
v___y_3902_ = v___y_3918_;
v___y_3903_ = v___y_3919_;
v___y_3904_ = v___y_3920_;
v___y_3905_ = v___y_3921_;
v___y_3906_ = v___y_3922_;
v___y_3907_ = v___y_3923_;
v___y_3908_ = v___y_3924_;
v___y_3909_ = v___y_3925_;
goto v___jp_3897_;
}
else
{
lean_object* v_inheritedTraceOptions_3930_; lean_object* v___x_3931_; uint8_t v___x_3932_; 
v_inheritedTraceOptions_3930_ = lean_ctor_get(v___y_3924_, 13);
v___x_3931_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__4);
v___x_3932_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3930_, v_options_3928_, v___x_3931_);
if (v___x_3932_ == 0)
{
v___y_3898_ = v___x_3926_;
v___y_3899_ = v___y_3915_;
v___y_3900_ = v___y_3916_;
v___y_3901_ = v___y_3917_;
v___y_3902_ = v___y_3918_;
v___y_3903_ = v___y_3919_;
v___y_3904_ = v___y_3920_;
v___y_3905_ = v___y_3921_;
v___y_3906_ = v___y_3922_;
v___y_3907_ = v___y_3923_;
v___y_3908_ = v___y_3924_;
v___y_3909_ = v___y_3925_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___closed__6);
v___x_3934_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_2851_, v___x_3933_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_dec_ref_known(v___x_3934_, 1);
v___y_3898_ = v___x_3926_;
v___y_3899_ = v___y_3915_;
v___y_3900_ = v___y_3916_;
v___y_3901_ = v___y_3917_;
v___y_3902_ = v___y_3918_;
v___y_3903_ = v___y_3919_;
v___y_3904_ = v___y_3920_;
v___y_3905_ = v___y_3921_;
v___y_3906_ = v___y_3922_;
v___y_3907_ = v___y_3923_;
v___y_3908_ = v___y_3924_;
v___y_3909_ = v___y_3925_;
goto v___jp_3897_;
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
v_a_3943_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3927_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3927_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_box(v___x_3926_);
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
return v___x_3952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize___boxed(lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec(v_a_4065_);
lean_dec_ref(v_a_4064_);
lean_dec(v_a_4063_);
lean_dec_ref(v_a_4062_);
lean_dec(v_a_4061_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(lean_object* v_00_u03b1_4072_, lean_object* v_x_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___redArg(v_x_4073_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4087_, lean_object* v_x_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__3(v_00_u03b1_4087_, v_x_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3(lean_object* v_cls_4102_, lean_object* v_msg_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___redArg(v_cls_4102_, v_msg_4103_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3___boxed(lean_object* v_cls_4117_, lean_object* v_msg_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__3(v_cls_4117_, v_msg_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(lean_object* v_oldTraces_4132_, lean_object* v_data_4133_, lean_object* v_ref_4134_, lean_object* v_msg_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___redArg(v_oldTraces_4132_, v_data_4133_, v_ref_4134_, v_msg_4135_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2___boxed(lean_object* v_oldTraces_4149_, lean_object* v_data_4150_, lean_object* v_ref_4151_, lean_object* v_msg_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize_spec__2_spec__2(v_oldTraces_4149_, v_data_4150_, v_ref_4151_, v_msg_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
return v_res_4165_;
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
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_CollectHyps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
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
