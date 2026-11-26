// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Cegar
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.BitVec public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Function public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Epr public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Lemmas public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Subsolver import Lean.Meta.Tactic.BVDecide.Prover.Bitblast import Lean.Meta.Tactic.BVDecide.External
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(uint8_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkUf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkEpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_BitVec_repr(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "bv_decide reached its round limit, consider increasing it via the `cegarRounds` config option"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTheories(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTheories___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Model found"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___boxed(lean_object**);
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___boxed(lean_object**);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "CEGAR step"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__1___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "The countermodel stayed the same for two iterations, this is a bug."};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___boxed(lean_object**);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_CegarCert_ofLratCert, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__1));
v___x_53_ = l_Lean_stringToMessageData(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___y_70_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__0));
v___x_92_ = l_Lean_Core_checkSystem(v___x_91_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_93_; lean_object* v_roundBudget_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
lean_dec_ref_known(v___x_92_, 1);
v___x_93_ = lean_st_ref_get(v_a_55_);
v_roundBudget_94_ = lean_ctor_get(v___x_93_, 5);
lean_inc(v_roundBudget_94_);
lean_dec(v___x_93_);
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_nat_dec_eq(v_roundBudget_94_, v___x_95_);
lean_dec(v_roundBudget_94_);
if (v___x_96_ == 0)
{
v___y_70_ = v_a_55_;
goto v___jp_69_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___closed__2);
v___x_98_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v___x_97_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
return v___x_98_;
}
}
else
{
return v___x_92_;
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v_satExpr_72_; lean_object* v_hypQueue_73_; lean_object* v_usedHyps_74_; uint8_t v_didChange_75_; lean_object* v_theoryState_76_; lean_object* v_solverTimeBudgetMs_77_; lean_object* v_roundBudget_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_90_; 
v___x_71_ = lean_st_ref_take(v___y_70_);
v_satExpr_72_ = lean_ctor_get(v___x_71_, 0);
v_hypQueue_73_ = lean_ctor_get(v___x_71_, 1);
v_usedHyps_74_ = lean_ctor_get(v___x_71_, 2);
v_didChange_75_ = lean_ctor_get_uint8(v___x_71_, sizeof(void*)*6);
v_theoryState_76_ = lean_ctor_get(v___x_71_, 3);
v_solverTimeBudgetMs_77_ = lean_ctor_get(v___x_71_, 4);
v_roundBudget_78_ = lean_ctor_get(v___x_71_, 5);
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_90_ == 0)
{
v___x_80_ = v___x_71_;
v_isShared_81_ = v_isSharedCheck_90_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_roundBudget_78_);
lean_inc(v_solverTimeBudgetMs_77_);
lean_inc(v_theoryState_76_);
lean_inc(v_usedHyps_74_);
lean_inc(v_hypQueue_73_);
lean_inc(v_satExpr_72_);
lean_dec(v___x_71_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_90_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_nat_sub(v_roundBudget_78_, v___x_83_);
lean_dec(v_roundBudget_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 5, v___x_84_);
v___x_86_ = v___x_80_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_satExpr_72_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_hypQueue_73_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v_usedHyps_74_);
lean_ctor_set(v_reuseFailAlloc_89_, 3, v_theoryState_76_);
lean_ctor_set(v_reuseFailAlloc_89_, 4, v_solverTimeBudgetMs_77_);
lean_ctor_set(v_reuseFailAlloc_89_, 5, v___x_84_);
lean_ctor_set_uint8(v_reuseFailAlloc_89_, sizeof(void*)*6, v_didChange_75_);
v___x_86_ = v_reuseFailAlloc_89_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_st_ref_put(v___y_70_, v___x_86_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_82_);
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination___boxed(lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(lean_object* v_00_u03b1_115_, lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v_msg_116_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_133_ = _args[0];
lean_object* v_msg_134_ = _args[1];
lean_object* v___y_135_ = _args[2];
lean_object* v___y_136_ = _args[3];
lean_object* v___y_137_ = _args[4];
lean_object* v___y_138_ = _args[5];
lean_object* v___y_139_ = _args[6];
lean_object* v___y_140_ = _args[7];
lean_object* v___y_141_ = _args[8];
lean_object* v___y_142_ = _args[9];
lean_object* v___y_143_ = _args[10];
lean_object* v___y_144_ = _args[11];
lean_object* v___y_145_ = _args[12];
lean_object* v___y_146_ = _args[13];
lean_object* v___y_147_ = _args[14];
lean_object* v___y_148_ = _args[15];
lean_object* v___y_149_ = _args[16];
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0(v_00_u03b1_133_, v_msg_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTheories(lean_object* v_cex_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
lean_inc_ref(v_cex_151_);
v___x_167_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkUf(v_cex_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_195_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_195_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_195_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_195_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint8_t v___x_172_; 
v___x_172_ = lean_unbox(v_a_168_);
lean_dec(v_a_168_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_del_object(v___x_170_);
v___x_173_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkEpr(v_cex_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v___x_173_, 0);
lean_dec(v_unused_182_);
v___x_175_ = v___x_173_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_dec(v___x_173_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_box(0);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_173_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_173_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_193_; 
lean_dec_ref(v_cex_151_);
v___x_191_ = lean_box(0);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_191_);
v___x_193_ = v___x_170_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v_cex_151_);
v_a_196_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_167_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_167_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTheories___boxed(lean_object* v_cex_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTheories(v_cex_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0_spec__0(lean_object* v_as_221_, size_t v_i_222_, size_t v_stop_223_, lean_object* v_b_224_){
_start:
{
lean_object* v___y_226_; uint8_t v___x_230_; 
v___x_230_ = lean_usize_dec_eq(v_i_222_, v_stop_223_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v_snd_232_; lean_object* v_fst_233_; uint8_t v___x_234_; 
v___x_231_ = lean_array_uget_borrowed(v_as_221_, v_i_222_);
v_snd_232_ = lean_ctor_get(v___x_231_, 1);
lean_inc(v_snd_232_);
v_fst_233_ = lean_ctor_get(v_snd_232_, 0);
v___x_234_ = lean_unbox(v_fst_233_);
if (v___x_234_ == 0)
{
lean_object* v_fst_235_; lean_object* v_snd_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_fst_235_ = lean_ctor_get(v___x_231_, 0);
v_snd_236_ = lean_ctor_get(v_snd_232_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_snd_232_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_snd_232_, 0);
lean_dec(v_unused_245_);
v___x_238_ = v_snd_232_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_snd_236_);
lean_dec(v_snd_232_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
lean_inc(v_fst_235_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v_fst_235_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_fst_235_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_snd_236_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_array_push(v_b_224_, v___x_241_);
v___y_226_ = v___x_242_;
goto v___jp_225_;
}
}
}
else
{
lean_dec(v_snd_232_);
v___y_226_ = v_b_224_;
goto v___jp_225_;
}
}
else
{
return v_b_224_;
}
v___jp_225_:
{
size_t v___x_227_; size_t v___x_228_; 
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_add(v_i_222_, v___x_227_);
v_i_222_ = v___x_228_;
v_b_224_ = v___y_226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0_spec__0___boxed(lean_object* v_as_246_, lean_object* v_i_247_, lean_object* v_stop_248_, lean_object* v_b_249_){
_start:
{
size_t v_i_boxed_250_; size_t v_stop_boxed_251_; lean_object* v_res_252_; 
v_i_boxed_250_ = lean_unbox_usize(v_i_247_);
lean_dec(v_i_247_);
v_stop_boxed_251_ = lean_unbox_usize(v_stop_248_);
lean_dec(v_stop_248_);
v_res_252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0_spec__0(v_as_246_, v_i_boxed_250_, v_stop_boxed_251_, v_b_249_);
lean_dec_ref(v_as_246_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0(lean_object* v_as_255_, lean_object* v_start_256_, lean_object* v_stop_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0___closed__0));
v___x_259_ = lean_nat_dec_lt(v_start_256_, v_stop_257_);
if (v___x_259_ == 0)
{
return v___x_258_;
}
else
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_array_get_size(v_as_255_);
v___x_261_ = lean_nat_dec_le(v_stop_257_, v___x_260_);
if (v___x_261_ == 0)
{
uint8_t v___x_262_; 
v___x_262_ = lean_nat_dec_lt(v_start_256_, v___x_260_);
if (v___x_262_ == 0)
{
return v___x_258_;
}
else
{
size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_usize_of_nat(v_start_256_);
v___x_264_ = lean_usize_of_nat(v___x_260_);
v___x_265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0_spec__0(v_as_255_, v___x_263_, v___x_264_, v___x_258_);
return v___x_265_;
}
}
else
{
size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_usize_of_nat(v_start_256_);
v___x_267_ = lean_usize_of_nat(v_stop_257_);
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0_spec__0(v_as_255_, v___x_266_, v___x_267_, v___x_258_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0___boxed(lean_object* v_as_269_, lean_object* v_start_270_, lean_object* v_stop_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0(v_as_269_, v_start_270_, v_stop_271_);
lean_dec(v_stop_271_);
lean_dec(v_start_270_);
lean_dec_ref(v_as_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(lean_object* v_cex_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_array_get_size(v_cex_273_);
v___x_277_ = l_Array_filterMapM___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations_spec__0(v_cex_273_, v___x_275_, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg___boxed(lean_object* v_cex_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(v_cex_279_);
lean_dec_ref(v_cex_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations(lean_object* v_cex_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(v_cex_282_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___boxed(lean_object* v_cex_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations(v_cex_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec_ref(v_cex_299_);
return v_res_315_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_unsigned_to_nat(32u);
v___x_317_ = lean_mk_empty_array_with_capacity(v___x_316_);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_319_ = ((size_t)5ULL);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_unsigned_to_nat(32u);
v___x_322_ = lean_mk_empty_array_with_capacity(v___x_321_);
v___x_323_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__0);
v___x_324_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_322_);
lean_ctor_set(v___x_324_, 2, v___x_320_);
lean_ctor_set(v___x_324_, 3, v___x_320_);
lean_ctor_set_usize(v___x_324_, 4, v___x_319_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg(lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v_traceState_328_; lean_object* v_traces_329_; lean_object* v___x_330_; lean_object* v_traceState_331_; lean_object* v_env_332_; lean_object* v_nextMacroScope_333_; lean_object* v_ngen_334_; lean_object* v_auxDeclNGen_335_; lean_object* v_cache_336_; lean_object* v_recordedDeps_337_; lean_object* v_messages_338_; lean_object* v_infoState_339_; lean_object* v_snapshotTasks_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_359_; 
v___x_327_ = lean_st_ref_get(v___y_325_);
v_traceState_328_ = lean_ctor_get(v___x_327_, 4);
lean_inc_ref(v_traceState_328_);
lean_dec(v___x_327_);
v_traces_329_ = lean_ctor_get(v_traceState_328_, 0);
lean_inc_ref(v_traces_329_);
lean_dec_ref(v_traceState_328_);
v___x_330_ = lean_st_ref_take(v___y_325_);
v_traceState_331_ = lean_ctor_get(v___x_330_, 4);
v_env_332_ = lean_ctor_get(v___x_330_, 0);
v_nextMacroScope_333_ = lean_ctor_get(v___x_330_, 1);
v_ngen_334_ = lean_ctor_get(v___x_330_, 2);
v_auxDeclNGen_335_ = lean_ctor_get(v___x_330_, 3);
v_cache_336_ = lean_ctor_get(v___x_330_, 5);
v_recordedDeps_337_ = lean_ctor_get(v___x_330_, 6);
v_messages_338_ = lean_ctor_get(v___x_330_, 7);
v_infoState_339_ = lean_ctor_get(v___x_330_, 8);
v_snapshotTasks_340_ = lean_ctor_get(v___x_330_, 9);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_359_ == 0)
{
v___x_342_ = v___x_330_;
v_isShared_343_ = v_isSharedCheck_359_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_snapshotTasks_340_);
lean_inc(v_infoState_339_);
lean_inc(v_messages_338_);
lean_inc(v_recordedDeps_337_);
lean_inc(v_cache_336_);
lean_inc(v_traceState_331_);
lean_inc(v_auxDeclNGen_335_);
lean_inc(v_ngen_334_);
lean_inc(v_nextMacroScope_333_);
lean_inc(v_env_332_);
lean_dec(v___x_330_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_359_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint64_t v_tid_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_357_; 
v_tid_344_ = lean_ctor_get_uint64(v_traceState_331_, sizeof(void*)*1);
v_isSharedCheck_357_ = !lean_is_exclusive(v_traceState_331_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v_traceState_331_, 0);
lean_dec(v_unused_358_);
v___x_346_ = v_traceState_331_;
v_isShared_347_ = v_isSharedCheck_357_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_traceState_331_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_357_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___closed__1);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_348_);
lean_ctor_set_uint64(v_reuseFailAlloc_356_, sizeof(void*)*1, v_tid_344_);
v___x_350_ = v_reuseFailAlloc_356_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v___x_350_);
v___x_352_ = v___x_342_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_env_332_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_nextMacroScope_333_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_ngen_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_auxDeclNGen_335_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v_cache_336_);
lean_ctor_set(v_reuseFailAlloc_355_, 6, v_recordedDeps_337_);
lean_ctor_set(v_reuseFailAlloc_355_, 7, v_messages_338_);
lean_ctor_set(v_reuseFailAlloc_355_, 8, v_infoState_339_);
lean_ctor_set(v_reuseFailAlloc_355_, 9, v_snapshotTasks_340_);
v___x_352_ = v_reuseFailAlloc_355_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_st_ref_put(v___y_325_, v___x_352_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v_traces_329_);
return v___x_354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg___boxed(lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg(v___y_360_);
lean_dec(v___y_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2(lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg(v___y_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___boxed(lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2(v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_394_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(lean_object* v_opts_395_, lean_object* v_opt_396_){
_start:
{
lean_object* v_name_397_; lean_object* v_defValue_398_; lean_object* v_map_399_; lean_object* v___x_400_; 
v_name_397_ = lean_ctor_get(v_opt_396_, 0);
v_defValue_398_ = lean_ctor_get(v_opt_396_, 1);
v_map_399_ = lean_ctor_get(v_opts_395_, 0);
v___x_400_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_399_, v_name_397_);
if (lean_obj_tag(v___x_400_) == 0)
{
uint8_t v___x_401_; 
v___x_401_ = lean_unbox(v_defValue_398_);
return v___x_401_;
}
else
{
lean_object* v_val_402_; 
v_val_402_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v___x_400_, 1);
if (lean_obj_tag(v_val_402_) == 1)
{
uint8_t v_v_403_; 
v_v_403_ = lean_ctor_get_uint8(v_val_402_, 0);
lean_dec_ref_known(v_val_402_, 0);
return v_v_403_;
}
else
{
uint8_t v___x_404_; 
lean_dec(v_val_402_);
v___x_404_ = lean_unbox(v_defValue_398_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3___boxed(lean_object* v_opts_405_, lean_object* v_opt_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_opts_405_, v_opt_406_);
lean_dec_ref(v_opt_406_);
lean_dec_ref(v_opts_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__1(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__0));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0(lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___closed__1);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0___boxed(lean_object* v_x_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___lam__0(v_x_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec_ref(v_x_430_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4_spec__5(size_t v_sz_447_, size_t v_i_448_, lean_object* v_bs_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_lt(v_i_448_, v_sz_447_);
if (v___x_450_ == 0)
{
return v_bs_449_;
}
else
{
lean_object* v_v_451_; lean_object* v_msg_452_; lean_object* v___x_453_; lean_object* v_bs_x27_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; 
v_v_451_ = lean_array_uget_borrowed(v_bs_449_, v_i_448_);
v_msg_452_ = lean_ctor_get(v_v_451_, 1);
lean_inc_ref(v_msg_452_);
v___x_453_ = lean_unsigned_to_nat(0u);
v_bs_x27_454_ = lean_array_uset(v_bs_449_, v_i_448_, v___x_453_);
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_add(v_i_448_, v___x_455_);
v___x_457_ = lean_array_uset(v_bs_x27_454_, v_i_448_, v_msg_452_);
v_i_448_ = v___x_456_;
v_bs_449_ = v___x_457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4_spec__5___boxed(lean_object* v_sz_459_, lean_object* v_i_460_, lean_object* v_bs_461_){
_start:
{
size_t v_sz_boxed_462_; size_t v_i_boxed_463_; lean_object* v_res_464_; 
v_sz_boxed_462_ = lean_unbox_usize(v_sz_459_);
lean_dec(v_sz_459_);
v_i_boxed_463_ = lean_unbox_usize(v_i_460_);
lean_dec(v_i_460_);
v_res_464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4_spec__5(v_sz_boxed_462_, v_i_boxed_463_, v_bs_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___redArg(lean_object* v_oldTraces_465_, lean_object* v_data_466_, lean_object* v_ref_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_toCold_474_; lean_object* v_currRecDepth_475_; lean_object* v_ref_476_; uint16_t v_optionFlags_477_; uint8_t v_suppressElabErrors_478_; uint8_t v_checkDeprecated_479_; uint8_t v_isRecordingDeps_480_; lean_object* v_ref_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_traceState_484_; lean_object* v_traces_485_; lean_object* v___x_486_; size_t v_sz_487_; size_t v___x_488_; lean_object* v___x_489_; lean_object* v_msg_490_; lean_object* v___x_491_; lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_530_; 
v_toCold_474_ = lean_ctor_get(v___y_471_, 0);
v_currRecDepth_475_ = lean_ctor_get(v___y_471_, 1);
v_ref_476_ = lean_ctor_get(v___y_471_, 2);
v_optionFlags_477_ = lean_ctor_get_uint16(v___y_471_, sizeof(void*)*3);
v_suppressElabErrors_478_ = lean_ctor_get_uint8(v___y_471_, sizeof(void*)*3 + 2);
v_checkDeprecated_479_ = lean_ctor_get_uint8(v___y_471_, sizeof(void*)*3 + 3);
v_isRecordingDeps_480_ = lean_ctor_get_uint8(v___y_471_, sizeof(void*)*3 + 4);
v_ref_481_ = l_Lean_replaceRef(v_ref_467_, v_ref_476_);
lean_inc(v_currRecDepth_475_);
lean_inc_ref(v_toCold_474_);
v___x_482_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_482_, 0, v_toCold_474_);
lean_ctor_set(v___x_482_, 1, v_currRecDepth_475_);
lean_ctor_set(v___x_482_, 2, v_ref_481_);
lean_ctor_set_uint16(v___x_482_, sizeof(void*)*3, v_optionFlags_477_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*3 + 2, v_suppressElabErrors_478_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*3 + 3, v_checkDeprecated_479_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*3 + 4, v_isRecordingDeps_480_);
v___x_483_ = lean_st_ref_get(v___y_472_);
v_traceState_484_ = lean_ctor_get(v___x_483_, 4);
lean_inc_ref(v_traceState_484_);
lean_dec(v___x_483_);
v_traces_485_ = lean_ctor_get(v_traceState_484_, 0);
lean_inc_ref(v_traces_485_);
lean_dec_ref(v_traceState_484_);
v___x_486_ = l_Lean_PersistentArray_toArray___redArg(v_traces_485_);
lean_dec_ref(v_traces_485_);
v_sz_487_ = lean_array_size(v___x_486_);
v___x_488_ = ((size_t)0ULL);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4_spec__5(v_sz_487_, v___x_488_, v___x_486_);
v_msg_490_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_490_, 0, v_data_466_);
lean_ctor_set(v_msg_490_, 1, v_msg_468_);
lean_ctor_set(v_msg_490_, 2, v___x_489_);
v___x_491_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msg_490_, v___y_469_, v___y_470_, v___x_482_, v___y_472_);
lean_dec_ref_known(v___x_482_, 3);
v_a_492_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_530_ == 0)
{
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_530_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_530_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v_traceState_497_; lean_object* v_env_498_; lean_object* v_nextMacroScope_499_; lean_object* v_ngen_500_; lean_object* v_auxDeclNGen_501_; lean_object* v_cache_502_; lean_object* v_recordedDeps_503_; lean_object* v_messages_504_; lean_object* v_infoState_505_; lean_object* v_snapshotTasks_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_529_; 
v___x_496_ = lean_st_ref_take(v___y_472_);
v_traceState_497_ = lean_ctor_get(v___x_496_, 4);
v_env_498_ = lean_ctor_get(v___x_496_, 0);
v_nextMacroScope_499_ = lean_ctor_get(v___x_496_, 1);
v_ngen_500_ = lean_ctor_get(v___x_496_, 2);
v_auxDeclNGen_501_ = lean_ctor_get(v___x_496_, 3);
v_cache_502_ = lean_ctor_get(v___x_496_, 5);
v_recordedDeps_503_ = lean_ctor_get(v___x_496_, 6);
v_messages_504_ = lean_ctor_get(v___x_496_, 7);
v_infoState_505_ = lean_ctor_get(v___x_496_, 8);
v_snapshotTasks_506_ = lean_ctor_get(v___x_496_, 9);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_529_ == 0)
{
v___x_508_ = v___x_496_;
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snapshotTasks_506_);
lean_inc(v_infoState_505_);
lean_inc(v_messages_504_);
lean_inc(v_recordedDeps_503_);
lean_inc(v_cache_502_);
lean_inc(v_traceState_497_);
lean_inc(v_auxDeclNGen_501_);
lean_inc(v_ngen_500_);
lean_inc(v_nextMacroScope_499_);
lean_inc(v_env_498_);
lean_dec(v___x_496_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
uint64_t v_tid_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_527_; 
v_tid_510_ = lean_ctor_get_uint64(v_traceState_497_, sizeof(void*)*1);
v_isSharedCheck_527_ = !lean_is_exclusive(v_traceState_497_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v_traceState_497_, 0);
lean_dec(v_unused_528_);
v___x_512_ = v_traceState_497_;
v_isShared_513_ = v_isSharedCheck_527_;
goto v_resetjp_511_;
}
else
{
lean_dec(v_traceState_497_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_527_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_514_ = lean_box(0);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_ref_467_);
lean_ctor_set(v___x_515_, 1, v_a_492_);
v___x_516_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_465_, v___x_515_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_516_);
v___x_518_ = v___x_512_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_516_);
lean_ctor_set_uint64(v_reuseFailAlloc_526_, sizeof(void*)*1, v_tid_510_);
v___x_518_ = v_reuseFailAlloc_526_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v___x_518_);
v___x_520_ = v___x_508_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_env_498_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_nextMacroScope_499_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_ngen_500_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_auxDeclNGen_501_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_525_, 5, v_cache_502_);
lean_ctor_set(v_reuseFailAlloc_525_, 6, v_recordedDeps_503_);
lean_ctor_set(v_reuseFailAlloc_525_, 7, v_messages_504_);
lean_ctor_set(v_reuseFailAlloc_525_, 8, v_infoState_505_);
lean_ctor_set(v_reuseFailAlloc_525_, 9, v_snapshotTasks_506_);
v___x_520_ = v_reuseFailAlloc_525_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = lean_st_ref_put(v___y_472_, v___x_520_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_514_);
v___x_523_ = v___x_494_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_514_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___redArg___boxed(lean_object* v_oldTraces_531_, lean_object* v_data_532_, lean_object* v_ref_533_, lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___redArg(v_oldTraces_531_, v_data_532_, v_ref_533_, v_msg_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__6(lean_object* v_e_541_){
_start:
{
if (lean_obj_tag(v_e_541_) == 0)
{
uint8_t v___x_542_; 
v___x_542_ = 2;
return v___x_542_;
}
else
{
uint8_t v___x_543_; 
v___x_543_ = 0;
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__6___boxed(lean_object* v_e_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__6(v_e_544_);
lean_dec_ref(v_e_544_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7(lean_object* v_opts_547_, lean_object* v_opt_548_){
_start:
{
lean_object* v_name_549_; lean_object* v_defValue_550_; lean_object* v_map_551_; lean_object* v___x_552_; 
v_name_549_ = lean_ctor_get(v_opt_548_, 0);
v_defValue_550_ = lean_ctor_get(v_opt_548_, 1);
v_map_551_ = lean_ctor_get(v_opts_547_, 0);
v___x_552_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_551_, v_name_549_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_inc(v_defValue_550_);
return v_defValue_550_;
}
else
{
lean_object* v_val_553_; 
v_val_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v___x_552_, 1);
if (lean_obj_tag(v_val_553_) == 3)
{
lean_object* v_v_554_; 
v_v_554_ = lean_ctor_get(v_val_553_, 0);
lean_inc(v_v_554_);
lean_dec_ref_known(v_val_553_, 1);
return v_v_554_;
}
else
{
lean_dec(v_val_553_);
lean_inc(v_defValue_550_);
return v_defValue_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7___boxed(lean_object* v_opts_555_, lean_object* v_opt_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7(v_opts_555_, v_opt_556_);
lean_dec_ref(v_opt_556_);
lean_dec_ref(v_opts_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg(lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_a_560_ = lean_ctor_get(v_x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v_x_558_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v_x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 1);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v_x_558_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v_x_558_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v_x_558_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 0);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg___boxed(lean_object* v_x_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg(v_x_576_);
return v_res_578_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0(void){
_start:
{
lean_object* v___x_579_; double v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_float_of_nat(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__1));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3(void){
_start:
{
lean_object* v___x_584_; double v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(1000u);
v___x_585_ = lean_float_of_nat(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4(lean_object* v_cls_586_, uint8_t v_collapsed_587_, lean_object* v_tag_588_, lean_object* v_opts_589_, uint8_t v_clsEnabled_590_, lean_object* v_oldTraces_591_, lean_object* v_msg_592_, lean_object* v_resStartStop_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v_data_614_; lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___x_619_; uint8_t v___x_620_; lean_object* v___y_622_; lean_object* v_a_623_; uint8_t v___y_638_; double v___y_670_; 
v_fst_609_ = lean_ctor_get(v_resStartStop_593_, 0);
lean_inc(v_fst_609_);
v_snd_610_ = lean_ctor_get(v_resStartStop_593_, 1);
lean_inc(v_snd_610_);
lean_dec_ref(v_resStartStop_593_);
v_fst_617_ = lean_ctor_get(v_snd_610_, 0);
lean_inc(v_fst_617_);
v_snd_618_ = lean_ctor_get(v_snd_610_, 1);
lean_inc(v_snd_618_);
lean_dec(v_snd_610_);
v___x_619_ = l_Lean_trace_profiler;
v___x_620_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_opts_589_, v___x_619_);
if (v___x_620_ == 0)
{
v___y_638_ = v___x_620_;
goto v___jp_637_;
}
else
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = l_Lean_trace_profiler_useHeartbeats;
v___x_676_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_opts_589_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; double v___x_679_; double v___x_680_; double v___x_681_; 
v___x_677_ = l_Lean_trace_profiler_threshold;
v___x_678_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7(v_opts_589_, v___x_677_);
v___x_679_ = lean_float_of_nat(v___x_678_);
v___x_680_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3);
v___x_681_ = lean_float_div(v___x_679_, v___x_680_);
v___y_670_ = v___x_681_;
goto v___jp_669_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; double v___x_684_; 
v___x_682_ = l_Lean_trace_profiler_threshold;
v___x_683_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7(v_opts_589_, v___x_682_);
v___x_684_ = lean_float_of_nat(v___x_683_);
v___y_670_ = v___x_684_;
goto v___jp_669_;
}
}
v___jp_611_:
{
lean_object* v___x_615_; 
lean_inc(v___y_612_);
v___x_615_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___redArg(v_oldTraces_591_, v_data_614_, v___y_612_, v___y_613_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v___x_616_; 
lean_dec_ref_known(v___x_615_, 1);
v___x_616_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg(v_fst_609_);
return v___x_616_;
}
else
{
lean_dec(v_fst_609_);
return v___x_615_;
}
}
v___jp_621_:
{
uint8_t v_result_624_; lean_object* v___x_625_; lean_object* v___x_626_; double v___x_627_; lean_object* v_data_628_; 
v_result_624_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__6(v_fst_609_);
v___x_625_ = lean_box(v_result_624_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0);
lean_inc_ref(v_tag_588_);
lean_inc_ref(v___x_626_);
lean_inc(v_cls_586_);
v_data_628_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_628_, 0, v_cls_586_);
lean_ctor_set(v_data_628_, 1, v___x_626_);
lean_ctor_set(v_data_628_, 2, v_tag_588_);
lean_ctor_set_float(v_data_628_, sizeof(void*)*3, v___x_627_);
lean_ctor_set_float(v_data_628_, sizeof(void*)*3 + 8, v___x_627_);
lean_ctor_set_uint8(v_data_628_, sizeof(void*)*3 + 16, v_collapsed_587_);
if (v___x_620_ == 0)
{
lean_dec_ref_known(v___x_626_, 1);
lean_dec(v_snd_618_);
lean_dec(v_fst_617_);
lean_dec_ref(v_tag_588_);
lean_dec(v_cls_586_);
v___y_612_ = v___y_622_;
v___y_613_ = v_a_623_;
v_data_614_ = v_data_628_;
goto v___jp_611_;
}
else
{
lean_object* v_data_629_; double v___x_630_; double v___x_631_; 
lean_dec_ref_known(v_data_628_, 3);
v_data_629_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_629_, 0, v_cls_586_);
lean_ctor_set(v_data_629_, 1, v___x_626_);
lean_ctor_set(v_data_629_, 2, v_tag_588_);
v___x_630_ = lean_unbox_float(v_fst_617_);
lean_dec(v_fst_617_);
lean_ctor_set_float(v_data_629_, sizeof(void*)*3, v___x_630_);
v___x_631_ = lean_unbox_float(v_snd_618_);
lean_dec(v_snd_618_);
lean_ctor_set_float(v_data_629_, sizeof(void*)*3 + 8, v___x_631_);
lean_ctor_set_uint8(v_data_629_, sizeof(void*)*3 + 16, v_collapsed_587_);
v___y_612_ = v___y_622_;
v___y_613_ = v_a_623_;
v_data_614_ = v_data_629_;
goto v___jp_611_;
}
}
v___jp_632_:
{
lean_object* v_ref_633_; lean_object* v___x_634_; 
v_ref_633_ = lean_ctor_get(v___y_606_, 2);
lean_inc(v___y_607_);
lean_inc_ref(v___y_606_);
lean_inc(v___y_605_);
lean_inc_ref(v___y_604_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
lean_inc(v___y_599_);
lean_inc(v___y_598_);
lean_inc_ref(v___y_597_);
lean_inc(v___y_596_);
lean_inc(v___y_595_);
lean_inc_ref(v___y_594_);
lean_inc(v_fst_609_);
v___x_634_ = lean_apply_16(v_msg_592_, v_fst_609_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, lean_box(0));
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v___y_622_ = v_ref_633_;
v_a_623_ = v_a_635_;
goto v___jp_621_;
}
else
{
lean_object* v___x_636_; 
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2);
v___y_622_ = v_ref_633_;
v_a_623_ = v___x_636_;
goto v___jp_621_;
}
}
v___jp_637_:
{
if (v_clsEnabled_590_ == 0)
{
if (v___y_638_ == 0)
{
lean_object* v___x_639_; lean_object* v_traceState_640_; lean_object* v_env_641_; lean_object* v_nextMacroScope_642_; lean_object* v_ngen_643_; lean_object* v_auxDeclNGen_644_; lean_object* v_cache_645_; lean_object* v_recordedDeps_646_; lean_object* v_messages_647_; lean_object* v_infoState_648_; lean_object* v_snapshotTasks_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_snd_618_);
lean_dec(v_fst_617_);
lean_dec_ref(v_msg_592_);
lean_dec_ref(v_tag_588_);
lean_dec(v_cls_586_);
v___x_639_ = lean_st_ref_take(v___y_607_);
v_traceState_640_ = lean_ctor_get(v___x_639_, 4);
v_env_641_ = lean_ctor_get(v___x_639_, 0);
v_nextMacroScope_642_ = lean_ctor_get(v___x_639_, 1);
v_ngen_643_ = lean_ctor_get(v___x_639_, 2);
v_auxDeclNGen_644_ = lean_ctor_get(v___x_639_, 3);
v_cache_645_ = lean_ctor_get(v___x_639_, 5);
v_recordedDeps_646_ = lean_ctor_get(v___x_639_, 6);
v_messages_647_ = lean_ctor_get(v___x_639_, 7);
v_infoState_648_ = lean_ctor_get(v___x_639_, 8);
v_snapshotTasks_649_ = lean_ctor_get(v___x_639_, 9);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_668_ == 0)
{
v___x_651_ = v___x_639_;
v_isShared_652_ = v_isSharedCheck_668_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_snapshotTasks_649_);
lean_inc(v_infoState_648_);
lean_inc(v_messages_647_);
lean_inc(v_recordedDeps_646_);
lean_inc(v_cache_645_);
lean_inc(v_traceState_640_);
lean_inc(v_auxDeclNGen_644_);
lean_inc(v_ngen_643_);
lean_inc(v_nextMacroScope_642_);
lean_inc(v_env_641_);
lean_dec(v___x_639_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_668_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
uint64_t v_tid_653_; lean_object* v_traces_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_667_; 
v_tid_653_ = lean_ctor_get_uint64(v_traceState_640_, sizeof(void*)*1);
v_traces_654_ = lean_ctor_get(v_traceState_640_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_traceState_640_);
if (v_isSharedCheck_667_ == 0)
{
v___x_656_ = v_traceState_640_;
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_traces_654_);
lean_dec(v_traceState_640_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_591_, v_traces_654_);
lean_dec_ref(v_traces_654_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_658_);
lean_ctor_set_uint64(v_reuseFailAlloc_666_, sizeof(void*)*1, v_tid_653_);
v___x_660_ = v_reuseFailAlloc_666_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v___x_660_);
v___x_662_ = v___x_651_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_env_641_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_nextMacroScope_642_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_ngen_643_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_auxDeclNGen_644_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_665_, 5, v_cache_645_);
lean_ctor_set(v_reuseFailAlloc_665_, 6, v_recordedDeps_646_);
lean_ctor_set(v_reuseFailAlloc_665_, 7, v_messages_647_);
lean_ctor_set(v_reuseFailAlloc_665_, 8, v_infoState_648_);
lean_ctor_set(v_reuseFailAlloc_665_, 9, v_snapshotTasks_649_);
v___x_662_ = v_reuseFailAlloc_665_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_st_ref_put(v___y_607_, v___x_662_);
v___x_664_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg(v_fst_609_);
return v___x_664_;
}
}
}
}
}
else
{
goto v___jp_632_;
}
}
else
{
goto v___jp_632_;
}
}
v___jp_669_:
{
double v___x_671_; double v___x_672_; double v___x_673_; uint8_t v___x_674_; 
v___x_671_ = lean_unbox_float(v_snd_618_);
v___x_672_ = lean_unbox_float(v_fst_617_);
v___x_673_ = lean_float_sub(v___x_671_, v___x_672_);
v___x_674_ = lean_float_decLt(v___y_670_, v___x_673_);
v___y_638_ = v___x_674_;
goto v___jp_637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___boxed(lean_object** _args){
lean_object* v_cls_685_ = _args[0];
lean_object* v_collapsed_686_ = _args[1];
lean_object* v_tag_687_ = _args[2];
lean_object* v_opts_688_ = _args[3];
lean_object* v_clsEnabled_689_ = _args[4];
lean_object* v_oldTraces_690_ = _args[5];
lean_object* v_msg_691_ = _args[6];
lean_object* v_resStartStop_692_ = _args[7];
lean_object* v___y_693_ = _args[8];
lean_object* v___y_694_ = _args[9];
lean_object* v___y_695_ = _args[10];
lean_object* v___y_696_ = _args[11];
lean_object* v___y_697_ = _args[12];
lean_object* v___y_698_ = _args[13];
lean_object* v___y_699_ = _args[14];
lean_object* v___y_700_ = _args[15];
lean_object* v___y_701_ = _args[16];
lean_object* v___y_702_ = _args[17];
lean_object* v___y_703_ = _args[18];
lean_object* v___y_704_ = _args[19];
lean_object* v___y_705_ = _args[20];
lean_object* v___y_706_ = _args[21];
lean_object* v___y_707_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_708_; uint8_t v_clsEnabled_boxed_709_; lean_object* v_res_710_; 
v_collapsed_boxed_708_ = lean_unbox(v_collapsed_686_);
v_clsEnabled_boxed_709_ = lean_unbox(v_clsEnabled_689_);
v_res_710_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4(v_cls_685_, v_collapsed_boxed_708_, v_tag_687_, v_opts_688_, v_clsEnabled_boxed_709_, v_oldTraces_690_, v_msg_691_, v_resStartStop_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec_ref(v_opts_688_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg(lean_object* v_cls_714_, lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_ref_721_; lean_object* v___x_722_; lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_768_; 
v_ref_721_ = lean_ctor_get(v___y_718_, 2);
v___x_722_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0_spec__0(v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_768_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_768_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_768_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v_traceState_728_; lean_object* v_env_729_; lean_object* v_nextMacroScope_730_; lean_object* v_ngen_731_; lean_object* v_auxDeclNGen_732_; lean_object* v_cache_733_; lean_object* v_recordedDeps_734_; lean_object* v_messages_735_; lean_object* v_infoState_736_; lean_object* v_snapshotTasks_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_767_; 
v___x_727_ = lean_st_ref_take(v___y_719_);
v_traceState_728_ = lean_ctor_get(v___x_727_, 4);
v_env_729_ = lean_ctor_get(v___x_727_, 0);
v_nextMacroScope_730_ = lean_ctor_get(v___x_727_, 1);
v_ngen_731_ = lean_ctor_get(v___x_727_, 2);
v_auxDeclNGen_732_ = lean_ctor_get(v___x_727_, 3);
v_cache_733_ = lean_ctor_get(v___x_727_, 5);
v_recordedDeps_734_ = lean_ctor_get(v___x_727_, 6);
v_messages_735_ = lean_ctor_get(v___x_727_, 7);
v_infoState_736_ = lean_ctor_get(v___x_727_, 8);
v_snapshotTasks_737_ = lean_ctor_get(v___x_727_, 9);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_767_ == 0)
{
v___x_739_ = v___x_727_;
v_isShared_740_ = v_isSharedCheck_767_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snapshotTasks_737_);
lean_inc(v_infoState_736_);
lean_inc(v_messages_735_);
lean_inc(v_recordedDeps_734_);
lean_inc(v_cache_733_);
lean_inc(v_traceState_728_);
lean_inc(v_auxDeclNGen_732_);
lean_inc(v_ngen_731_);
lean_inc(v_nextMacroScope_730_);
lean_inc(v_env_729_);
lean_dec(v___x_727_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_767_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
uint64_t v_tid_741_; lean_object* v_traces_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_766_; 
v_tid_741_ = lean_ctor_get_uint64(v_traceState_728_, sizeof(void*)*1);
v_traces_742_ = lean_ctor_get(v_traceState_728_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v_traceState_728_);
if (v_isSharedCheck_766_ == 0)
{
v___x_744_ = v_traceState_728_;
v_isShared_745_ = v_isSharedCheck_766_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_traces_742_);
lean_dec(v_traceState_728_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_766_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; double v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_746_ = lean_box(0);
v___x_747_ = lean_box(0);
v___x_748_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0);
v___x_749_ = 0;
v___x_750_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__0));
v___x_751_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_751_, 0, v_cls_714_);
lean_ctor_set(v___x_751_, 1, v___x_747_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
lean_ctor_set_float(v___x_751_, sizeof(void*)*3, v___x_748_);
lean_ctor_set_float(v___x_751_, sizeof(void*)*3 + 8, v___x_748_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*3 + 16, v___x_749_);
v___x_752_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__1));
v___x_753_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v_a_723_);
lean_ctor_set(v___x_753_, 2, v___x_752_);
lean_inc(v_ref_721_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_ref_721_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_PersistentArray_push___redArg(v_traces_742_, v___x_754_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_755_);
v___x_757_ = v___x_744_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_755_);
lean_ctor_set_uint64(v_reuseFailAlloc_765_, sizeof(void*)*1, v_tid_741_);
v___x_757_ = v_reuseFailAlloc_765_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 4, v___x_757_);
v___x_759_ = v___x_739_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_env_729_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_nextMacroScope_730_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_ngen_731_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_auxDeclNGen_732_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_764_, 5, v_cache_733_);
lean_ctor_set(v_reuseFailAlloc_764_, 6, v_recordedDeps_734_);
lean_ctor_set(v_reuseFailAlloc_764_, 7, v_messages_735_);
lean_ctor_set(v_reuseFailAlloc_764_, 8, v_infoState_736_);
lean_ctor_set(v_reuseFailAlloc_764_, 9, v_snapshotTasks_737_);
v___x_759_ = v_reuseFailAlloc_764_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_st_ref_put(v___y_719_, v___x_759_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_746_);
v___x_762_ = v___x_725_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_746_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___boxed(lean_object* v_cls_769_, lean_object* v_msg_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg(v_cls_769_, v_msg_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_776_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6(void){
_start:
{
lean_object* v_cls_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_cls_787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3));
v___x_788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__5));
v___x_789_ = l_Lean_Name_append(v___x_788_, v_cls_787_);
return v___x_789_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__8(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__7));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1(lean_object* v_as_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_a_813_; uint8_t v___x_817_; 
v___x_817_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v_b_796_);
return v___x_818_;
}
else
{
lean_object* v_a_819_; lean_object* v_toCold_820_; lean_object* v_options_821_; lean_object* v_fst_822_; lean_object* v_snd_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_854_; 
v_a_819_ = lean_array_uget(v_as_793_, v_i_795_);
v_toCold_820_ = lean_ctor_get(v___y_809_, 0);
v_options_821_ = lean_ctor_get(v_toCold_820_, 2);
v_fst_822_ = lean_ctor_get(v_a_819_, 0);
v_snd_823_ = lean_ctor_get(v_a_819_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_854_ == 0)
{
v___x_825_ = v_a_819_;
v_isShared_826_ = v_isSharedCheck_854_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_snd_823_);
lean_inc(v_fst_822_);
lean_dec(v_a_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_854_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_inheritedTraceOptions_827_; uint8_t v_hasTrace_828_; lean_object* v___x_829_; 
v_inheritedTraceOptions_827_ = lean_ctor_get(v_toCold_820_, 11);
v_hasTrace_828_ = lean_ctor_get_uint8(v_options_821_, sizeof(void*)*1);
v___x_829_ = lean_box(0);
if (v_hasTrace_828_ == 0)
{
lean_del_object(v___x_825_);
lean_dec(v_snd_823_);
lean_dec(v_fst_822_);
v_a_813_ = v___x_829_;
goto v___jp_812_;
}
else
{
lean_object* v_cls_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_cls_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3));
v___x_831_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6);
v___x_832_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_827_, v_options_821_, v___x_831_);
if (v___x_832_ == 0)
{
lean_del_object(v___x_825_);
lean_dec(v_snd_823_);
lean_dec(v_fst_822_);
v_a_813_ = v___x_829_;
goto v___jp_812_;
}
else
{
lean_object* v_w_833_; lean_object* v_bv_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_853_; 
v_w_833_ = lean_ctor_get(v_snd_823_, 0);
v_bv_834_ = lean_ctor_get(v_snd_823_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_snd_823_);
if (v_isSharedCheck_853_ == 0)
{
v___x_836_ = v_snd_823_;
v_isShared_837_ = v_isSharedCheck_853_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_bv_834_);
lean_inc(v_w_833_);
lean_dec(v_snd_823_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_853_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = l_Lean_MessageData_ofExpr(v_fst_822_);
v___x_839_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__8);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 7);
lean_ctor_set(v___x_836_, 1, v___x_839_);
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_839_);
v___x_841_ = v_reuseFailAlloc_852_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_842_ = l_BitVec_repr(v_w_833_, v_bv_834_);
v___x_843_ = l_Std_Format_defWidth;
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = l_Std_Format_pretty(v___x_842_, v___x_843_, v___x_844_, v___x_844_);
v___x_846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
v___x_847_ = l_Lean_MessageData_ofFormat(v___x_846_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 7);
lean_ctor_set(v___x_825_, 1, v___x_847_);
lean_ctor_set(v___x_825_, 0, v___x_841_);
v___x_849_ = v___x_825_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg(v_cls_830_, v___x_849_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_dec_ref_known(v___x_850_, 1);
v_a_813_ = v___x_829_;
goto v___jp_812_;
}
else
{
return v___x_850_;
}
}
}
}
}
}
}
}
v___jp_812_:
{
size_t v___x_814_; size_t v___x_815_; 
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_795_, v___x_814_);
v_i_795_ = v___x_815_;
v_b_796_ = v_a_813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___boxed(lean_object** _args){
lean_object* v_as_855_ = _args[0];
lean_object* v_sz_856_ = _args[1];
lean_object* v_i_857_ = _args[2];
lean_object* v_b_858_ = _args[3];
lean_object* v___y_859_ = _args[4];
lean_object* v___y_860_ = _args[5];
lean_object* v___y_861_ = _args[6];
lean_object* v___y_862_ = _args[7];
lean_object* v___y_863_ = _args[8];
lean_object* v___y_864_ = _args[9];
lean_object* v___y_865_ = _args[10];
lean_object* v___y_866_ = _args[11];
lean_object* v___y_867_ = _args[12];
lean_object* v___y_868_ = _args[13];
lean_object* v___y_869_ = _args[14];
lean_object* v___y_870_ = _args[15];
lean_object* v___y_871_ = _args[16];
lean_object* v___y_872_ = _args[17];
lean_object* v___y_873_ = _args[18];
_start:
{
size_t v_sz_boxed_874_; size_t v_i_boxed_875_; lean_object* v_res_876_; 
v_sz_boxed_874_ = lean_unbox_usize(v_sz_856_);
lean_dec(v_sz_856_);
v_i_boxed_875_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1(v_as_855_, v_sz_boxed_874_, v_i_boxed_875_, v_b_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec_ref(v_as_855_);
return v_res_876_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1(void){
_start:
{
lean_object* v___x_878_; double v___x_879_; 
v___x_878_ = lean_unsigned_to_nat(1000000000u);
v___x_879_ = lean_float_of_nat(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel(lean_object* v_cex_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_____do__lift_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v_toCold_926_; lean_object* v_options_927_; uint8_t v_hasTrace_928_; 
v_toCold_926_ = lean_ctor_get(v_a_895_, 0);
v_options_927_ = lean_ctor_get(v_toCold_926_, 2);
v_hasTrace_928_ = lean_ctor_get_uint8(v_options_927_, sizeof(void*)*1);
if (v_hasTrace_928_ == 0)
{
lean_object* v___x_929_; lean_object* v_a_930_; 
v___x_929_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(v_cex_882_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref(v___x_929_);
v_____do__lift_899_ = v_a_930_;
v___y_900_ = v_a_883_;
v___y_901_ = v_a_884_;
v___y_902_ = v_a_885_;
v___y_903_ = v_a_886_;
v___y_904_ = v_a_887_;
v___y_905_ = v_a_888_;
v___y_906_ = v_a_889_;
v___y_907_ = v_a_890_;
v___y_908_ = v_a_891_;
v___y_909_ = v_a_892_;
v___y_910_ = v_a_893_;
v___y_911_ = v_a_894_;
v___y_912_ = v_a_895_;
v___y_913_ = v_a_896_;
goto v___jp_898_;
}
else
{
lean_object* v_inheritedTraceOptions_931_; lean_object* v___f_932_; lean_object* v_cls_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v_a_940_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v_a_955_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v_a_960_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v_a_972_; 
v_inheritedTraceOptions_931_ = lean_ctor_get(v_toCold_926_, 11);
v___f_932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__0));
v_cls_933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3));
v___x_934_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__0));
v___x_935_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6);
v___x_936_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_931_, v_options_927_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = l_Lean_trace_profiler;
v___x_998_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_options_927_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v_a_1000_; 
v___x_999_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(v_cex_882_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v_____do__lift_899_ = v_a_1000_;
v___y_900_ = v_a_883_;
v___y_901_ = v_a_884_;
v___y_902_ = v_a_885_;
v___y_903_ = v_a_886_;
v___y_904_ = v_a_887_;
v___y_905_ = v_a_888_;
v___y_906_ = v_a_889_;
v___y_907_ = v_a_890_;
v___y_908_ = v_a_891_;
v___y_909_ = v_a_892_;
v___y_910_ = v_a_893_;
v___y_911_ = v_a_894_;
v___y_912_ = v_a_895_;
v___y_913_ = v_a_896_;
goto v___jp_898_;
}
else
{
goto v___jp_974_;
}
}
else
{
goto v___jp_974_;
}
v___jp_937_:
{
lean_object* v___x_941_; double v___x_942_; double v___x_943_; double v___x_944_; double v___x_945_; double v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_941_ = lean_io_mono_nanos_now();
v___x_942_ = lean_float_of_nat(v___y_939_);
v___x_943_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1);
v___x_944_ = lean_float_div(v___x_942_, v___x_943_);
v___x_945_ = lean_float_of_nat(v___x_941_);
v___x_946_ = lean_float_div(v___x_945_, v___x_943_);
v___x_947_ = lean_box_float(v___x_944_);
v___x_948_ = lean_box_float(v___x_946_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v_a_940_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4(v_cls_933_, v_hasTrace_928_, v___x_934_, v_options_927_, v___x_936_, v___y_938_, v___f_932_, v___x_950_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
return v___x_951_;
}
v___jp_952_:
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_a_955_);
v___y_938_ = v___y_953_;
v___y_939_ = v___y_954_;
v_a_940_ = v___x_956_;
goto v___jp_937_;
}
v___jp_957_:
{
lean_object* v___x_961_; double v___x_962_; double v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_961_ = lean_io_get_num_heartbeats();
v___x_962_ = lean_float_of_nat(v___y_959_);
v___x_963_ = lean_float_of_nat(v___x_961_);
v___x_964_ = lean_box_float(v___x_962_);
v___x_965_ = lean_box_float(v___x_963_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v_a_960_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4(v_cls_933_, v_hasTrace_928_, v___x_934_, v_options_927_, v___x_936_, v___y_958_, v___f_932_, v___x_967_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
return v___x_968_;
}
v___jp_969_:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_a_972_);
v___y_958_ = v___y_970_;
v___y_959_ = v___y_971_;
v_a_960_ = v___x_973_;
goto v___jp_957_;
}
v___jp_974_:
{
lean_object* v___x_975_; lean_object* v_a_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_975_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg(v_a_896_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
v___x_977_ = l_Lean_trace_profiler_useHeartbeats;
v___x_978_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_options_927_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_a_981_; lean_object* v___x_982_; size_t v_sz_983_; size_t v___x_984_; lean_object* v___x_985_; 
v___x_979_ = lean_io_mono_nanos_now();
v___x_980_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(v_cex_882_);
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v___x_982_ = lean_box(0);
v_sz_983_ = lean_array_size(v_a_981_);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1(v_a_981_, v_sz_983_, v___x_984_, v___x_982_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec(v_a_981_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_986_; 
lean_dec_ref_known(v___x_985_, 1);
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__2));
v___y_938_ = v_a_976_;
v___y_939_ = v___x_979_;
v_a_940_ = v___x_986_;
goto v___jp_937_;
}
else
{
lean_object* v_a_987_; 
v_a_987_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_985_, 1);
v___y_953_ = v_a_976_;
v___y_954_ = v___x_979_;
v_a_955_ = v_a_987_;
goto v___jp_952_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_991_; size_t v_sz_992_; size_t v___x_993_; lean_object* v___x_994_; 
v___x_988_ = lean_io_get_num_heartbeats();
v___x_989_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(v_cex_882_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref(v___x_989_);
v___x_991_ = lean_box(0);
v_sz_992_ = lean_array_size(v_a_990_);
v___x_993_ = ((size_t)0ULL);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1(v_a_990_, v_sz_992_, v___x_993_, v___x_991_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec(v_a_990_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v___x_995_; 
lean_dec_ref_known(v___x_994_, 1);
v___x_995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__2));
v___y_958_ = v_a_976_;
v___y_959_ = v___x_988_;
v_a_960_ = v___x_995_;
goto v___jp_957_;
}
else
{
lean_object* v_a_996_; 
v_a_996_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_994_, 1);
v___y_970_ = v_a_976_;
v___y_971_ = v___x_988_;
v_a_972_ = v_a_996_;
goto v___jp_969_;
}
}
}
}
v___jp_898_:
{
lean_object* v___x_914_; size_t v_sz_915_; size_t v___x_916_; lean_object* v___x_917_; 
v___x_914_ = lean_box(0);
v_sz_915_ = lean_array_size(v_____do__lift_899_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1(v_____do__lift_899_, v_sz_915_, v___x_916_, v___x_914_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec_ref(v_____do__lift_899_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v___x_917_, 0);
lean_dec(v_unused_925_);
v___x_919_ = v___x_917_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_dec(v___x_917_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_914_);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_914_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___boxed(lean_object* v_cex_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel(v_cex_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec_ref(v_cex_1001_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0(lean_object* v_cls_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg(v_cls_1018_, v_msg_1019_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___boxed(lean_object** _args){
lean_object* v_cls_1036_ = _args[0];
lean_object* v_msg_1037_ = _args[1];
lean_object* v___y_1038_ = _args[2];
lean_object* v___y_1039_ = _args[3];
lean_object* v___y_1040_ = _args[4];
lean_object* v___y_1041_ = _args[5];
lean_object* v___y_1042_ = _args[6];
lean_object* v___y_1043_ = _args[7];
lean_object* v___y_1044_ = _args[8];
lean_object* v___y_1045_ = _args[9];
lean_object* v___y_1046_ = _args[10];
lean_object* v___y_1047_ = _args[11];
lean_object* v___y_1048_ = _args[12];
lean_object* v___y_1049_ = _args[13];
lean_object* v___y_1050_ = _args[14];
lean_object* v___y_1051_ = _args[15];
lean_object* v___y_1052_ = _args[16];
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0(v_cls_1036_, v_msg_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5(lean_object* v_00_u03b1_1054_, lean_object* v_x_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg(v_x_1055_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___boxed(lean_object** _args){
lean_object* v_00_u03b1_1072_ = _args[0];
lean_object* v_x_1073_ = _args[1];
lean_object* v___y_1074_ = _args[2];
lean_object* v___y_1075_ = _args[3];
lean_object* v___y_1076_ = _args[4];
lean_object* v___y_1077_ = _args[5];
lean_object* v___y_1078_ = _args[6];
lean_object* v___y_1079_ = _args[7];
lean_object* v___y_1080_ = _args[8];
lean_object* v___y_1081_ = _args[9];
lean_object* v___y_1082_ = _args[10];
lean_object* v___y_1083_ = _args[11];
lean_object* v___y_1084_ = _args[12];
lean_object* v___y_1085_ = _args[13];
lean_object* v___y_1086_ = _args[14];
lean_object* v___y_1087_ = _args[15];
lean_object* v___y_1088_ = _args[16];
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5(v_00_u03b1_1072_, v_x_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4(lean_object* v_oldTraces_1090_, lean_object* v_data_1091_, lean_object* v_ref_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___redArg(v_oldTraces_1090_, v_data_1091_, v_ref_1092_, v_msg_1093_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___boxed(lean_object** _args){
lean_object* v_oldTraces_1110_ = _args[0];
lean_object* v_data_1111_ = _args[1];
lean_object* v_ref_1112_ = _args[2];
lean_object* v_msg_1113_ = _args[3];
lean_object* v___y_1114_ = _args[4];
lean_object* v___y_1115_ = _args[5];
lean_object* v___y_1116_ = _args[6];
lean_object* v___y_1117_ = _args[7];
lean_object* v___y_1118_ = _args[8];
lean_object* v___y_1119_ = _args[9];
lean_object* v___y_1120_ = _args[10];
lean_object* v___y_1121_ = _args[11];
lean_object* v___y_1122_ = _args[12];
lean_object* v___y_1123_ = _args[13];
lean_object* v___y_1124_ = _args[14];
lean_object* v___y_1125_ = _args[15];
lean_object* v___y_1126_ = _args[16];
lean_object* v___y_1127_ = _args[17];
lean_object* v___y_1128_ = _args[18];
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4(v_oldTraces_1110_, v_data_1111_, v_ref_1112_, v_msg_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__1));
v___x_1134_ = l_Lean_MessageData_ofFormat(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0(lean_object* v_x_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___closed__2);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0___boxed(lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__0(v_x_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_x_1153_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__1(lean_object* v_a_1170_, lean_object* v_____r_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel(v_a_1170_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v___x_1188_; 
lean_dec_ref_known(v___x_1187_, 1);
v___x_1188_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v_a_1170_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTheories(v_a_1189_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v___x_1190_, 0);
lean_dec(v_unused_1199_);
v___x_1192_ = v___x_1190_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1190_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_a_1170_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_a_1170_);
v_a_1200_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1190_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1190_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v_a_1170_);
v_a_1208_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1188_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1188_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_a_1170_);
v_a_1216_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1187_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1187_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__1___boxed(lean_object** _args){
lean_object* v_a_1224_ = _args[0];
lean_object* v_____r_1225_ = _args[1];
lean_object* v___y_1226_ = _args[2];
lean_object* v___y_1227_ = _args[3];
lean_object* v___y_1228_ = _args[4];
lean_object* v___y_1229_ = _args[5];
lean_object* v___y_1230_ = _args[6];
lean_object* v___y_1231_ = _args[7];
lean_object* v___y_1232_ = _args[8];
lean_object* v___y_1233_ = _args[9];
lean_object* v___y_1234_ = _args[10];
lean_object* v___y_1235_ = _args[11];
lean_object* v___y_1236_ = _args[12];
lean_object* v___y_1237_ = _args[13];
lean_object* v___y_1238_ = _args[14];
lean_object* v___y_1239_ = _args[15];
lean_object* v___y_1240_ = _args[16];
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__1(v_a_1224_, v_____r_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1241_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg(lean_object* v_xs_1242_, lean_object* v_ys_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v_zero_1245_; uint8_t v_isZero_1246_; 
v_zero_1245_ = lean_unsigned_to_nat(0u);
v_isZero_1246_ = lean_nat_dec_eq(v_x_1244_, v_zero_1245_);
if (v_isZero_1246_ == 1)
{
lean_dec(v_x_1244_);
return v_isZero_1246_;
}
else
{
lean_object* v_one_1247_; lean_object* v_n_1248_; lean_object* v___x_1249_; lean_object* v_fst_1250_; lean_object* v_snd_1251_; lean_object* v___x_1252_; lean_object* v_fst_1253_; lean_object* v_snd_1254_; uint8_t v___x_1255_; 
v_one_1247_ = lean_unsigned_to_nat(1u);
v_n_1248_ = lean_nat_sub(v_x_1244_, v_one_1247_);
lean_dec(v_x_1244_);
v___x_1249_ = lean_array_fget_borrowed(v_xs_1242_, v_n_1248_);
v_fst_1250_ = lean_ctor_get(v___x_1249_, 0);
v_snd_1251_ = lean_ctor_get(v___x_1249_, 1);
v___x_1252_ = lean_array_fget_borrowed(v_ys_1243_, v_n_1248_);
v_fst_1253_ = lean_ctor_get(v___x_1252_, 0);
v_snd_1254_ = lean_ctor_get(v___x_1252_, 1);
v___x_1255_ = lean_expr_eqv(v_fst_1250_, v_fst_1253_);
if (v___x_1255_ == 0)
{
lean_dec(v_n_1248_);
return v___x_1255_;
}
else
{
lean_object* v_fst_1256_; lean_object* v_snd_1257_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; uint8_t v___x_1263_; 
v_fst_1256_ = lean_ctor_get(v_snd_1251_, 0);
v_snd_1257_ = lean_ctor_get(v_snd_1251_, 1);
v_fst_1258_ = lean_ctor_get(v_snd_1254_, 0);
v_snd_1259_ = lean_ctor_get(v_snd_1254_, 1);
v___x_1263_ = lean_unbox(v_fst_1258_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_unbox(v_fst_1256_);
if (v___x_1264_ == 0)
{
goto v___jp_1260_;
}
else
{
uint8_t v___x_1265_; 
lean_dec(v_n_1248_);
v___x_1265_ = lean_unbox(v_fst_1258_);
return v___x_1265_;
}
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_unbox(v_fst_1256_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; 
lean_dec(v_n_1248_);
v___x_1267_ = lean_unbox(v_fst_1256_);
return v___x_1267_;
}
else
{
goto v___jp_1260_;
}
}
v___jp_1260_:
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Std_Tactic_BVDecide_BVExpr_instDecidableEqPackedBitVec_decEq(v_snd_1257_, v_snd_1259_);
if (v___x_1261_ == 0)
{
lean_dec(v_n_1248_);
return v___x_1261_;
}
else
{
v_x_1244_ = v_n_1248_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg___boxed(lean_object* v_xs_1268_, lean_object* v_ys_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg(v_xs_1268_, v_ys_1269_, v_x_1270_);
lean_dec_ref(v_ys_1269_);
lean_dec_ref(v_xs_1268_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1_spec__1(lean_object* v_e_1273_){
_start:
{
if (lean_obj_tag(v_e_1273_) == 0)
{
uint8_t v___x_1274_; 
v___x_1274_ = 2;
return v___x_1274_;
}
else
{
uint8_t v___x_1275_; 
v___x_1275_ = 0;
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1_spec__1___boxed(lean_object* v_e_1276_){
_start:
{
uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_res_1277_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1_spec__1(v_e_1276_);
lean_dec_ref(v_e_1276_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1(lean_object* v_cls_1279_, uint8_t v_collapsed_1280_, lean_object* v_tag_1281_, lean_object* v_opts_1282_, uint8_t v_clsEnabled_1283_, lean_object* v_oldTraces_1284_, lean_object* v_msg_1285_, lean_object* v_resStartStop_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v_data_1307_; lean_object* v_fst_1318_; lean_object* v_snd_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; lean_object* v___y_1323_; lean_object* v_a_1324_; uint8_t v___y_1339_; double v___y_1371_; 
v_fst_1302_ = lean_ctor_get(v_resStartStop_1286_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v_resStartStop_1286_, 1);
lean_inc(v_snd_1303_);
lean_dec_ref(v_resStartStop_1286_);
v_fst_1318_ = lean_ctor_get(v_snd_1303_, 0);
lean_inc(v_fst_1318_);
v_snd_1319_ = lean_ctor_get(v_snd_1303_, 1);
lean_inc(v_snd_1319_);
lean_dec(v_snd_1303_);
v___x_1320_ = l_Lean_trace_profiler;
v___x_1321_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_opts_1282_, v___x_1320_);
if (v___x_1321_ == 0)
{
v___y_1339_ = v___x_1321_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1377_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_opts_1282_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; double v___x_1380_; double v___x_1381_; double v___x_1382_; 
v___x_1378_ = l_Lean_trace_profiler_threshold;
v___x_1379_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7(v_opts_1282_, v___x_1378_);
v___x_1380_ = lean_float_of_nat(v___x_1379_);
v___x_1381_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__3);
v___x_1382_ = lean_float_div(v___x_1380_, v___x_1381_);
v___y_1371_ = v___x_1382_;
goto v___jp_1370_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; double v___x_1385_; 
v___x_1383_ = l_Lean_trace_profiler_threshold;
v___x_1384_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__7(v_opts_1282_, v___x_1383_);
v___x_1385_ = lean_float_of_nat(v___x_1384_);
v___y_1371_ = v___x_1385_;
goto v___jp_1370_;
}
}
v___jp_1304_:
{
lean_object* v___x_1308_; 
lean_inc(v___y_1305_);
v___x_1308_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__4___redArg(v_oldTraces_1284_, v_data_1307_, v___y_1305_, v___y_1306_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1309_; 
lean_dec_ref_known(v___x_1308_, 1);
v___x_1309_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg(v_fst_1302_);
return v___x_1309_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_fst_1302_);
v_a_1310_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1308_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
v___jp_1322_:
{
uint8_t v_result_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; double v___x_1328_; lean_object* v_data_1329_; 
v_result_1325_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1_spec__1(v_fst_1302_);
v___x_1326_ = lean_box(v_result_1325_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
v___x_1328_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__0);
lean_inc_ref(v_tag_1281_);
lean_inc_ref(v___x_1327_);
lean_inc(v_cls_1279_);
v_data_1329_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1329_, 0, v_cls_1279_);
lean_ctor_set(v_data_1329_, 1, v___x_1327_);
lean_ctor_set(v_data_1329_, 2, v_tag_1281_);
lean_ctor_set_float(v_data_1329_, sizeof(void*)*3, v___x_1328_);
lean_ctor_set_float(v_data_1329_, sizeof(void*)*3 + 8, v___x_1328_);
lean_ctor_set_uint8(v_data_1329_, sizeof(void*)*3 + 16, v_collapsed_1280_);
if (v___x_1321_ == 0)
{
lean_dec_ref_known(v___x_1327_, 1);
lean_dec(v_snd_1319_);
lean_dec(v_fst_1318_);
lean_dec_ref(v_tag_1281_);
lean_dec(v_cls_1279_);
v___y_1305_ = v___y_1323_;
v___y_1306_ = v_a_1324_;
v_data_1307_ = v_data_1329_;
goto v___jp_1304_;
}
else
{
lean_object* v_data_1330_; double v___x_1331_; double v___x_1332_; 
lean_dec_ref_known(v_data_1329_, 3);
v_data_1330_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1330_, 0, v_cls_1279_);
lean_ctor_set(v_data_1330_, 1, v___x_1327_);
lean_ctor_set(v_data_1330_, 2, v_tag_1281_);
v___x_1331_ = lean_unbox_float(v_fst_1318_);
lean_dec(v_fst_1318_);
lean_ctor_set_float(v_data_1330_, sizeof(void*)*3, v___x_1331_);
v___x_1332_ = lean_unbox_float(v_snd_1319_);
lean_dec(v_snd_1319_);
lean_ctor_set_float(v_data_1330_, sizeof(void*)*3 + 8, v___x_1332_);
lean_ctor_set_uint8(v_data_1330_, sizeof(void*)*3 + 16, v_collapsed_1280_);
v___y_1305_ = v___y_1323_;
v___y_1306_ = v_a_1324_;
v_data_1307_ = v_data_1330_;
goto v___jp_1304_;
}
}
v___jp_1333_:
{
lean_object* v_ref_1334_; lean_object* v___x_1335_; 
v_ref_1334_ = lean_ctor_get(v___y_1299_, 2);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc(v___y_1292_);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
lean_inc(v_fst_1302_);
v___x_1335_ = lean_apply_16(v_msg_1285_, v_fst_1302_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, lean_box(0));
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v___y_1323_ = v_ref_1334_;
v_a_1324_ = v_a_1336_;
goto v___jp_1322_;
}
else
{
lean_object* v___x_1337_; 
lean_dec_ref_known(v___x_1335_, 1);
v___x_1337_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4___closed__2);
v___y_1323_ = v_ref_1334_;
v_a_1324_ = v___x_1337_;
goto v___jp_1322_;
}
}
v___jp_1338_:
{
if (v_clsEnabled_1283_ == 0)
{
if (v___y_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v_traceState_1341_; lean_object* v_env_1342_; lean_object* v_nextMacroScope_1343_; lean_object* v_ngen_1344_; lean_object* v_auxDeclNGen_1345_; lean_object* v_cache_1346_; lean_object* v_recordedDeps_1347_; lean_object* v_messages_1348_; lean_object* v_infoState_1349_; lean_object* v_snapshotTasks_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_snd_1319_);
lean_dec(v_fst_1318_);
lean_dec_ref(v_msg_1285_);
lean_dec_ref(v_tag_1281_);
lean_dec(v_cls_1279_);
v___x_1340_ = lean_st_ref_take(v___y_1300_);
v_traceState_1341_ = lean_ctor_get(v___x_1340_, 4);
v_env_1342_ = lean_ctor_get(v___x_1340_, 0);
v_nextMacroScope_1343_ = lean_ctor_get(v___x_1340_, 1);
v_ngen_1344_ = lean_ctor_get(v___x_1340_, 2);
v_auxDeclNGen_1345_ = lean_ctor_get(v___x_1340_, 3);
v_cache_1346_ = lean_ctor_get(v___x_1340_, 5);
v_recordedDeps_1347_ = lean_ctor_get(v___x_1340_, 6);
v_messages_1348_ = lean_ctor_get(v___x_1340_, 7);
v_infoState_1349_ = lean_ctor_get(v___x_1340_, 8);
v_snapshotTasks_1350_ = lean_ctor_get(v___x_1340_, 9);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1352_ = v___x_1340_;
v_isShared_1353_ = v_isSharedCheck_1369_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_snapshotTasks_1350_);
lean_inc(v_infoState_1349_);
lean_inc(v_messages_1348_);
lean_inc(v_recordedDeps_1347_);
lean_inc(v_cache_1346_);
lean_inc(v_traceState_1341_);
lean_inc(v_auxDeclNGen_1345_);
lean_inc(v_ngen_1344_);
lean_inc(v_nextMacroScope_1343_);
lean_inc(v_env_1342_);
lean_dec(v___x_1340_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1369_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
uint64_t v_tid_1354_; lean_object* v_traces_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1368_; 
v_tid_1354_ = lean_ctor_get_uint64(v_traceState_1341_, sizeof(void*)*1);
v_traces_1355_ = lean_ctor_get(v_traceState_1341_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_traceState_1341_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1357_ = v_traceState_1341_;
v_isShared_1358_ = v_isSharedCheck_1368_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_traces_1355_);
lean_dec(v_traceState_1341_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1368_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1284_, v_traces_1355_);
lean_dec_ref(v_traces_1355_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1359_);
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1359_);
lean_ctor_set_uint64(v_reuseFailAlloc_1367_, sizeof(void*)*1, v_tid_1354_);
v___x_1361_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 4, v___x_1361_);
v___x_1363_ = v___x_1352_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_env_1342_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_nextMacroScope_1343_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_ngen_1344_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_auxDeclNGen_1345_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1366_, 5, v_cache_1346_);
lean_ctor_set(v_reuseFailAlloc_1366_, 6, v_recordedDeps_1347_);
lean_ctor_set(v_reuseFailAlloc_1366_, 7, v_messages_1348_);
lean_ctor_set(v_reuseFailAlloc_1366_, 8, v_infoState_1349_);
lean_ctor_set(v_reuseFailAlloc_1366_, 9, v_snapshotTasks_1350_);
v___x_1363_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_st_ref_put(v___y_1300_, v___x_1363_);
v___x_1365_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__4_spec__5___redArg(v_fst_1302_);
return v___x_1365_;
}
}
}
}
}
else
{
goto v___jp_1333_;
}
}
else
{
goto v___jp_1333_;
}
}
v___jp_1370_:
{
double v___x_1372_; double v___x_1373_; double v___x_1374_; uint8_t v___x_1375_; 
v___x_1372_ = lean_unbox_float(v_snd_1319_);
v___x_1373_ = lean_unbox_float(v_fst_1318_);
v___x_1374_ = lean_float_sub(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_float_decLt(v___y_1371_, v___x_1374_);
v___y_1339_ = v___x_1375_;
goto v___jp_1338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1___boxed(lean_object** _args){
lean_object* v_cls_1386_ = _args[0];
lean_object* v_collapsed_1387_ = _args[1];
lean_object* v_tag_1388_ = _args[2];
lean_object* v_opts_1389_ = _args[3];
lean_object* v_clsEnabled_1390_ = _args[4];
lean_object* v_oldTraces_1391_ = _args[5];
lean_object* v_msg_1392_ = _args[6];
lean_object* v_resStartStop_1393_ = _args[7];
lean_object* v___y_1394_ = _args[8];
lean_object* v___y_1395_ = _args[9];
lean_object* v___y_1396_ = _args[10];
lean_object* v___y_1397_ = _args[11];
lean_object* v___y_1398_ = _args[12];
lean_object* v___y_1399_ = _args[13];
lean_object* v___y_1400_ = _args[14];
lean_object* v___y_1401_ = _args[15];
lean_object* v___y_1402_ = _args[16];
lean_object* v___y_1403_ = _args[17];
lean_object* v___y_1404_ = _args[18];
lean_object* v___y_1405_ = _args[19];
lean_object* v___y_1406_ = _args[20];
lean_object* v___y_1407_ = _args[21];
lean_object* v___y_1408_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_1409_; uint8_t v_clsEnabled_boxed_1410_; lean_object* v_res_1411_; 
v_collapsed_boxed_1409_ = lean_unbox(v_collapsed_1387_);
v_clsEnabled_boxed_1410_ = lean_unbox(v_clsEnabled_1390_);
v_res_1411_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1(v_cls_1386_, v_collapsed_boxed_1409_, v_tag_1388_, v_opts_1389_, v_clsEnabled_boxed_1410_, v_oldTraces_1391_, v_msg_1392_, v_resStartStop_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec_ref(v_opts_1389_);
return v_res_1411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__0));
v___x_1414_ = l_Lean_stringToMessageData(v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep(lean_object* v_lastCex_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v_toCold_1551_; lean_object* v_options_1552_; uint8_t v_hasTrace_1553_; 
v_toCold_1551_ = lean_ctor_get(v_a_1429_, 0);
v_options_1552_ = lean_ctor_get(v_toCold_1551_, 2);
v_hasTrace_1553_ = lean_ctor_get_uint8(v_options_1552_, sizeof(void*)*1);
if (v_hasTrace_1553_ == 0)
{
lean_object* v___x_1554_; 
v___x_1554_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_dec_ref_known(v___x_1554_, 1);
v___y_1486_ = v_a_1417_;
v___y_1487_ = v_a_1418_;
v___y_1488_ = v_a_1419_;
v___y_1489_ = v_a_1420_;
v___y_1490_ = v_a_1421_;
v___y_1491_ = v_a_1422_;
v___y_1492_ = v_a_1423_;
v___y_1493_ = v_a_1424_;
v___y_1494_ = v_a_1425_;
v___y_1495_ = v_a_1426_;
v___y_1496_ = v_a_1427_;
v___y_1497_ = v_a_1428_;
v___y_1498_ = v_a_1429_;
v___y_1499_ = v_a_1430_;
goto v___jp_1485_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1554_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v_a_1572_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v_a_1584_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v_a_1589_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v_a_1606_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v_a_1621_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v_a_1626_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; 
v_inheritedTraceOptions_1563_ = lean_ctor_get(v_toCold_1551_, 11);
v___f_1564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__2));
v___x_1565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__3));
v___x_1566_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__0___redArg___closed__0));
v___x_1567_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__1___closed__6);
v___x_1568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1563_, v_options_1552_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1711_ = l_Lean_trace_profiler;
v___x_1712_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_options_1552_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_dec_ref_known(v___x_1713_, 1);
v___y_1486_ = v_a_1417_;
v___y_1487_ = v_a_1418_;
v___y_1488_ = v_a_1419_;
v___y_1489_ = v_a_1420_;
v___y_1490_ = v_a_1421_;
v___y_1491_ = v_a_1422_;
v___y_1492_ = v_a_1423_;
v___y_1493_ = v_a_1424_;
v___y_1494_ = v_a_1425_;
v___y_1495_ = v_a_1426_;
v___y_1496_ = v_a_1427_;
v___y_1497_ = v_a_1428_;
v___y_1498_ = v_a_1429_;
v___y_1499_ = v_a_1430_;
goto v___jp_1485_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
goto v___jp_1640_;
}
}
else
{
goto v___jp_1640_;
}
v___jp_1569_:
{
lean_object* v___x_1573_; double v___x_1574_; double v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1573_ = lean_io_get_num_heartbeats();
v___x_1574_ = lean_float_of_nat(v___y_1570_);
v___x_1575_ = lean_float_of_nat(v___x_1573_);
v___x_1576_ = lean_box_float(v___x_1574_);
v___x_1577_ = lean_box_float(v___x_1575_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_a_1572_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1(v___x_1565_, v_hasTrace_1553_, v___x_1566_, v_options_1552_, v___x_1568_, v___y_1571_, v___f_1564_, v___x_1579_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
return v___x_1580_;
}
v___jp_1581_:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_a_1584_);
v___y_1570_ = v___y_1582_;
v___y_1571_ = v___y_1583_;
v_a_1572_ = v___x_1585_;
goto v___jp_1569_;
}
v___jp_1586_:
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_a_1589_);
v___y_1570_ = v___y_1587_;
v___y_1571_ = v___y_1588_;
v_a_1572_ = v___x_1590_;
goto v___jp_1569_;
}
v___jp_1591_:
{
if (lean_obj_tag(v___y_1594_) == 0)
{
lean_object* v_a_1595_; 
v_a_1595_ = lean_ctor_get(v___y_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___y_1594_, 1);
v___y_1587_ = v___y_1592_;
v___y_1588_ = v___y_1593_;
v_a_1589_ = v_a_1595_;
goto v___jp_1586_;
}
else
{
lean_object* v_a_1596_; 
v_a_1596_ = lean_ctor_get(v___y_1594_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___y_1594_, 1);
v___y_1582_ = v___y_1592_;
v___y_1583_ = v___y_1593_;
v_a_1584_ = v_a_1596_;
goto v___jp_1581_;
}
}
v___jp_1597_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_box(0);
lean_inc(v_a_1430_);
lean_inc_ref(v_a_1429_);
lean_inc(v_a_1428_);
lean_inc_ref(v_a_1427_);
lean_inc(v_a_1426_);
lean_inc_ref(v_a_1425_);
lean_inc(v_a_1424_);
lean_inc_ref(v_a_1423_);
lean_inc(v_a_1422_);
lean_inc(v_a_1421_);
lean_inc_ref(v_a_1420_);
lean_inc(v_a_1419_);
lean_inc(v_a_1418_);
lean_inc_ref(v_a_1417_);
v___x_1602_ = lean_apply_16(v___y_1599_, v___x_1601_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, lean_box(0));
v___y_1592_ = v___y_1598_;
v___y_1593_ = v___y_1600_;
v___y_1594_ = v___x_1602_;
goto v___jp_1591_;
}
v___jp_1603_:
{
lean_object* v___x_1607_; double v___x_1608_; double v___x_1609_; double v___x_1610_; double v___x_1611_; double v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1607_ = lean_io_mono_nanos_now();
v___x_1608_ = lean_float_of_nat(v___y_1604_);
v___x_1609_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel___closed__1);
v___x_1610_ = lean_float_div(v___x_1608_, v___x_1609_);
v___x_1611_ = lean_float_of_nat(v___x_1607_);
v___x_1612_ = lean_float_div(v___x_1611_, v___x_1609_);
v___x_1613_ = lean_box_float(v___x_1610_);
v___x_1614_ = lean_box_float(v___x_1612_);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_a_1606_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__1(v___x_1565_, v_hasTrace_1553_, v___x_1566_, v_options_1552_, v___x_1568_, v___y_1605_, v___f_1564_, v___x_1616_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
return v___x_1617_;
}
v___jp_1618_:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v_a_1621_);
v___y_1604_ = v___y_1619_;
v___y_1605_ = v___y_1620_;
v_a_1606_ = v___x_1622_;
goto v___jp_1603_;
}
v___jp_1623_:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1627_, 0, v_a_1626_);
v___y_1604_ = v___y_1624_;
v___y_1605_ = v___y_1625_;
v_a_1606_ = v___x_1627_;
goto v___jp_1603_;
}
v___jp_1628_:
{
if (lean_obj_tag(v___y_1631_) == 0)
{
lean_object* v_a_1632_; 
v_a_1632_ = lean_ctor_get(v___y_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___y_1631_, 1);
v___y_1619_ = v___y_1629_;
v___y_1620_ = v___y_1630_;
v_a_1621_ = v_a_1632_;
goto v___jp_1618_;
}
else
{
lean_object* v_a_1633_; 
v_a_1633_ = lean_ctor_get(v___y_1631_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___y_1631_, 1);
v___y_1624_ = v___y_1629_;
v___y_1625_ = v___y_1630_;
v_a_1626_ = v_a_1633_;
goto v___jp_1623_;
}
}
v___jp_1634_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_box(0);
lean_inc(v_a_1430_);
lean_inc_ref(v_a_1429_);
lean_inc(v_a_1428_);
lean_inc_ref(v_a_1427_);
lean_inc(v_a_1426_);
lean_inc_ref(v_a_1425_);
lean_inc(v_a_1424_);
lean_inc_ref(v_a_1423_);
lean_inc(v_a_1422_);
lean_inc(v_a_1421_);
lean_inc_ref(v_a_1420_);
lean_inc(v_a_1419_);
lean_inc(v_a_1418_);
lean_inc_ref(v_a_1417_);
v___x_1639_ = lean_apply_16(v___y_1636_, v___x_1638_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, lean_box(0));
v___y_1629_ = v___y_1635_;
v___y_1630_ = v___y_1637_;
v___y_1631_ = v___x_1639_;
goto v___jp_1628_;
}
v___jp_1640_:
{
lean_object* v___x_1641_; lean_object* v_a_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1641_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__2___redArg(v_a_1430_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
v___x_1643_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1644_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel_spec__3(v_options_1552_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_io_mono_nanos_now();
v___x_1646_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref_known(v___x_1646_, 1);
v___x_1647_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1675_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1675_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1675_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
if (lean_obj_tag(v_a_1648_) == 0)
{
lean_object* v_a_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
lean_del_object(v___x_1650_);
v_a_1652_ = lean_ctor_get(v_a_1648_, 0);
lean_inc_n(v_a_1652_, 2);
lean_dec_ref_known(v_a_1648_, 1);
v___f_1653_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__1___boxed), 17, 1);
lean_closure_set(v___f_1653_, 0, v_a_1652_);
v___x_1654_ = lean_array_get_size(v_lastCex_1416_);
v___x_1655_ = lean_array_get_size(v_a_1652_);
v___x_1656_ = lean_nat_dec_eq(v___x_1654_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_dec(v_a_1652_);
v___y_1635_ = v___x_1645_;
v___y_1636_ = v___f_1653_;
v___y_1637_ = v_a_1642_;
goto v___jp_1634_;
}
else
{
uint8_t v___x_1657_; 
v___x_1657_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg(v_lastCex_1416_, v_a_1652_, v___x_1654_);
lean_dec(v_a_1652_);
if (v___x_1657_ == 0)
{
v___y_1635_ = v___x_1645_;
v___y_1636_ = v___f_1653_;
v___y_1637_ = v_a_1642_;
goto v___jp_1634_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v_a_1660_; 
lean_dec_ref(v___f_1653_);
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1);
v___x_1659_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v___x_1658_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref(v___x_1659_);
v___y_1624_ = v___x_1645_;
v___y_1625_ = v_a_1642_;
v_a_1626_ = v_a_1660_;
goto v___jp_1623_;
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1674_; 
v_a_1661_ = lean_ctor_get(v_a_1648_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_a_1648_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1663_ = v_a_1648_;
v_isShared_1664_ = v_isSharedCheck_1674_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v_a_1648_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1674_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 1);
lean_ctor_set(v___x_1650_, 0, v_a_1661_);
v___x_1666_ = v___x_1650_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_1666_, v_a_1418_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v_a_1668_);
v___x_1670_ = v___x_1663_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
v___y_1619_ = v___x_1645_;
v___y_1620_ = v_a_1642_;
v_a_1621_ = v___x_1670_;
goto v___jp_1618_;
}
}
else
{
lean_object* v_a_1672_; 
lean_del_object(v___x_1663_);
v_a_1672_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1667_, 1);
v___y_1624_ = v___x_1645_;
v___y_1625_ = v_a_1642_;
v_a_1626_ = v_a_1672_;
goto v___jp_1623_;
}
}
}
}
}
}
else
{
lean_object* v_a_1676_; 
v_a_1676_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1647_, 1);
v___y_1624_ = v___x_1645_;
v___y_1625_ = v_a_1642_;
v_a_1626_ = v_a_1676_;
goto v___jp_1623_;
}
}
else
{
lean_object* v_a_1677_; 
v_a_1677_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1646_, 1);
v___y_1624_ = v___x_1645_;
v___y_1625_ = v_a_1642_;
v_a_1626_ = v_a_1677_;
goto v___jp_1623_;
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_io_get_num_heartbeats();
v___x_1679_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1680_; 
lean_dec_ref_known(v___x_1679_, 1);
v___x_1680_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1708_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1708_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1708_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
if (lean_obj_tag(v_a_1681_) == 0)
{
lean_object* v_a_1685_; lean_object* v___f_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
lean_del_object(v___x_1683_);
v_a_1685_ = lean_ctor_get(v_a_1681_, 0);
lean_inc_n(v_a_1685_, 2);
lean_dec_ref_known(v_a_1681_, 1);
v___f_1686_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___lam__1___boxed), 17, 1);
lean_closure_set(v___f_1686_, 0, v_a_1685_);
v___x_1687_ = lean_array_get_size(v_lastCex_1416_);
v___x_1688_ = lean_array_get_size(v_a_1685_);
v___x_1689_ = lean_nat_dec_eq(v___x_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_dec(v_a_1685_);
v___y_1598_ = v___x_1678_;
v___y_1599_ = v___f_1686_;
v___y_1600_ = v_a_1642_;
goto v___jp_1597_;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg(v_lastCex_1416_, v_a_1685_, v___x_1687_);
lean_dec(v_a_1685_);
if (v___x_1690_ == 0)
{
v___y_1598_ = v___x_1678_;
v___y_1599_ = v___f_1686_;
v___y_1600_ = v_a_1642_;
goto v___jp_1597_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_a_1693_; 
lean_dec_ref(v___f_1686_);
v___x_1691_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1);
v___x_1692_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v___x_1691_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref(v___x_1692_);
v___y_1582_ = v___x_1678_;
v___y_1583_ = v_a_1642_;
v_a_1584_ = v_a_1693_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1707_; 
v_a_1694_ = lean_ctor_get(v_a_1681_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_a_1681_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1696_ = v_a_1681_;
v_isShared_1697_ = v_isSharedCheck_1707_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v_a_1681_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1707_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 1);
lean_ctor_set(v___x_1683_, 0, v_a_1694_);
v___x_1699_ = v___x_1683_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_1699_, v_a_1418_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v_a_1701_);
v___x_1703_ = v___x_1696_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
v___y_1587_ = v___x_1678_;
v___y_1588_ = v_a_1642_;
v_a_1589_ = v___x_1703_;
goto v___jp_1586_;
}
}
else
{
lean_object* v_a_1705_; 
lean_del_object(v___x_1696_);
v_a_1705_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1700_, 1);
v___y_1582_ = v___x_1678_;
v___y_1583_ = v_a_1642_;
v_a_1584_ = v_a_1705_;
goto v___jp_1581_;
}
}
}
}
}
}
else
{
lean_object* v_a_1709_; 
v_a_1709_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1680_, 1);
v___y_1582_ = v___x_1678_;
v___y_1583_ = v_a_1642_;
v_a_1584_ = v_a_1709_;
goto v___jp_1581_;
}
}
else
{
lean_object* v_a_1710_; 
v_a_1710_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1679_, 1);
v___y_1582_ = v___x_1678_;
v___y_1583_ = v_a_1642_;
v_a_1584_ = v_a_1710_;
goto v___jp_1581_;
}
}
}
}
v___jp_1432_:
{
lean_object* v___x_1448_; 
v___x_1448_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_traceModel(v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1449_; 
lean_dec_ref_known(v___x_1448_, 1);
v___x_1449_ = l_Lean_Meta_Tactic_BVDecide_CegarM_CounterExample_ofArray(v___y_1433_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTheories(v_a_1450_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1459_; 
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v___x_1451_, 0);
lean_dec(v_unused_1460_);
v___x_1453_ = v___x_1451_;
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v___x_1451_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___y_1433_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v___y_1433_);
v_a_1461_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1451_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1451_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v___y_1433_);
v_a_1469_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1449_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1449_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v___y_1433_);
v_a_1477_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1448_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1448_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
v___jp_1485_:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
if (lean_obj_tag(v_a_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_a_1502_ = lean_ctor_get(v_a_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v_a_1501_, 1);
v___x_1503_ = lean_array_get_size(v_lastCex_1416_);
v___x_1504_ = lean_array_get_size(v_a_1502_);
v___x_1505_ = lean_nat_dec_eq(v___x_1503_, v___x_1504_);
if (v___x_1505_ == 0)
{
v___y_1433_ = v_a_1502_;
v___y_1434_ = v___y_1486_;
v___y_1435_ = v___y_1487_;
v___y_1436_ = v___y_1488_;
v___y_1437_ = v___y_1489_;
v___y_1438_ = v___y_1490_;
v___y_1439_ = v___y_1491_;
v___y_1440_ = v___y_1492_;
v___y_1441_ = v___y_1493_;
v___y_1442_ = v___y_1494_;
v___y_1443_ = v___y_1495_;
v___y_1444_ = v___y_1496_;
v___y_1445_ = v___y_1497_;
v___y_1446_ = v___y_1498_;
v___y_1447_ = v___y_1499_;
goto v___jp_1432_;
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg(v_lastCex_1416_, v_a_1502_, v___x_1503_);
if (v___x_1506_ == 0)
{
v___y_1433_ = v_a_1502_;
v___y_1434_ = v___y_1486_;
v___y_1435_ = v___y_1487_;
v___y_1436_ = v___y_1488_;
v___y_1437_ = v___y_1489_;
v___y_1438_ = v___y_1490_;
v___y_1439_ = v___y_1491_;
v___y_1440_ = v___y_1492_;
v___y_1441_ = v___y_1493_;
v___y_1442_ = v___y_1494_;
v___y_1443_ = v___y_1495_;
v___y_1444_ = v___y_1496_;
v___y_1445_ = v___y_1497_;
v___y_1446_ = v___y_1498_;
v___y_1447_ = v___y_1499_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_a_1502_);
v___x_1507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___closed__1);
v___x_1508_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_checkTermination_spec__0___redArg(v___x_1507_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1542_; 
v_a_1517_ = lean_ctor_get(v_a_1501_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_a_1501_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1519_ = v_a_1501_;
v_isShared_1520_ = v_isSharedCheck_1542_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v_a_1501_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1542_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_a_1517_);
v___x_1522_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_1521_, v___y_1487_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1533_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1533_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1533_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v_a_1523_);
v___x_1528_ = v___x_1519_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1528_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_del_object(v___x_1519_);
v_a_1534_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1522_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1522_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1500_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1500_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep___boxed(lean_object* v_lastCex_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep(v_lastCex_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec_ref(v_lastCex_1722_);
return v_res_1738_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0(lean_object* v_xs_1739_, lean_object* v_ys_1740_, lean_object* v_hsz_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___redArg(v_xs_1739_, v_ys_1740_, v_x_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0___boxed(lean_object* v_xs_1745_, lean_object* v_ys_1746_, lean_object* v_hsz_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
uint8_t v_res_1750_; lean_object* v_r_1751_; 
v_res_1750_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep_spec__0(v_xs_1745_, v_ys_1746_, v_hsz_1747_, v_x_1748_, v_x_1749_);
lean_dec_ref(v_ys_1746_);
lean_dec_ref(v_xs_1745_);
v_r_1751_ = lean_box(v_res_1750_);
return v_r_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_1753_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_tacticContext_1756_; lean_object* v_config_1757_; lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1769_; 
v_tacticContext_1756_ = lean_ctor_get(v_a_1752_, 2);
v_config_1757_ = lean_ctor_get(v_tacticContext_1756_, 5);
v_a_1758_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1760_ = v___x_1755_;
v_isShared_1761_ = v_isSharedCheck_1769_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1755_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1769_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint8_t v_solverMode_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v_solverMode_1762_ = lean_ctor_get_uint8(v_config_1757_, sizeof(void*)*3 + 10);
v___x_1763_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_ofMode(v_solverMode_1762_);
v___x_1764_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_addIncremental(v___x_1763_);
v___x_1765_ = l_Lean_Meta_Tactic_BVDecide_External_SatOptions_configureSolver(v___x_1764_, v_a_1758_);
lean_dec(v_a_1758_);
lean_dec_ref(v___x_1764_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1765_);
v___x_1767_ = v___x_1760_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1755_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1755_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg___boxed(lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_1778_, v_a_1779_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v_a_1782_, v_a_1783_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___boxed(lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver(v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(size_t v_sz_1814_, size_t v_i_1815_, lean_object* v_bs_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_usize_dec_lt(v_i_1815_, v_sz_1814_);
if (v___x_1817_ == 0)
{
return v_bs_1816_;
}
else
{
lean_object* v_v_1818_; lean_object* v_funExpr_1819_; lean_object* v___x_1820_; lean_object* v_bs_x27_1821_; size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v_v_1818_ = lean_array_uget_borrowed(v_bs_1816_, v_i_1815_);
v_funExpr_1819_ = lean_ctor_get(v_v_1818_, 0);
lean_inc_ref(v_funExpr_1819_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v_bs_x27_1821_ = lean_array_uset(v_bs_1816_, v_i_1815_, v___x_1820_);
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = lean_usize_add(v_i_1815_, v___x_1822_);
v___x_1824_ = lean_array_uset(v_bs_x27_1821_, v_i_1815_, v_funExpr_1819_);
v_i_1815_ = v___x_1823_;
v_bs_1816_ = v___x_1824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1___boxed(lean_object* v_sz_1826_, lean_object* v_i_1827_, lean_object* v_bs_1828_){
_start:
{
size_t v_sz_boxed_1829_; size_t v_i_boxed_1830_; lean_object* v_res_1831_; 
v_sz_boxed_1829_ = lean_unbox_usize(v_sz_1826_);
lean_dec(v_sz_1826_);
v_i_boxed_1830_ = lean_unbox_usize(v_i_1827_);
lean_dec(v_i_1827_);
v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(v_sz_boxed_1829_, v_i_boxed_1830_, v_bs_1828_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(lean_object* v_a_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_snd_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1968_; 
v_snd_1848_ = lean_ctor_get(v_a_1832_, 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_a_1832_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v_a_1832_, 0);
lean_dec(v_unused_1969_);
v___x_1850_ = v_a_1832_;
v_isShared_1851_ = v_isSharedCheck_1968_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_snd_1848_);
lean_dec(v_a_1832_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1968_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; uint8_t v_didChange_1855_; 
v___x_1852_ = lean_box(0);
v___x_1853_ = 1;
v___x_1854_ = lean_st_ref_get(v___y_1834_);
v_didChange_1855_ = lean_ctor_get_uint8(v___x_1854_, sizeof(void*)*6);
lean_dec(v___x_1854_);
if (v_didChange_1855_ == 0)
{
lean_object* v___x_1857_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1857_ = v___x_1850_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_snd_1848_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
else
{
lean_object* v___x_1860_; 
v___x_1860_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarStep(v_snd_1848_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1959_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1959_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1959_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
if (lean_obj_tag(v_a_1861_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1943_; 
lean_del_object(v___x_1863_);
lean_dec(v_snd_1848_);
v_a_1865_ = lean_ctor_get(v_a_1861_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_a_1861_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1867_ = v_a_1861_;
v_isShared_1868_ = v_isSharedCheck_1943_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v_a_1861_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1943_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; uint8_t v___x_1871_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v___x_1871_ = lean_unbox(v_a_1870_);
lean_dec(v_a_1870_);
switch(v___x_1871_)
{
case 0:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_Meta_Tactic_BVDecide_CegarM_createCert___redArg(v___x_1852_, v___y_1834_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1887_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1887_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1887_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 1);
lean_ctor_set(v___x_1867_, 0, v_a_1873_);
v___x_1878_ = v___x_1867_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v_a_1865_);
lean_ctor_set(v___x_1850_, 0, v___x_1879_);
v___x_1881_ = v___x_1850_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_a_1865_);
v___x_1881_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1881_);
v___x_1883_ = v___x_1875_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_del_object(v___x_1867_);
lean_dec(v_a_1865_);
lean_del_object(v___x_1850_);
v_a_1888_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1872_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1872_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
case 1:
{
lean_object* v___x_1896_; lean_object* v_satExpr_1897_; lean_object* v_hypQueue_1898_; lean_object* v_usedHyps_1899_; lean_object* v_theoryState_1900_; lean_object* v_solverTimeBudgetMs_1901_; lean_object* v_roundBudget_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1914_; 
lean_del_object(v___x_1867_);
v___x_1896_ = lean_st_ref_take(v___y_1834_);
v_satExpr_1897_ = lean_ctor_get(v___x_1896_, 0);
v_hypQueue_1898_ = lean_ctor_get(v___x_1896_, 1);
v_usedHyps_1899_ = lean_ctor_get(v___x_1896_, 2);
v_theoryState_1900_ = lean_ctor_get(v___x_1896_, 3);
v_solverTimeBudgetMs_1901_ = lean_ctor_get(v___x_1896_, 4);
v_roundBudget_1902_ = lean_ctor_get(v___x_1896_, 5);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1904_ = v___x_1896_;
v_isShared_1905_ = v_isSharedCheck_1914_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_roundBudget_1902_);
lean_inc(v_solverTimeBudgetMs_1901_);
lean_inc(v_theoryState_1900_);
lean_inc(v_usedHyps_1899_);
lean_inc(v_hypQueue_1898_);
lean_inc(v_satExpr_1897_);
lean_dec(v___x_1896_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1914_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_satExpr_1897_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_hypQueue_1898_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_usedHyps_1899_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_theoryState_1900_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_solverTimeBudgetMs_1901_);
lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_roundBudget_1902_);
v___x_1907_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_ctor_set_uint8(v___x_1907_, sizeof(void*)*6, v___x_1853_);
v___x_1908_ = lean_st_ref_put(v___y_1834_, v___x_1907_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v_a_1865_);
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1910_ = v___x_1850_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_a_1865_);
v___x_1910_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
v_a_1832_ = v___x_1910_;
goto _start;
}
}
}
}
default: 
{
uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v_satExpr_1917_; lean_object* v_hypQueue_1918_; lean_object* v_usedHyps_1919_; lean_object* v_theoryState_1920_; lean_object* v_solverTimeBudgetMs_1921_; lean_object* v_roundBudget_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1934_; 
lean_del_object(v___x_1867_);
v___x_1915_ = 0;
v___x_1916_ = lean_st_ref_take(v___y_1834_);
v_satExpr_1917_ = lean_ctor_get(v___x_1916_, 0);
v_hypQueue_1918_ = lean_ctor_get(v___x_1916_, 1);
v_usedHyps_1919_ = lean_ctor_get(v___x_1916_, 2);
v_theoryState_1920_ = lean_ctor_get(v___x_1916_, 3);
v_solverTimeBudgetMs_1921_ = lean_ctor_get(v___x_1916_, 4);
v_roundBudget_1922_ = lean_ctor_get(v___x_1916_, 5);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1924_ = v___x_1916_;
v_isShared_1925_ = v_isSharedCheck_1934_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_roundBudget_1922_);
lean_inc(v_solverTimeBudgetMs_1921_);
lean_inc(v_theoryState_1920_);
lean_inc(v_usedHyps_1919_);
lean_inc(v_hypQueue_1918_);
lean_inc(v_satExpr_1917_);
lean_dec(v___x_1916_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1934_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_satExpr_1917_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_hypQueue_1918_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_usedHyps_1919_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_theoryState_1920_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v_solverTimeBudgetMs_1921_);
lean_ctor_set(v_reuseFailAlloc_1933_, 5, v_roundBudget_1922_);
v___x_1927_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
lean_ctor_set_uint8(v___x_1927_, sizeof(void*)*6, v___x_1915_);
v___x_1928_ = lean_st_ref_put(v___y_1834_, v___x_1927_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v_a_1865_);
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1930_ = v___x_1850_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_a_1865_);
v___x_1930_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
v_a_1832_ = v___x_1930_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_del_object(v___x_1867_);
lean_dec(v_a_1865_);
lean_del_object(v___x_1850_);
v_a_1935_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1869_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1869_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1958_; 
v_a_1944_ = lean_ctor_get(v_a_1861_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_a_1861_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1946_ = v_a_1861_;
v_isShared_1947_ = v_isSharedCheck_1958_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v_a_1861_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1958_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1950_);
v___x_1952_ = v___x_1850_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_snd_1848_);
v___x_1952_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1952_);
v___x_1954_ = v___x_1863_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_del_object(v___x_1850_);
lean_dec(v_snd_1848_);
v_a_1960_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1860_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1860_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg___boxed(lean_object* v_a_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(lean_object* v_ctx_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_lastCex_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v_config_2011_; lean_object* v_satExpr_2012_; lean_object* v_unusedHypotheses_2013_; lean_object* v_timeout_2014_; lean_object* v_cegarRounds_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v_a_2022_; lean_object* v___x_2025_; lean_object* v_satExpr_2026_; lean_object* v_hypQueue_2027_; lean_object* v_usedHyps_2028_; lean_object* v_theoryState_2029_; lean_object* v_solverTimeBudgetMs_2030_; lean_object* v_roundBudget_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2079_; 
v_lastCex_2008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__0));
v___x_2009_ = 1;
v___x_2010_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic_0__Lean_Meta_Tactic_BVDecide_CegarM_TheoryState_new();
v_config_2011_ = lean_ctor_get(v_ctx_1992_, 5);
v_satExpr_2012_ = lean_ctor_get(v_a_1994_, 0);
v_unusedHypotheses_2013_ = lean_ctor_get(v_a_1994_, 1);
v_timeout_2014_ = lean_ctor_get(v_config_2011_, 0);
v_cegarRounds_2015_ = lean_ctor_get(v_config_2011_, 2);
v___x_2016_ = lean_unsigned_to_nat(1000u);
v___x_2017_ = lean_nat_mul(v_timeout_2014_, v___x_2016_);
lean_inc(v_cegarRounds_2015_);
lean_inc_ref(v_satExpr_2012_);
v___x_2018_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2018_, 0, v_satExpr_2012_);
lean_ctor_set(v___x_2018_, 1, v_lastCex_2008_);
lean_ctor_set(v___x_2018_, 2, v_lastCex_2008_);
lean_ctor_set(v___x_2018_, 3, v___x_2010_);
lean_ctor_set(v___x_2018_, 4, v___x_2017_);
lean_ctor_set(v___x_2018_, 5, v_cegarRounds_2015_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*6, v___x_2009_);
lean_inc_ref(v_unusedHypotheses_2013_);
lean_inc(v_a_1993_);
v___x_2019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2019_, 0, v_a_1993_);
lean_ctor_set(v___x_2019_, 1, v_unusedHypotheses_2013_);
lean_ctor_set(v___x_2019_, 2, v_ctx_1992_);
v___x_2020_ = lean_st_mk_ref(v___x_2018_);
v___x_2025_ = lean_st_ref_take(v___x_2020_);
v_satExpr_2026_ = lean_ctor_get(v___x_2025_, 0);
v_hypQueue_2027_ = lean_ctor_get(v___x_2025_, 1);
v_usedHyps_2028_ = lean_ctor_get(v___x_2025_, 2);
v_theoryState_2029_ = lean_ctor_get(v___x_2025_, 3);
v_solverTimeBudgetMs_2030_ = lean_ctor_get(v___x_2025_, 4);
v_roundBudget_2031_ = lean_ctor_get(v___x_2025_, 5);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2033_ = v___x_2025_;
v_isShared_2034_ = v_isSharedCheck_2079_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_roundBudget_2031_);
lean_inc(v_solverTimeBudgetMs_2030_);
lean_inc(v_theoryState_2029_);
lean_inc(v_usedHyps_2028_);
lean_inc(v_hypQueue_2027_);
lean_inc(v_satExpr_2026_);
lean_dec(v___x_2025_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2079_;
goto v_resetjp_2032_;
}
v___jp_2021_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_st_ref_get(v___x_2020_);
lean_dec(v___x_2020_);
lean_dec(v___x_2023_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_a_2022_);
return v___x_2024_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_satExpr_2026_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_hypQueue_2027_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_usedHyps_2028_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_theoryState_2029_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_solverTimeBudgetMs_2030_);
lean_ctor_set(v_reuseFailAlloc_2078_, 5, v_roundBudget_2031_);
v___x_2036_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*6, v___x_2009_);
v___x_2037_ = lean_st_ref_put(v___x_2020_, v___x_2036_);
v___x_2038_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_configureSolver___redArg(v___x_2019_, v___x_2020_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref_known(v___x_2038_, 1);
v___x_2039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___closed__1));
v___x_2040_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v___x_2039_, v___x_2019_, v___x_2020_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec_ref_known(v___x_2019_, 3);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_fst_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v_fst_2042_ = lean_ctor_get(v_a_2041_, 0);
if (lean_obj_tag(v_fst_2042_) == 0)
{
lean_object* v_snd_2043_; lean_object* v___x_2044_; lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2060_; 
v_snd_2043_ = lean_ctor_get(v_a_2041_, 1);
lean_inc(v_snd_2043_);
lean_dec(v_a_2041_);
v___x_2044_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_mkEquations___redArg(v_snd_2043_);
lean_dec(v_snd_2043_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2060_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2060_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v_theoryState_2050_; lean_object* v_funState_2051_; lean_object* v_atoms_2052_; size_t v_sz_2053_; size_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2049_ = lean_st_ref_get(v_a_1997_);
v_theoryState_2050_ = lean_ctor_get(v___x_2049_, 4);
lean_inc_ref(v_theoryState_2050_);
lean_dec(v___x_2049_);
v_funState_2051_ = lean_ctor_get(v_theoryState_2050_, 0);
lean_inc_ref(v_funState_2051_);
lean_dec_ref(v_theoryState_2050_);
v_atoms_2052_ = lean_ctor_get(v_funState_2051_, 0);
lean_inc_ref(v_atoms_2052_);
lean_dec_ref(v_funState_2051_);
v_sz_2053_ = lean_array_size(v_atoms_2052_);
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__1(v_sz_2053_, v___x_2054_, v_atoms_2052_);
lean_inc_ref(v_unusedHypotheses_2013_);
v___x_2056_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2056_, 0, v_a_1993_);
lean_ctor_set(v___x_2056_, 1, v_unusedHypotheses_2013_);
lean_ctor_set(v___x_2056_, 2, v_a_2045_);
lean_ctor_set(v___x_2056_, 3, v___x_2055_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2056_);
v___x_2058_ = v___x_2047_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
v_a_2022_ = v___x_2058_;
goto v___jp_2021_;
}
}
}
else
{
lean_object* v_val_2061_; 
lean_inc_ref(v_fst_2042_);
lean_dec(v_a_2041_);
lean_dec(v_a_1993_);
v_val_2061_ = lean_ctor_get(v_fst_2042_, 0);
lean_inc(v_val_2061_);
lean_dec_ref_known(v_fst_2042_, 1);
v_a_2022_ = v_val_2061_;
goto v___jp_2021_;
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v___x_2020_);
lean_dec(v_a_1993_);
v_a_2062_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2040_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2040_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v___x_2020_);
lean_dec_ref_known(v___x_2019_, 3);
lean_dec(v_a_1993_);
v_a_2070_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2038_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2038_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop___boxed(lean_object* v_ctx_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(lean_object* v_inst_2097_, lean_object* v_a_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___redArg(v_a_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0___boxed(lean_object** _args){
lean_object* v_inst_2115_ = _args[0];
lean_object* v_a_2116_ = _args[1];
lean_object* v___y_2117_ = _args[2];
lean_object* v___y_2118_ = _args[3];
lean_object* v___y_2119_ = _args[4];
lean_object* v___y_2120_ = _args[5];
lean_object* v___y_2121_ = _args[6];
lean_object* v___y_2122_ = _args[7];
lean_object* v___y_2123_ = _args[8];
lean_object* v___y_2124_ = _args[9];
lean_object* v___y_2125_ = _args[10];
lean_object* v___y_2126_ = _args[11];
lean_object* v___y_2127_ = _args[12];
lean_object* v___y_2128_ = _args[13];
lean_object* v___y_2129_ = _args[14];
lean_object* v___y_2130_ = _args[15];
lean_object* v___y_2131_ = _args[16];
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop_spec__0(v_inst_2115_, v_a_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster(lean_object* v_ctx_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_config_2150_; uint8_t v___x_2151_; 
v_config_2150_ = lean_ctor_get(v_ctx_2134_, 5);
v___x_2151_ = l_Lean_Elab_Tactic_BVDecide_BVDecideConfig_needsIncremental(v_config_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_cegarBlaster___closed__0));
v___x_2153_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed), 16, 1);
lean_closure_set(v___x_2153_, 0, v_ctx_2134_);
v___x_2154_ = l_Lean_Meta_Tactic_BVDecide_UnsatProver_map___redArg(v___x_2152_, v___x_2153_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
return v___x_2154_;
}
else
{
lean_object* v___x_2155_; 
v___x_2155_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_0__Lean_Meta_Tactic_BVDecide_cegarBlaster_cegarLoop(v_ctx_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
lean_dec_ref(v_a_2136_);
return v___x_2155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_cegarBlaster___boxed(lean_object* v_ctx_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Meta_Tactic_BVDecide_cegarBlaster(v_ctx_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
return v_res_2172_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Function(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Epr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Epr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Function(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Epr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Epr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Subsolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar(builtin);
}
#ifdef __cplusplus
}
#endif
