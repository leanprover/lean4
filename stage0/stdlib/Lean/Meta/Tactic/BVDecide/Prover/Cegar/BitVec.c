// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Cegar.BitVec
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic import Lean.Meta.Sym.InferType import Lean.Meta.Tactic.BVDecide.Prover.Bitblast import Lean.Meta.Tactic.BVDecide.External
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_lazyPure___redArg(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Cadical_Solver_val(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Cadical_Solver_solve___boxed(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_IO_sleep(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Cadical_Solver_terminate(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Cadical_Solver_assume(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Cadical_Solver_clause(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toCNF_State_cast___redArg(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toCNF_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_empty___redArg();
lean_object* l_Std_Sat_AIG_toCNF_State_empty___redArg(lean_object*);
lean_object* l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___boxed(lean_object**);
static const lean_array_object l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2;
static lean_once_cell_t l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Converting AIG to CNF"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Running incremental SAT solver"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Bitblasting BVLogicalExpr to AIG"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Checking BitVec abstraction"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -> "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " [label=\""};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\", shape=box];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__4_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__5 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__5_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\", shape=doublecircle];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__6 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__6_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 21, .m_data = " ∧\",shape=trapezium];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__7 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0_value;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Digraph AIG {"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "SAT solver found a counter example."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Error during proof recovery"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CNF has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " clauses, added "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " clauses this round"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__14_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "aig.gv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1___boxed(lean_object*);
static const lean_array_object l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__6_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13_value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "AIG has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " nodes, added "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " nodes this round"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Std_Sat_AIG_empty___redArg();
return v___x_1_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = lean_mk_array(v___x_3_, v___x_2_);
return v___x_4_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__1);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_5_);
return v___x_7_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0);
v___x_9_ = l_Std_Sat_AIG_toCNF_State_empty___redArg(v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__3);
v___x_11_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2);
v___x_12_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__0);
v___x_13_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_11_);
lean_ctor_set(v___x_13_, 2, v___x_10_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg(lean_object* v_a_14_){
_start:
{
lean_object* v___x_16_; lean_object* v_theoryState_17_; lean_object* v_bitvecState_18_; lean_object* v___x_19_; lean_object* v_theoryState_20_; lean_object* v_satExpr_21_; lean_object* v_hypQueue_22_; lean_object* v_usedHyps_23_; uint8_t v_didChange_24_; lean_object* v_solverTimeBudgetMs_25_; lean_object* v_roundBudget_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_47_; 
v___x_16_ = lean_st_ref_get(v_a_14_);
v_theoryState_17_ = lean_ctor_get(v___x_16_, 3);
lean_inc_ref(v_theoryState_17_);
lean_dec(v___x_16_);
v_bitvecState_18_ = lean_ctor_get(v_theoryState_17_, 1);
lean_inc_ref(v_bitvecState_18_);
lean_dec_ref(v_theoryState_17_);
v___x_19_ = lean_st_ref_take(v_a_14_);
v_theoryState_20_ = lean_ctor_get(v___x_19_, 3);
v_satExpr_21_ = lean_ctor_get(v___x_19_, 0);
v_hypQueue_22_ = lean_ctor_get(v___x_19_, 1);
v_usedHyps_23_ = lean_ctor_get(v___x_19_, 2);
v_didChange_24_ = lean_ctor_get_uint8(v___x_19_, sizeof(void*)*6);
v_solverTimeBudgetMs_25_ = lean_ctor_get(v___x_19_, 4);
v_roundBudget_26_ = lean_ctor_get(v___x_19_, 5);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_47_ == 0)
{
v___x_28_ = v___x_19_;
v_isShared_29_ = v_isSharedCheck_47_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_roundBudget_26_);
lean_inc(v_solverTimeBudgetMs_25_);
lean_inc(v_theoryState_20_);
lean_inc(v_usedHyps_23_);
lean_inc(v_hypQueue_22_);
lean_inc(v_satExpr_21_);
lean_dec(v___x_19_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_47_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v_funState_30_; lean_object* v_preprocessCaches_31_; lean_object* v_satSolver_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_45_; 
v_funState_30_ = lean_ctor_get(v_theoryState_20_, 0);
v_preprocessCaches_31_ = lean_ctor_get(v_theoryState_20_, 2);
v_satSolver_32_ = lean_ctor_get(v_theoryState_20_, 3);
v_isSharedCheck_45_ = !lean_is_exclusive(v_theoryState_20_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v_theoryState_20_, 1);
lean_dec(v_unused_46_);
v___x_34_ = v_theoryState_20_;
v_isShared_35_ = v_isSharedCheck_45_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_satSolver_32_);
lean_inc(v_preprocessCaches_31_);
lean_inc(v_funState_30_);
lean_dec(v_theoryState_20_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_45_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_funState_30_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v_preprocessCaches_31_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_satSolver_32_);
v___x_38_ = v_reuseFailAlloc_44_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_40_; 
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 3, v___x_38_);
v___x_40_ = v___x_28_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_satExpr_21_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_hypQueue_22_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v_usedHyps_23_);
lean_ctor_set(v_reuseFailAlloc_43_, 3, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_43_, 4, v_solverTimeBudgetMs_25_);
lean_ctor_set(v_reuseFailAlloc_43_, 5, v_roundBudget_26_);
lean_ctor_set_uint8(v_reuseFailAlloc_43_, sizeof(void*)*6, v_didChange_24_);
v___x_40_ = v_reuseFailAlloc_43_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_st_ref_put(v_a_14_, v___x_40_);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v_bitvecState_18_);
return v___x_42_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___boxed(lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg(v_a_48_);
lean_dec(v_a_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState(lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; lean_object* v_theoryState_67_; lean_object* v_bitvecState_68_; lean_object* v___x_69_; lean_object* v_theoryState_70_; lean_object* v_satExpr_71_; lean_object* v_hypQueue_72_; lean_object* v_usedHyps_73_; uint8_t v_didChange_74_; lean_object* v_solverTimeBudgetMs_75_; lean_object* v_roundBudget_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_97_; 
v___x_66_ = lean_st_ref_get(v_a_52_);
v_theoryState_67_ = lean_ctor_get(v___x_66_, 3);
lean_inc_ref(v_theoryState_67_);
lean_dec(v___x_66_);
v_bitvecState_68_ = lean_ctor_get(v_theoryState_67_, 1);
lean_inc_ref(v_bitvecState_68_);
lean_dec_ref(v_theoryState_67_);
v___x_69_ = lean_st_ref_take(v_a_52_);
v_theoryState_70_ = lean_ctor_get(v___x_69_, 3);
v_satExpr_71_ = lean_ctor_get(v___x_69_, 0);
v_hypQueue_72_ = lean_ctor_get(v___x_69_, 1);
v_usedHyps_73_ = lean_ctor_get(v___x_69_, 2);
v_didChange_74_ = lean_ctor_get_uint8(v___x_69_, sizeof(void*)*6);
v_solverTimeBudgetMs_75_ = lean_ctor_get(v___x_69_, 4);
v_roundBudget_76_ = lean_ctor_get(v___x_69_, 5);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_97_ == 0)
{
v___x_78_ = v___x_69_;
v_isShared_79_ = v_isSharedCheck_97_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_roundBudget_76_);
lean_inc(v_solverTimeBudgetMs_75_);
lean_inc(v_theoryState_70_);
lean_inc(v_usedHyps_73_);
lean_inc(v_hypQueue_72_);
lean_inc(v_satExpr_71_);
lean_dec(v___x_69_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_97_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v_funState_80_; lean_object* v_preprocessCaches_81_; lean_object* v_satSolver_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_95_; 
v_funState_80_ = lean_ctor_get(v_theoryState_70_, 0);
v_preprocessCaches_81_ = lean_ctor_get(v_theoryState_70_, 2);
v_satSolver_82_ = lean_ctor_get(v_theoryState_70_, 3);
v_isSharedCheck_95_ = !lean_is_exclusive(v_theoryState_70_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v_theoryState_70_, 1);
lean_dec(v_unused_96_);
v___x_84_ = v_theoryState_70_;
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_satSolver_82_);
lean_inc(v_preprocessCaches_81_);
lean_inc(v_funState_80_);
lean_dec(v_theoryState_70_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_86_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_funState_80_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_preprocessCaches_81_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v_satSolver_82_);
v___x_88_ = v_reuseFailAlloc_94_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 3, v___x_88_);
v___x_90_ = v___x_78_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_satExpr_71_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_hypQueue_72_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_usedHyps_73_);
lean_ctor_set(v_reuseFailAlloc_93_, 3, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_93_, 4, v_solverTimeBudgetMs_75_);
lean_ctor_set(v_reuseFailAlloc_93_, 5, v_roundBudget_76_);
lean_ctor_set_uint8(v_reuseFailAlloc_93_, sizeof(void*)*6, v_didChange_74_);
v___x_90_ = v_reuseFailAlloc_93_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_st_ref_put(v_a_52_, v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v_bitvecState_68_);
return v___x_92_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___boxed(lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState(v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg(lean_object* v_s_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; lean_object* v_theoryState_118_; lean_object* v_satExpr_119_; lean_object* v_hypQueue_120_; lean_object* v_usedHyps_121_; uint8_t v_didChange_122_; lean_object* v_solverTimeBudgetMs_123_; lean_object* v_roundBudget_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_145_; 
v___x_117_ = lean_st_ref_take(v_a_115_);
v_theoryState_118_ = lean_ctor_get(v___x_117_, 3);
v_satExpr_119_ = lean_ctor_get(v___x_117_, 0);
v_hypQueue_120_ = lean_ctor_get(v___x_117_, 1);
v_usedHyps_121_ = lean_ctor_get(v___x_117_, 2);
v_didChange_122_ = lean_ctor_get_uint8(v___x_117_, sizeof(void*)*6);
v_solverTimeBudgetMs_123_ = lean_ctor_get(v___x_117_, 4);
v_roundBudget_124_ = lean_ctor_get(v___x_117_, 5);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_145_ == 0)
{
v___x_126_ = v___x_117_;
v_isShared_127_ = v_isSharedCheck_145_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_roundBudget_124_);
lean_inc(v_solverTimeBudgetMs_123_);
lean_inc(v_theoryState_118_);
lean_inc(v_usedHyps_121_);
lean_inc(v_hypQueue_120_);
lean_inc(v_satExpr_119_);
lean_dec(v___x_117_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_145_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v_funState_128_; lean_object* v_preprocessCaches_129_; lean_object* v_satSolver_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_143_; 
v_funState_128_ = lean_ctor_get(v_theoryState_118_, 0);
v_preprocessCaches_129_ = lean_ctor_get(v_theoryState_118_, 2);
v_satSolver_130_ = lean_ctor_get(v_theoryState_118_, 3);
v_isSharedCheck_143_ = !lean_is_exclusive(v_theoryState_118_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v_theoryState_118_, 1);
lean_dec(v_unused_144_);
v___x_132_ = v_theoryState_118_;
v_isShared_133_ = v_isSharedCheck_143_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_satSolver_130_);
lean_inc(v_preprocessCaches_129_);
lean_inc(v_funState_128_);
lean_dec(v_theoryState_118_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_143_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = lean_box(0);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_s_114_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_funState_128_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_s_114_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_preprocessCaches_129_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_satSolver_130_);
v___x_136_ = v_reuseFailAlloc_142_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 3, v___x_136_);
v___x_138_ = v___x_126_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_satExpr_119_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_hypQueue_120_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_usedHyps_121_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_solverTimeBudgetMs_123_);
lean_ctor_set(v_reuseFailAlloc_141_, 5, v_roundBudget_124_);
lean_ctor_set_uint8(v_reuseFailAlloc_141_, sizeof(void*)*6, v_didChange_122_);
v___x_138_ = v_reuseFailAlloc_141_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_st_ref_put(v_a_115_, v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_134_);
return v___x_140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg___boxed(lean_object* v_s_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg(v_s_146_, v_a_147_);
lean_dec(v_a_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState(lean_object* v_s_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_theoryState_167_; lean_object* v_satExpr_168_; lean_object* v_hypQueue_169_; lean_object* v_usedHyps_170_; uint8_t v_didChange_171_; lean_object* v_solverTimeBudgetMs_172_; lean_object* v_roundBudget_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_194_; 
v___x_166_ = lean_st_ref_take(v_a_152_);
v_theoryState_167_ = lean_ctor_get(v___x_166_, 3);
v_satExpr_168_ = lean_ctor_get(v___x_166_, 0);
v_hypQueue_169_ = lean_ctor_get(v___x_166_, 1);
v_usedHyps_170_ = lean_ctor_get(v___x_166_, 2);
v_didChange_171_ = lean_ctor_get_uint8(v___x_166_, sizeof(void*)*6);
v_solverTimeBudgetMs_172_ = lean_ctor_get(v___x_166_, 4);
v_roundBudget_173_ = lean_ctor_get(v___x_166_, 5);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_194_ == 0)
{
v___x_175_ = v___x_166_;
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_roundBudget_173_);
lean_inc(v_solverTimeBudgetMs_172_);
lean_inc(v_theoryState_167_);
lean_inc(v_usedHyps_170_);
lean_inc(v_hypQueue_169_);
lean_inc(v_satExpr_168_);
lean_dec(v___x_166_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_funState_177_; lean_object* v_preprocessCaches_178_; lean_object* v_satSolver_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_192_; 
v_funState_177_ = lean_ctor_get(v_theoryState_167_, 0);
v_preprocessCaches_178_ = lean_ctor_get(v_theoryState_167_, 2);
v_satSolver_179_ = lean_ctor_get(v_theoryState_167_, 3);
v_isSharedCheck_192_ = !lean_is_exclusive(v_theoryState_167_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v_theoryState_167_, 1);
lean_dec(v_unused_193_);
v___x_181_ = v_theoryState_167_;
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_satSolver_179_);
lean_inc(v_preprocessCaches_178_);
lean_inc(v_funState_177_);
lean_dec(v_theoryState_167_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_192_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = lean_box(0);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v_s_150_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_funState_177_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_s_150_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_preprocessCaches_178_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_satSolver_179_);
v___x_185_ = v_reuseFailAlloc_191_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_187_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 3, v___x_185_);
v___x_187_ = v___x_175_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_satExpr_168_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_hypQueue_169_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_usedHyps_170_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v_solverTimeBudgetMs_172_);
lean_ctor_set(v_reuseFailAlloc_190_, 5, v_roundBudget_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, sizeof(void*)*6, v_didChange_171_);
v___x_187_ = v_reuseFailAlloc_190_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_st_ref_put(v_a_152_, v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_183_);
return v___x_189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___boxed(lean_object* v_s_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState(v_s_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_b_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_array_217_; lean_object* v_start_218_; lean_object* v_stop_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_247_; 
v_array_217_ = lean_ctor_get(v_a_213_, 0);
v_start_218_ = lean_ctor_get(v_a_213_, 1);
v_stop_219_ = lean_ctor_get(v_a_213_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_a_213_);
if (v_isSharedCheck_247_ == 0)
{
v___x_221_ = v_a_213_;
v_isShared_222_ = v_isSharedCheck_247_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_stop_219_);
lean_inc(v_start_218_);
lean_inc(v_array_217_);
lean_dec(v_a_213_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_247_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; 
v___x_223_ = lean_nat_dec_lt(v_start_218_, v_stop_219_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; 
lean_del_object(v___x_221_);
lean_dec(v_stop_219_);
lean_dec(v_start_218_);
lean_dec_ref(v_array_217_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v_b_214_);
return v___x_224_;
}
else
{
lean_object* v_ref_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v_ref_225_ = lean_ctor_get(v___y_215_, 2);
v___x_226_ = lean_box(0);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_start_218_, v___x_227_);
lean_inc_ref(v_array_217_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_228_);
v___x_230_ = v___x_221_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_array_217_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_stop_219_);
v___x_230_ = v_reuseFailAlloc_246_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_array_fget(v_array_217_, v_start_218_);
lean_dec(v_start_218_);
lean_dec_ref(v_array_217_);
v___x_232_ = l_Lean_Cadical_Solver_clause(v_a_212_, v___x_231_);
lean_dec(v___x_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_dec_ref_known(v___x_232_, 1);
v_a_213_ = v___x_230_;
v_b_214_ = v___x_226_;
goto _start;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v___x_230_);
v_a_234_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_245_ == 0)
{
v___x_236_ = v___x_232_;
v_isShared_237_ = v_isSharedCheck_245_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_245_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_238_ = lean_io_error_to_string(v_a_234_);
v___x_239_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
v___x_240_ = l_Lean_MessageData_ofFormat(v___x_239_);
lean_inc(v_ref_225_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_ref_225_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_241_);
v___x_243_ = v___x_236_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg___boxed(lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_b_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(v_a_248_, v_a_249_, v_b_250_, v___y_251_);
lean_dec_ref(v___y_251_);
lean_dec_ref(v_a_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(lean_object* v_prevCnfSize_254_, lean_object* v_current_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_257_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v_lower_274_; lean_object* v_upper_275_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_array_get_size(v_current_255_);
v___x_289_ = lean_nat_dec_le(v_prevCnfSize_254_, v___x_287_);
if (v___x_289_ == 0)
{
v_lower_274_ = v_prevCnfSize_254_;
v_upper_275_ = v___x_288_;
goto v___jp_273_;
}
else
{
lean_dec(v_prevCnfSize_254_);
v_lower_274_ = v___x_287_;
v_upper_275_ = v___x_288_;
goto v___jp_273_;
}
v___jp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = l_Array_toSubarray___redArg(v_current_255_, v_lower_274_, v_upper_275_);
v___x_277_ = lean_box(0);
v___x_278_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(v_a_272_, v___x_276_, v___x_277_, v_a_268_);
lean_dec(v_a_272_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v___x_278_, 0);
lean_dec(v_unused_286_);
v___x_280_ = v___x_278_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_dec(v___x_278_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_277_);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_277_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
return v___x_278_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_current_255_);
lean_dec(v_prevCnfSize_254_);
v_a_290_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_271_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_271_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf___boxed(lean_object** _args){
lean_object* v_prevCnfSize_298_ = _args[0];
lean_object* v_current_299_ = _args[1];
lean_object* v_a_300_ = _args[2];
lean_object* v_a_301_ = _args[3];
lean_object* v_a_302_ = _args[4];
lean_object* v_a_303_ = _args[5];
lean_object* v_a_304_ = _args[6];
lean_object* v_a_305_ = _args[7];
lean_object* v_a_306_ = _args[8];
lean_object* v_a_307_ = _args[9];
lean_object* v_a_308_ = _args[10];
lean_object* v_a_309_ = _args[11];
lean_object* v_a_310_ = _args[12];
lean_object* v_a_311_ = _args[13];
lean_object* v_a_312_ = _args[14];
lean_object* v_a_313_ = _args[15];
lean_object* v_a_314_ = _args[16];
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v_prevCnfSize_298_, v_current_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
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
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0(lean_object* v_a_316_, lean_object* v_inst_317_, lean_object* v_R_318_, lean_object* v_a_319_, lean_object* v_b_320_, lean_object* v_c_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(v_a_316_, v_a_319_, v_b_320_, v___y_334_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___boxed(lean_object** _args){
lean_object* v_a_338_ = _args[0];
lean_object* v_inst_339_ = _args[1];
lean_object* v_R_340_ = _args[2];
lean_object* v_a_341_ = _args[3];
lean_object* v_b_342_ = _args[4];
lean_object* v_c_343_ = _args[5];
lean_object* v___y_344_ = _args[6];
lean_object* v___y_345_ = _args[7];
lean_object* v___y_346_ = _args[8];
lean_object* v___y_347_ = _args[9];
lean_object* v___y_348_ = _args[10];
lean_object* v___y_349_ = _args[11];
lean_object* v___y_350_ = _args[12];
lean_object* v___y_351_ = _args[13];
lean_object* v___y_352_ = _args[14];
lean_object* v___y_353_ = _args[15];
lean_object* v___y_354_ = _args[16];
lean_object* v___y_355_ = _args[17];
lean_object* v___y_356_ = _args[18];
lean_object* v___y_357_ = _args[19];
lean_object* v___y_358_ = _args[20];
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0(v_a_338_, v_inst_339_, v_R_340_, v_a_341_, v_b_342_, v_c_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec_ref(v_a_338_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(lean_object* v_upperBound_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_b_363_, lean_object* v___y_364_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_nat_dec_lt(v_a_362_, v_upperBound_360_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_b_363_);
return v___x_367_;
}
else
{
lean_object* v_ref_368_; lean_object* v___x_369_; 
v_ref_368_ = lean_ctor_get(v___y_364_, 2);
lean_inc_ref(v_a_361_);
v___x_369_ = l_Lean_Cadical_Solver_val(v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
lean_inc(v_a_362_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_a_370_);
lean_ctor_set(v___x_371_, 1, v_a_362_);
v___x_372_ = lean_array_push(v_b_363_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_a_362_, v___x_373_);
lean_dec(v_a_362_);
v_a_362_ = v___x_374_;
v_b_363_ = v___x_372_;
goto _start;
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v_b_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
v_a_376_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_387_ == 0)
{
v___x_378_ = v___x_369_;
v_isShared_379_ = v_isSharedCheck_387_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_369_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_387_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_380_ = lean_io_error_to_string(v_a_376_);
v___x_381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = l_Lean_MessageData_ofFormat(v___x_381_);
lean_inc(v_ref_368_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_ref_368_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_383_);
v___x_385_ = v___x_378_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg___boxed(lean_object* v_upperBound_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_b_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(v_upperBound_388_, v_a_389_, v_a_390_, v_b_391_, v___y_392_);
lean_dec_ref(v___y_392_);
lean_dec(v_upperBound_388_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(lean_object* v_aigSize_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_397_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = lean_mk_empty_array_with_capacity(v_aigSize_395_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(v_aigSize_395_, v_a_412_, v___x_414_, v___x_413_, v_a_408_);
return v___x_415_;
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_a_416_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_411_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_411_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment___boxed(lean_object* v_aigSize_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v_aigSize_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_aigSize_424_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0(lean_object* v_upperBound_441_, lean_object* v_a_442_, lean_object* v_inst_443_, lean_object* v_R_444_, lean_object* v_a_445_, lean_object* v_b_446_, lean_object* v_c_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(v_upperBound_441_, v_a_442_, v_a_445_, v_b_446_, v___y_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_464_ = _args[0];
lean_object* v_a_465_ = _args[1];
lean_object* v_inst_466_ = _args[2];
lean_object* v_R_467_ = _args[3];
lean_object* v_a_468_ = _args[4];
lean_object* v_b_469_ = _args[5];
lean_object* v_c_470_ = _args[6];
lean_object* v___y_471_ = _args[7];
lean_object* v___y_472_ = _args[8];
lean_object* v___y_473_ = _args[9];
lean_object* v___y_474_ = _args[10];
lean_object* v___y_475_ = _args[11];
lean_object* v___y_476_ = _args[12];
lean_object* v___y_477_ = _args[13];
lean_object* v___y_478_ = _args[14];
lean_object* v___y_479_ = _args[15];
lean_object* v___y_480_ = _args[16];
lean_object* v___y_481_ = _args[17];
lean_object* v___y_482_ = _args[18];
lean_object* v___y_483_ = _args[19];
lean_object* v___y_484_ = _args[20];
lean_object* v___y_485_ = _args[21];
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0(v_upperBound_464_, v_a_465_, v_inst_466_, v_R_467_, v_a_468_, v_b_469_, v_c_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v_upperBound_464_);
return v_res_486_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_box(0);
v___x_488_ = l_Lean_interruptExceptionId;
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg(){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___boxed(lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0(lean_object* v_00_u03b1_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___boxed(lean_object* v_00_u03b1_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0(v_00_u03b1_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(lean_object* v_a_529_, lean_object* v___x_530_, lean_object* v_____r_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
uint32_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v_satExpr_550_; lean_object* v_hypQueue_551_; lean_object* v_usedHyps_552_; uint8_t v_didChange_553_; lean_object* v_theoryState_554_; lean_object* v_solverTimeBudgetMs_555_; lean_object* v_roundBudget_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_572_; 
v___x_547_ = lean_uint32_of_nat(v_a_529_);
v___x_548_ = l_IO_sleep(v___x_547_);
v___x_549_ = lean_st_ref_take(v___y_533_);
v_satExpr_550_ = lean_ctor_get(v___x_549_, 0);
v_hypQueue_551_ = lean_ctor_get(v___x_549_, 1);
v_usedHyps_552_ = lean_ctor_get(v___x_549_, 2);
v_didChange_553_ = lean_ctor_get_uint8(v___x_549_, sizeof(void*)*6);
v_theoryState_554_ = lean_ctor_get(v___x_549_, 3);
v_solverTimeBudgetMs_555_ = lean_ctor_get(v___x_549_, 4);
v_roundBudget_556_ = lean_ctor_get(v___x_549_, 5);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_572_ == 0)
{
v___x_558_ = v___x_549_;
v_isShared_559_ = v_isSharedCheck_572_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_roundBudget_556_);
lean_inc(v_solverTimeBudgetMs_555_);
lean_inc(v_theoryState_554_);
lean_inc(v_usedHyps_552_);
lean_inc(v_hypQueue_551_);
lean_inc(v_satExpr_550_);
lean_dec(v___x_549_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_572_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_nat_sub(v_solverTimeBudgetMs_555_, v_a_529_);
lean_dec(v_solverTimeBudgetMs_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 4, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_satExpr_550_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_hypQueue_551_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_usedHyps_552_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_theoryState_554_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 5, v_roundBudget_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*6, v_didChange_553_);
v___x_562_ = v_reuseFailAlloc_571_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___y_565_; uint8_t v___x_568_; 
v___x_563_ = lean_st_ref_put(v___y_533_, v___x_562_);
v___x_568_ = lean_nat_dec_le(v___x_530_, v_a_529_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(2u);
v___x_570_ = lean_nat_mul(v_a_529_, v___x_569_);
lean_dec(v_a_529_);
v___y_565_ = v___x_570_;
goto v___jp_564_;
}
else
{
v___y_565_ = v_a_529_;
goto v___jp_564_;
}
v___jp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___y_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_573_ = _args[0];
lean_object* v___x_574_ = _args[1];
lean_object* v_____r_575_ = _args[2];
lean_object* v___y_576_ = _args[3];
lean_object* v___y_577_ = _args[4];
lean_object* v___y_578_ = _args[5];
lean_object* v___y_579_ = _args[6];
lean_object* v___y_580_ = _args[7];
lean_object* v___y_581_ = _args[8];
lean_object* v___y_582_ = _args[9];
lean_object* v___y_583_ = _args[10];
lean_object* v___y_584_ = _args[11];
lean_object* v___y_585_ = _args[12];
lean_object* v___y_586_ = _args[13];
lean_object* v___y_587_ = _args[14];
lean_object* v___y_588_ = _args[15];
lean_object* v___y_589_ = _args[16];
lean_object* v___y_590_ = _args[17];
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_573_, v___x_574_, v_____r_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___x_574_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(lean_object* v_val_592_, lean_object* v_solver_593_, lean_object* v_a_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___y_611_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_631_ = lean_unsigned_to_nat(64u);
v___x_632_ = lean_io_get_task_state(v_val_592_);
v___x_633_ = lean_box(v___x_632_);
v___x_634_ = lean_obj_tag_nat(v___x_633_);
lean_dec(v___x_633_);
v___x_635_ = lean_unsigned_to_nat(2u);
v___x_636_ = lean_nat_dec_eq(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v_solverTimeBudgetMs_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_637_ = lean_st_ref_get(v___y_596_);
v_solverTimeBudgetMs_638_ = lean_ctor_get(v___x_637_, 4);
lean_inc(v_solverTimeBudgetMs_638_);
lean_dec(v___x_637_);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_nat_dec_eq(v_solverTimeBudgetMs_638_, v___x_639_);
lean_dec(v_solverTimeBudgetMs_638_);
if (v___x_640_ == 0)
{
lean_object* v_toCold_641_; lean_object* v_cancelTk_x3f_642_; 
v_toCold_641_ = lean_ctor_get(v___y_607_, 0);
v_cancelTk_x3f_642_ = lean_ctor_get(v_toCold_641_, 10);
if (lean_obj_tag(v_cancelTk_x3f_642_) == 1)
{
lean_object* v_val_643_; uint8_t v___x_644_; 
v_val_643_ = lean_ctor_get(v_cancelTk_x3f_642_, 0);
v___x_644_ = l_IO_CancelToken_isSet(v_val_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_594_, v___x_631_, v___x_645_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
v___y_611_ = v___x_646_;
goto v___jp_610_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = l_Lean_Cadical_Solver_terminate(v_solver_593_);
v___x_648_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v___x_650_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_594_, v___x_631_, v_a_649_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
v___y_611_ = v___x_650_;
goto v___jp_610_;
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_a_594_);
v_a_651_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_648_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_648_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_box(0);
v___x_660_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_594_, v___x_631_, v___x_659_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
v___y_611_ = v___x_660_;
goto v___jp_610_;
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = l_Lean_Cadical_Solver_terminate(v_solver_593_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v_a_594_);
return v___x_662_;
}
}
else
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v_a_594_);
return v___x_663_;
}
v___jp_610_:
{
if (lean_obj_tag(v___y_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_622_; 
v_a_612_ = lean_ctor_get(v___y_611_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___y_611_);
if (v_isSharedCheck_622_ == 0)
{
v___x_614_ = v___y_611_;
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___y_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
if (lean_obj_tag(v_a_612_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; 
v_a_616_ = lean_ctor_get(v_a_612_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v_a_612_, 1);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v_a_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v_a_620_; 
lean_del_object(v___x_614_);
v_a_620_ = lean_ctor_get(v_a_612_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v_a_612_, 1);
v_a_594_ = v_a_620_;
goto _start;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_623_ = lean_ctor_get(v___y_611_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___y_611_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___y_611_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___y_611_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_val_664_ = _args[0];
lean_object* v_solver_665_ = _args[1];
lean_object* v_a_666_ = _args[2];
lean_object* v___y_667_ = _args[3];
lean_object* v___y_668_ = _args[4];
lean_object* v___y_669_ = _args[5];
lean_object* v___y_670_ = _args[6];
lean_object* v___y_671_ = _args[7];
lean_object* v___y_672_ = _args[8];
lean_object* v___y_673_ = _args[9];
lean_object* v___y_674_ = _args[10];
lean_object* v___y_675_ = _args[11];
lean_object* v___y_676_ = _args[12];
lean_object* v___y_677_ = _args[13];
lean_object* v___y_678_ = _args[14];
lean_object* v___y_679_ = _args[15];
lean_object* v___y_680_ = _args[16];
lean_object* v___y_681_ = _args[17];
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v_val_664_, v_solver_665_, v_a_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_solver_665_);
lean_dec_ref(v_val_664_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(lean_object* v_solver_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_inc_ref(v_solver_683_);
v___x_699_ = lean_alloc_closure((void*)(l_Lean_Cadical_Solver_solve___boxed), 2, 1);
lean_closure_set(v___x_699_, 0, v_solver_683_);
v___x_700_ = lean_unsigned_to_nat(9u);
v___x_701_ = lean_io_as_task(v___x_699_, v___x_700_);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v___x_701_, v_solver_683_, v___x_702_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec_ref(v_solver_683_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; 
v_unused_712_ = lean_ctor_get(v___x_703_, 0);
lean_dec(v_unused_712_);
v___x_705_ = v___x_703_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_dec(v___x_703_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_task_get_own(v___x_701_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v___x_701_);
v_a_713_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_703_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_703_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver___boxed(lean_object* v_solver_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v_solver_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1(lean_object* v_val_738_, lean_object* v_solver_739_, lean_object* v_inst_740_, lean_object* v_a_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v_val_738_, v_solver_739_, v_a_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___boxed(lean_object** _args){
lean_object* v_val_758_ = _args[0];
lean_object* v_solver_759_ = _args[1];
lean_object* v_inst_760_ = _args[2];
lean_object* v_a_761_ = _args[3];
lean_object* v___y_762_ = _args[4];
lean_object* v___y_763_ = _args[5];
lean_object* v___y_764_ = _args[6];
lean_object* v___y_765_ = _args[7];
lean_object* v___y_766_ = _args[8];
lean_object* v___y_767_ = _args[9];
lean_object* v___y_768_ = _args[10];
lean_object* v___y_769_ = _args[11];
lean_object* v___y_770_ = _args[12];
lean_object* v___y_771_ = _args[13];
lean_object* v___y_772_ = _args[14];
lean_object* v___y_773_ = _args[15];
lean_object* v___y_774_ = _args[16];
lean_object* v___y_775_ = _args[17];
lean_object* v___y_776_ = _args[18];
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1(v_val_758_, v_solver_759_, v_inst_760_, v_a_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec_ref(v_solver_759_);
lean_dec_ref(v_val_758_);
return v_res_777_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_box(0);
v___x_783_ = lean_unsigned_to_nat(16u);
v___x_784_ = lean_mk_array(v___x_783_, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
return v___x_787_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2);
v___x_789_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__0));
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
return v___x_790_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0(void){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3);
return v___x_791_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = lean_unsigned_to_nat(32u);
v___x_793_ = lean_mk_empty_array_with_capacity(v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_795_ = ((size_t)5ULL);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_unsigned_to_nat(32u);
v___x_798_ = lean_mk_empty_array_with_capacity(v___x_797_);
v___x_799_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0);
v___x_800_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___x_798_);
lean_ctor_set(v___x_800_, 2, v___x_796_);
lean_ctor_set(v___x_800_, 3, v___x_796_);
lean_ctor_set_usize(v___x_800_, 4, v___x_795_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v_traceState_804_; lean_object* v_traces_805_; lean_object* v___x_806_; lean_object* v_traceState_807_; lean_object* v_env_808_; lean_object* v_nextMacroScope_809_; lean_object* v_ngen_810_; lean_object* v_auxDeclNGen_811_; lean_object* v_cache_812_; lean_object* v_recordedDeps_813_; lean_object* v_messages_814_; lean_object* v_infoState_815_; lean_object* v_snapshotTasks_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_835_; 
v___x_803_ = lean_st_ref_get(v___y_801_);
v_traceState_804_ = lean_ctor_get(v___x_803_, 4);
lean_inc_ref(v_traceState_804_);
lean_dec(v___x_803_);
v_traces_805_ = lean_ctor_get(v_traceState_804_, 0);
lean_inc_ref(v_traces_805_);
lean_dec_ref(v_traceState_804_);
v___x_806_ = lean_st_ref_take(v___y_801_);
v_traceState_807_ = lean_ctor_get(v___x_806_, 4);
v_env_808_ = lean_ctor_get(v___x_806_, 0);
v_nextMacroScope_809_ = lean_ctor_get(v___x_806_, 1);
v_ngen_810_ = lean_ctor_get(v___x_806_, 2);
v_auxDeclNGen_811_ = lean_ctor_get(v___x_806_, 3);
v_cache_812_ = lean_ctor_get(v___x_806_, 5);
v_recordedDeps_813_ = lean_ctor_get(v___x_806_, 6);
v_messages_814_ = lean_ctor_get(v___x_806_, 7);
v_infoState_815_ = lean_ctor_get(v___x_806_, 8);
v_snapshotTasks_816_ = lean_ctor_get(v___x_806_, 9);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_835_ == 0)
{
v___x_818_ = v___x_806_;
v_isShared_819_ = v_isSharedCheck_835_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_snapshotTasks_816_);
lean_inc(v_infoState_815_);
lean_inc(v_messages_814_);
lean_inc(v_recordedDeps_813_);
lean_inc(v_cache_812_);
lean_inc(v_traceState_807_);
lean_inc(v_auxDeclNGen_811_);
lean_inc(v_ngen_810_);
lean_inc(v_nextMacroScope_809_);
lean_inc(v_env_808_);
lean_dec(v___x_806_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_835_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
uint64_t v_tid_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_833_; 
v_tid_820_ = lean_ctor_get_uint64(v_traceState_807_, sizeof(void*)*1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_traceState_807_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v_traceState_807_, 0);
lean_dec(v_unused_834_);
v___x_822_ = v_traceState_807_;
v_isShared_823_ = v_isSharedCheck_833_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_traceState_807_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_833_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_824_);
lean_ctor_set_uint64(v_reuseFailAlloc_832_, sizeof(void*)*1, v_tid_820_);
v___x_826_ = v_reuseFailAlloc_832_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 4, v___x_826_);
v___x_828_ = v___x_818_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_env_808_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_nextMacroScope_809_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_ngen_810_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_auxDeclNGen_811_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_831_, 5, v_cache_812_);
lean_ctor_set(v_reuseFailAlloc_831_, 6, v_recordedDeps_813_);
lean_ctor_set(v_reuseFailAlloc_831_, 7, v_messages_814_);
lean_ctor_set(v_reuseFailAlloc_831_, 8, v_infoState_815_);
lean_ctor_set(v_reuseFailAlloc_831_, 9, v_snapshotTasks_816_);
v___x_828_ = v_reuseFailAlloc_831_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_st_ref_put(v___y_801_, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_traces_805_);
return v___x_830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___boxed(lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_836_);
lean_dec(v___y_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4(lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___boxed(lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4(v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(lean_object* v_opts_871_, lean_object* v_opt_872_){
_start:
{
lean_object* v_name_873_; lean_object* v_defValue_874_; lean_object* v_map_875_; lean_object* v___x_876_; 
v_name_873_ = lean_ctor_get(v_opt_872_, 0);
v_defValue_874_ = lean_ctor_get(v_opt_872_, 1);
v_map_875_ = lean_ctor_get(v_opts_871_, 0);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_875_, v_name_873_);
if (lean_obj_tag(v___x_876_) == 0)
{
uint8_t v___x_877_; 
v___x_877_ = lean_unbox(v_defValue_874_);
return v___x_877_;
}
else
{
lean_object* v_val_878_; 
v_val_878_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v___x_876_, 1);
if (lean_obj_tag(v_val_878_) == 1)
{
uint8_t v_v_879_; 
v_v_879_ = lean_ctor_get_uint8(v_val_878_, 0);
lean_dec_ref_known(v_val_878_, 0);
return v_v_879_;
}
else
{
uint8_t v___x_880_; 
lean_dec(v_val_878_);
v___x_880_ = lean_unbox(v_defValue_874_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5___boxed(lean_object* v_opts_881_, lean_object* v_opt_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_881_, v_opt_882_);
lean_dec_ref(v_opt_882_);
lean_dec_ref(v_opts_881_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__1));
v___x_889_ = l_Lean_MessageData_ofFormat(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0(lean_object* v_x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___boxed(lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0(v_x_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec_ref(v_x_908_);
return v_res_924_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__0));
v___x_927_ = l_Lean_stringToMessageData(v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1(lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___boxed(lean_object* v_x_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1(v_x_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v_x_946_);
return v_res_962_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__1));
v___x_967_ = l_Lean_MessageData_ofFormat(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2(lean_object* v_x_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___boxed(lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2(v_x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v_x_986_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3(lean_object* v___x_1003_, lean_object* v___x_1004_, lean_object* v_result_1005_, lean_object* v___x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1003_, v___x_1004_, v_result_1005_, v___x_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed(lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v_result_1011_, lean_object* v___x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3(v___x_1009_, v___x_1010_, v_result_1011_, v___x_1012_, v_x_1013_);
lean_dec_ref(v___x_1010_);
lean_dec_ref(v___x_1009_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(lean_object* v___f_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_ref_1028_; lean_object* v___x_1029_; 
v_ref_1028_ = lean_ctor_get(v___y_1025_, 2);
v___x_1029_ = l_IO_lazyPure___redArg(v___f_1015_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
v_a_1038_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1040_ = v___x_1029_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1029_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1042_ = lean_io_error_to_string(v_a_1038_);
v___x_1043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
v___x_1044_ = l_Lean_MessageData_ofFormat(v___x_1043_);
lean_inc(v_ref_1028_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_ref_1028_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1045_);
v___x_1047_ = v___x_1040_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4___boxed(lean_object* v___f_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5(lean_object* v_aig_1064_, lean_object* v_bvExpr_1065_, lean_object* v_blastCache_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_1064_, v_bvExpr_1065_, v_blastCache_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(lean_object* v___f_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_ref_1082_; lean_object* v___x_1083_; 
v_ref_1082_ = lean_ctor_get(v___y_1079_, 2);
v___x_1083_ = l_IO_lazyPure___redArg(v___f_1069_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
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
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1103_; 
v_a_1092_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1094_ = v___x_1083_;
v_isShared_1095_ = v_isSharedCheck_1103_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1083_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1103_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1096_ = lean_io_error_to_string(v_a_1092_);
v___x_1097_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
v___x_1098_ = l_Lean_MessageData_ofFormat(v___x_1097_);
lean_inc(v_ref_1082_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_ref_1082_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1099_);
v___x_1101_ = v___x_1094_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6___boxed(lean_object* v___f_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1117_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__0));
v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7(lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___boxed(lean_object* v_x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7(v_x_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec_ref(v_x_1139_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(lean_object* v_x_1156_){
_start:
{
if (lean_obj_tag(v_x_1156_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v_x_1156_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1156_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v_x_1156_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v_x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 1);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v_x_1156_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_x_1156_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v_x_1156_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v_x_1156_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 0);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg___boxed(lean_object* v_x_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_x_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(lean_object* v_e_1177_){
_start:
{
if (lean_obj_tag(v_e_1177_) == 0)
{
uint8_t v___x_1178_; 
v___x_1178_ = 2;
return v___x_1178_;
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = 0;
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10___boxed(lean_object* v_e_1180_){
_start:
{
uint8_t v_res_1181_; lean_object* v_r_1182_; 
v_res_1181_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(v_e_1180_);
lean_dec_ref(v_e_1180_);
v_r_1182_ = lean_box(v_res_1181_);
return v_r_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(lean_object* v_msgData_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_env_1190_; uint8_t v___x_1191_; lean_object* v_env_1192_; lean_object* v___x_1193_; lean_object* v_toCold_1194_; lean_object* v_mctx_1195_; lean_object* v_lctx_1196_; lean_object* v_options_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1189_ = lean_st_ref_get(v___y_1187_);
v_env_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref(v_env_1190_);
lean_dec(v___x_1189_);
v___x_1191_ = 0;
v_env_1192_ = l_Lean_Environment_setRecordingDeps(v_env_1190_, v___x_1191_);
v___x_1193_ = lean_st_ref_get(v___y_1185_);
v_toCold_1194_ = lean_ctor_get(v___y_1186_, 0);
v_mctx_1195_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_ref(v_mctx_1195_);
lean_dec(v___x_1193_);
v_lctx_1196_ = lean_ctor_get(v___y_1184_, 2);
v_options_1197_ = lean_ctor_get(v_toCold_1194_, 2);
lean_inc_ref(v_options_1197_);
lean_inc_ref(v_lctx_1196_);
v___x_1198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1198_, 0, v_env_1192_);
lean_ctor_set(v___x_1198_, 1, v_mctx_1195_);
lean_ctor_set(v___x_1198_, 2, v_lctx_1196_);
lean_ctor_set(v___x_1198_, 3, v_options_1197_);
v___x_1199_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_msgData_1183_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3___boxed(lean_object* v_msgData_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msgData_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(size_t v_sz_1208_, size_t v_i_1209_, lean_object* v_bs_1210_){
_start:
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_usize_dec_lt(v_i_1209_, v_sz_1208_);
if (v___x_1211_ == 0)
{
return v_bs_1210_;
}
else
{
lean_object* v_v_1212_; lean_object* v_msg_1213_; lean_object* v___x_1214_; lean_object* v_bs_x27_1215_; size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v_v_1212_ = lean_array_uget_borrowed(v_bs_1210_, v_i_1209_);
v_msg_1213_ = lean_ctor_get(v_v_1212_, 1);
lean_inc_ref(v_msg_1213_);
v___x_1214_ = lean_unsigned_to_nat(0u);
v_bs_x27_1215_ = lean_array_uset(v_bs_1210_, v_i_1209_, v___x_1214_);
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_add(v_i_1209_, v___x_1216_);
v___x_1218_ = lean_array_uset(v_bs_x27_1215_, v_i_1209_, v_msg_1213_);
v_i_1209_ = v___x_1217_;
v_bs_1210_ = v___x_1218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_1220_, lean_object* v_i_1221_, lean_object* v_bs_1222_){
_start:
{
size_t v_sz_boxed_1223_; size_t v_i_boxed_1224_; lean_object* v_res_1225_; 
v_sz_boxed_1223_ = lean_unbox_usize(v_sz_1220_);
lean_dec(v_sz_1220_);
v_i_boxed_1224_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(v_sz_boxed_1223_, v_i_boxed_1224_, v_bs_1222_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(lean_object* v_oldTraces_1226_, lean_object* v_data_1227_, lean_object* v_ref_1228_, lean_object* v_msg_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_toCold_1235_; lean_object* v_currRecDepth_1236_; lean_object* v_ref_1237_; uint16_t v_optionFlags_1238_; uint8_t v_suppressElabErrors_1239_; uint8_t v_isRecordingDeps_1240_; lean_object* v_ref_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_traceState_1244_; lean_object* v_traces_1245_; lean_object* v___x_1246_; size_t v_sz_1247_; size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v_msg_1250_; lean_object* v___x_1251_; lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1290_; 
v_toCold_1235_ = lean_ctor_get(v___y_1232_, 0);
v_currRecDepth_1236_ = lean_ctor_get(v___y_1232_, 1);
v_ref_1237_ = lean_ctor_get(v___y_1232_, 2);
v_optionFlags_1238_ = lean_ctor_get_uint16(v___y_1232_, sizeof(void*)*3);
v_suppressElabErrors_1239_ = lean_ctor_get_uint8(v___y_1232_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1240_ = lean_ctor_get_uint8(v___y_1232_, sizeof(void*)*3 + 3);
v_ref_1241_ = l_Lean_replaceRef(v_ref_1228_, v_ref_1237_);
lean_inc(v_currRecDepth_1236_);
lean_inc_ref(v_toCold_1235_);
v___x_1242_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1242_, 0, v_toCold_1235_);
lean_ctor_set(v___x_1242_, 1, v_currRecDepth_1236_);
lean_ctor_set(v___x_1242_, 2, v_ref_1241_);
lean_ctor_set_uint16(v___x_1242_, sizeof(void*)*3, v_optionFlags_1238_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*3 + 2, v_suppressElabErrors_1239_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*3 + 3, v_isRecordingDeps_1240_);
v___x_1243_ = lean_st_ref_get(v___y_1233_);
v_traceState_1244_ = lean_ctor_get(v___x_1243_, 4);
lean_inc_ref(v_traceState_1244_);
lean_dec(v___x_1243_);
v_traces_1245_ = lean_ctor_get(v_traceState_1244_, 0);
lean_inc_ref(v_traces_1245_);
lean_dec_ref(v_traceState_1244_);
v___x_1246_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1245_);
lean_dec_ref(v_traces_1245_);
v_sz_1247_ = lean_array_size(v___x_1246_);
v___x_1248_ = ((size_t)0ULL);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(v_sz_1247_, v___x_1248_, v___x_1246_);
v_msg_1250_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1250_, 0, v_data_1227_);
lean_ctor_set(v_msg_1250_, 1, v_msg_1229_);
lean_ctor_set(v_msg_1250_, 2, v___x_1249_);
v___x_1251_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1250_, v___y_1230_, v___y_1231_, v___x_1242_, v___y_1233_);
lean_dec_ref_known(v___x_1242_, 3);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1290_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1290_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v_traceState_1257_; lean_object* v_env_1258_; lean_object* v_nextMacroScope_1259_; lean_object* v_ngen_1260_; lean_object* v_auxDeclNGen_1261_; lean_object* v_cache_1262_; lean_object* v_recordedDeps_1263_; lean_object* v_messages_1264_; lean_object* v_infoState_1265_; lean_object* v_snapshotTasks_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1289_; 
v___x_1256_ = lean_st_ref_take(v___y_1233_);
v_traceState_1257_ = lean_ctor_get(v___x_1256_, 4);
v_env_1258_ = lean_ctor_get(v___x_1256_, 0);
v_nextMacroScope_1259_ = lean_ctor_get(v___x_1256_, 1);
v_ngen_1260_ = lean_ctor_get(v___x_1256_, 2);
v_auxDeclNGen_1261_ = lean_ctor_get(v___x_1256_, 3);
v_cache_1262_ = lean_ctor_get(v___x_1256_, 5);
v_recordedDeps_1263_ = lean_ctor_get(v___x_1256_, 6);
v_messages_1264_ = lean_ctor_get(v___x_1256_, 7);
v_infoState_1265_ = lean_ctor_get(v___x_1256_, 8);
v_snapshotTasks_1266_ = lean_ctor_get(v___x_1256_, 9);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1268_ = v___x_1256_;
v_isShared_1269_ = v_isSharedCheck_1289_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snapshotTasks_1266_);
lean_inc(v_infoState_1265_);
lean_inc(v_messages_1264_);
lean_inc(v_recordedDeps_1263_);
lean_inc(v_cache_1262_);
lean_inc(v_traceState_1257_);
lean_inc(v_auxDeclNGen_1261_);
lean_inc(v_ngen_1260_);
lean_inc(v_nextMacroScope_1259_);
lean_inc(v_env_1258_);
lean_dec(v___x_1256_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1289_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
uint64_t v_tid_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1287_; 
v_tid_1270_ = lean_ctor_get_uint64(v_traceState_1257_, sizeof(void*)*1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_traceState_1257_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v_traceState_1257_, 0);
lean_dec(v_unused_1288_);
v___x_1272_ = v_traceState_1257_;
v_isShared_1273_ = v_isSharedCheck_1287_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v_traceState_1257_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1287_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_ref_1228_);
lean_ctor_set(v___x_1275_, 1, v_a_1252_);
v___x_1276_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1226_, v___x_1275_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1276_);
v___x_1278_ = v___x_1272_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1276_);
lean_ctor_set_uint64(v_reuseFailAlloc_1286_, sizeof(void*)*1, v_tid_1270_);
v___x_1278_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v___x_1278_);
v___x_1280_ = v___x_1268_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_env_1258_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_nextMacroScope_1259_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_ngen_1260_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_auxDeclNGen_1261_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1285_, 5, v_cache_1262_);
lean_ctor_set(v_reuseFailAlloc_1285_, 6, v_recordedDeps_1263_);
lean_ctor_set(v_reuseFailAlloc_1285_, 7, v_messages_1264_);
lean_ctor_set(v_reuseFailAlloc_1285_, 8, v_infoState_1265_);
lean_ctor_set(v_reuseFailAlloc_1285_, 9, v_snapshotTasks_1266_);
v___x_1280_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_st_ref_put(v___y_1233_, v___x_1280_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1274_);
v___x_1283_ = v___x_1254_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1274_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg___boxed(lean_object* v_oldTraces_1291_, lean_object* v_data_1292_, lean_object* v_ref_1293_, lean_object* v_msg_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1291_, v_data_1292_, v_ref_1293_, v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(lean_object* v_opts_1301_, lean_object* v_opt_1302_){
_start:
{
lean_object* v_name_1303_; lean_object* v_defValue_1304_; lean_object* v_map_1305_; lean_object* v___x_1306_; 
v_name_1303_ = lean_ctor_get(v_opt_1302_, 0);
v_defValue_1304_ = lean_ctor_get(v_opt_1302_, 1);
v_map_1305_ = lean_ctor_get(v_opts_1301_, 0);
v___x_1306_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1305_, v_name_1303_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_inc(v_defValue_1304_);
return v_defValue_1304_;
}
else
{
lean_object* v_val_1307_; 
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v___x_1306_, 1);
if (lean_obj_tag(v_val_1307_) == 3)
{
lean_object* v_v_1308_; 
v_v_1308_ = lean_ctor_get(v_val_1307_, 0);
lean_inc(v_v_1308_);
lean_dec_ref_known(v_val_1307_, 1);
return v_v_1308_;
}
else
{
lean_dec(v_val_1307_);
lean_inc(v_defValue_1304_);
return v_defValue_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11___boxed(lean_object* v_opts_1309_, lean_object* v_opt_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1309_, v_opt_1310_);
lean_dec_ref(v_opt_1310_);
lean_dec_ref(v_opts_1309_);
return v_res_1311_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1312_; double v___x_1313_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = lean_float_of_nat(v___x_1312_);
return v___x_1313_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__1));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1317_; double v___x_1318_; 
v___x_1317_ = lean_unsigned_to_nat(1000u);
v___x_1318_ = lean_float_of_nat(v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(lean_object* v_cls_1319_, uint8_t v_collapsed_1320_, lean_object* v_tag_1321_, lean_object* v_opts_1322_, uint8_t v_clsEnabled_1323_, lean_object* v_oldTraces_1324_, lean_object* v_msg_1325_, lean_object* v_resStartStop_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_fst_1342_; lean_object* v_snd_1343_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v_data_1347_; lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; lean_object* v___y_1363_; lean_object* v_a_1364_; uint8_t v___y_1379_; double v___y_1411_; 
v_fst_1342_ = lean_ctor_get(v_resStartStop_1326_, 0);
lean_inc(v_fst_1342_);
v_snd_1343_ = lean_ctor_get(v_resStartStop_1326_, 1);
lean_inc(v_snd_1343_);
lean_dec_ref(v_resStartStop_1326_);
v_fst_1358_ = lean_ctor_get(v_snd_1343_, 0);
lean_inc(v_fst_1358_);
v_snd_1359_ = lean_ctor_get(v_snd_1343_, 1);
lean_inc(v_snd_1359_);
lean_dec(v_snd_1343_);
v___x_1360_ = l_Lean_trace_profiler;
v___x_1361_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1322_, v___x_1360_);
if (v___x_1361_ == 0)
{
v___y_1379_ = v___x_1361_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1417_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1322_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; double v___x_1420_; double v___x_1421_; double v___x_1422_; 
v___x_1418_ = l_Lean_trace_profiler_threshold;
v___x_1419_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1322_, v___x_1418_);
v___x_1420_ = lean_float_of_nat(v___x_1419_);
v___x_1421_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_1422_ = lean_float_div(v___x_1420_, v___x_1421_);
v___y_1411_ = v___x_1422_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; double v___x_1425_; 
v___x_1423_ = l_Lean_trace_profiler_threshold;
v___x_1424_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1322_, v___x_1423_);
v___x_1425_ = lean_float_of_nat(v___x_1424_);
v___y_1411_ = v___x_1425_;
goto v___jp_1410_;
}
}
v___jp_1344_:
{
lean_object* v___x_1348_; 
lean_inc(v___y_1346_);
v___x_1348_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1324_, v_data_1347_, v___y_1346_, v___y_1345_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; 
lean_dec_ref_known(v___x_1348_, 1);
v___x_1349_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1342_);
return v___x_1349_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_fst_1342_);
v_a_1350_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1348_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
v___jp_1362_:
{
uint8_t v_result_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; double v___x_1368_; lean_object* v_data_1369_; 
v_result_1365_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(v_fst_1342_);
v___x_1366_ = lean_box(v_result_1365_);
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
v___x_1368_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_1321_);
lean_inc_ref(v___x_1367_);
lean_inc(v_cls_1319_);
v_data_1369_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1369_, 0, v_cls_1319_);
lean_ctor_set(v_data_1369_, 1, v___x_1367_);
lean_ctor_set(v_data_1369_, 2, v_tag_1321_);
lean_ctor_set_float(v_data_1369_, sizeof(void*)*3, v___x_1368_);
lean_ctor_set_float(v_data_1369_, sizeof(void*)*3 + 8, v___x_1368_);
lean_ctor_set_uint8(v_data_1369_, sizeof(void*)*3 + 16, v_collapsed_1320_);
if (v___x_1361_ == 0)
{
lean_dec_ref_known(v___x_1367_, 1);
lean_dec(v_snd_1359_);
lean_dec(v_fst_1358_);
lean_dec_ref(v_tag_1321_);
lean_dec(v_cls_1319_);
v___y_1345_ = v_a_1364_;
v___y_1346_ = v___y_1363_;
v_data_1347_ = v_data_1369_;
goto v___jp_1344_;
}
else
{
lean_object* v_data_1370_; double v___x_1371_; double v___x_1372_; 
lean_dec_ref_known(v_data_1369_, 3);
v_data_1370_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1370_, 0, v_cls_1319_);
lean_ctor_set(v_data_1370_, 1, v___x_1367_);
lean_ctor_set(v_data_1370_, 2, v_tag_1321_);
v___x_1371_ = lean_unbox_float(v_fst_1358_);
lean_dec(v_fst_1358_);
lean_ctor_set_float(v_data_1370_, sizeof(void*)*3, v___x_1371_);
v___x_1372_ = lean_unbox_float(v_snd_1359_);
lean_dec(v_snd_1359_);
lean_ctor_set_float(v_data_1370_, sizeof(void*)*3 + 8, v___x_1372_);
lean_ctor_set_uint8(v_data_1370_, sizeof(void*)*3 + 16, v_collapsed_1320_);
v___y_1345_ = v_a_1364_;
v___y_1346_ = v___y_1363_;
v_data_1347_ = v_data_1370_;
goto v___jp_1344_;
}
}
v___jp_1373_:
{
lean_object* v_ref_1374_; lean_object* v___x_1375_; 
v_ref_1374_ = lean_ctor_get(v___y_1339_, 2);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v_fst_1342_);
v___x_1375_ = lean_apply_16(v_msg_1325_, v_fst_1342_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, lean_box(0));
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___y_1363_ = v_ref_1374_;
v_a_1364_ = v_a_1376_;
goto v___jp_1362_;
}
else
{
lean_object* v___x_1377_; 
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_1363_ = v_ref_1374_;
v_a_1364_ = v___x_1377_;
goto v___jp_1362_;
}
}
v___jp_1378_:
{
if (v_clsEnabled_1323_ == 0)
{
if (v___y_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v_traceState_1381_; lean_object* v_env_1382_; lean_object* v_nextMacroScope_1383_; lean_object* v_ngen_1384_; lean_object* v_auxDeclNGen_1385_; lean_object* v_cache_1386_; lean_object* v_recordedDeps_1387_; lean_object* v_messages_1388_; lean_object* v_infoState_1389_; lean_object* v_snapshotTasks_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1409_; 
lean_dec(v_snd_1359_);
lean_dec(v_fst_1358_);
lean_dec_ref(v_msg_1325_);
lean_dec_ref(v_tag_1321_);
lean_dec(v_cls_1319_);
v___x_1380_ = lean_st_ref_take(v___y_1340_);
v_traceState_1381_ = lean_ctor_get(v___x_1380_, 4);
v_env_1382_ = lean_ctor_get(v___x_1380_, 0);
v_nextMacroScope_1383_ = lean_ctor_get(v___x_1380_, 1);
v_ngen_1384_ = lean_ctor_get(v___x_1380_, 2);
v_auxDeclNGen_1385_ = lean_ctor_get(v___x_1380_, 3);
v_cache_1386_ = lean_ctor_get(v___x_1380_, 5);
v_recordedDeps_1387_ = lean_ctor_get(v___x_1380_, 6);
v_messages_1388_ = lean_ctor_get(v___x_1380_, 7);
v_infoState_1389_ = lean_ctor_get(v___x_1380_, 8);
v_snapshotTasks_1390_ = lean_ctor_get(v___x_1380_, 9);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1392_ = v___x_1380_;
v_isShared_1393_ = v_isSharedCheck_1409_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snapshotTasks_1390_);
lean_inc(v_infoState_1389_);
lean_inc(v_messages_1388_);
lean_inc(v_recordedDeps_1387_);
lean_inc(v_cache_1386_);
lean_inc(v_traceState_1381_);
lean_inc(v_auxDeclNGen_1385_);
lean_inc(v_ngen_1384_);
lean_inc(v_nextMacroScope_1383_);
lean_inc(v_env_1382_);
lean_dec(v___x_1380_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1409_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
uint64_t v_tid_1394_; lean_object* v_traces_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1408_; 
v_tid_1394_ = lean_ctor_get_uint64(v_traceState_1381_, sizeof(void*)*1);
v_traces_1395_ = lean_ctor_get(v_traceState_1381_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_traceState_1381_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1397_ = v_traceState_1381_;
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_traces_1395_);
lean_dec(v_traceState_1381_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1324_, v_traces_1395_);
lean_dec_ref(v_traces_1395_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1399_);
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1399_);
lean_ctor_set_uint64(v_reuseFailAlloc_1407_, sizeof(void*)*1, v_tid_1394_);
v___x_1401_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1401_);
v___x_1403_ = v___x_1392_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_env_1382_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_nextMacroScope_1383_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_ngen_1384_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_auxDeclNGen_1385_);
lean_ctor_set(v_reuseFailAlloc_1406_, 4, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1406_, 5, v_cache_1386_);
lean_ctor_set(v_reuseFailAlloc_1406_, 6, v_recordedDeps_1387_);
lean_ctor_set(v_reuseFailAlloc_1406_, 7, v_messages_1388_);
lean_ctor_set(v_reuseFailAlloc_1406_, 8, v_infoState_1389_);
lean_ctor_set(v_reuseFailAlloc_1406_, 9, v_snapshotTasks_1390_);
v___x_1403_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_st_ref_put(v___y_1340_, v___x_1403_);
v___x_1405_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1342_);
return v___x_1405_;
}
}
}
}
}
else
{
goto v___jp_1373_;
}
}
else
{
goto v___jp_1373_;
}
}
v___jp_1410_:
{
double v___x_1412_; double v___x_1413_; double v___x_1414_; uint8_t v___x_1415_; 
v___x_1412_ = lean_unbox_float(v_snd_1359_);
v___x_1413_ = lean_unbox_float(v_fst_1358_);
v___x_1414_ = lean_float_sub(v___x_1412_, v___x_1413_);
v___x_1415_ = lean_float_decLt(v___y_1411_, v___x_1414_);
v___y_1379_ = v___x_1415_;
goto v___jp_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___boxed(lean_object** _args){
lean_object* v_cls_1426_ = _args[0];
lean_object* v_collapsed_1427_ = _args[1];
lean_object* v_tag_1428_ = _args[2];
lean_object* v_opts_1429_ = _args[3];
lean_object* v_clsEnabled_1430_ = _args[4];
lean_object* v_oldTraces_1431_ = _args[5];
lean_object* v_msg_1432_ = _args[6];
lean_object* v_resStartStop_1433_ = _args[7];
lean_object* v___y_1434_ = _args[8];
lean_object* v___y_1435_ = _args[9];
lean_object* v___y_1436_ = _args[10];
lean_object* v___y_1437_ = _args[11];
lean_object* v___y_1438_ = _args[12];
lean_object* v___y_1439_ = _args[13];
lean_object* v___y_1440_ = _args[14];
lean_object* v___y_1441_ = _args[15];
lean_object* v___y_1442_ = _args[16];
lean_object* v___y_1443_ = _args[17];
lean_object* v___y_1444_ = _args[18];
lean_object* v___y_1445_ = _args[19];
lean_object* v___y_1446_ = _args[20];
lean_object* v___y_1447_ = _args[21];
lean_object* v___y_1448_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_1449_; uint8_t v_clsEnabled_boxed_1450_; lean_object* v_res_1451_; 
v_collapsed_boxed_1449_ = lean_unbox(v_collapsed_1427_);
v_clsEnabled_boxed_1450_ = lean_unbox(v_clsEnabled_1430_);
v_res_1451_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v_cls_1426_, v_collapsed_boxed_1449_, v_tag_1428_, v_opts_1429_, v_clsEnabled_boxed_1450_, v_oldTraces_1431_, v_msg_1432_, v_resStartStop_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec_ref(v_opts_1429_);
return v_res_1451_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(lean_object* v_a_1452_, lean_object* v_x_1453_){
_start:
{
if (lean_obj_tag(v_x_1453_) == 0)
{
uint8_t v___x_1454_; 
v___x_1454_ = 0;
return v___x_1454_;
}
else
{
lean_object* v_key_1455_; lean_object* v_tail_1456_; uint8_t v___x_1457_; 
v_key_1455_ = lean_ctor_get(v_x_1453_, 0);
v_tail_1456_ = lean_ctor_get(v_x_1453_, 2);
v___x_1457_ = lean_nat_dec_eq(v_key_1455_, v_a_1452_);
if (v___x_1457_ == 0)
{
v_x_1453_ = v_tail_1456_;
goto _start;
}
else
{
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg___boxed(lean_object* v_a_1459_, lean_object* v_x_1460_){
_start:
{
uint8_t v_res_1461_; lean_object* v_r_1462_; 
v_res_1461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1459_, v_x_1460_);
lean_dec(v_x_1460_);
lean_dec(v_a_1459_);
v_r_1462_ = lean_box(v_res_1461_);
return v_r_1462_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(lean_object* v___x_1463_, lean_object* v_m_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_buckets_1466_; lean_object* v___x_1467_; uint64_t v___x_1468_; uint64_t v___x_1469_; uint64_t v___x_1470_; uint64_t v_fold_1471_; uint64_t v___x_1472_; uint64_t v___x_1473_; uint64_t v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v_buckets_1466_ = lean_ctor_get(v_m_1464_, 1);
v___x_1467_ = lean_array_get_size(v_buckets_1466_);
v___x_1468_ = lean_uint64_of_nat(v_a_1465_);
v___x_1469_ = 32ULL;
v___x_1470_ = lean_uint64_shift_right(v___x_1468_, v___x_1469_);
v_fold_1471_ = lean_uint64_xor(v___x_1468_, v___x_1470_);
v___x_1472_ = 16ULL;
v___x_1473_ = lean_uint64_shift_right(v_fold_1471_, v___x_1472_);
v___x_1474_ = lean_uint64_xor(v_fold_1471_, v___x_1473_);
v___x_1475_ = lean_uint64_to_usize(v___x_1474_);
v___x_1476_ = lean_usize_of_nat(v___x_1467_);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_sub(v___x_1476_, v___x_1477_);
v___x_1479_ = lean_usize_land(v___x_1475_, v___x_1478_);
v___x_1480_ = lean_array_uget_borrowed(v_buckets_1466_, v___x_1479_);
v___x_1481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1465_, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg___boxed(lean_object* v___x_1482_, lean_object* v_m_1483_, lean_object* v_a_1484_){
_start:
{
uint8_t v_res_1485_; lean_object* v_r_1486_; 
v_res_1485_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_1482_, v_m_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_m_1483_);
lean_dec(v___x_1482_);
v_r_1486_ = lean_box(v_res_1485_);
return v_r_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
if (lean_obj_tag(v_x_1488_) == 0)
{
return v_x_1487_;
}
else
{
lean_object* v_key_1489_; lean_object* v_value_1490_; lean_object* v_tail_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1514_; 
v_key_1489_ = lean_ctor_get(v_x_1488_, 0);
v_value_1490_ = lean_ctor_get(v_x_1488_, 1);
v_tail_1491_ = lean_ctor_get(v_x_1488_, 2);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_x_1488_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1493_ = v_x_1488_;
v_isShared_1494_ = v_isSharedCheck_1514_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_tail_1491_);
lean_inc(v_value_1490_);
lean_inc(v_key_1489_);
lean_dec(v_x_1488_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1514_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; uint64_t v___x_1496_; uint64_t v___x_1497_; uint64_t v___x_1498_; uint64_t v_fold_1499_; uint64_t v___x_1500_; uint64_t v___x_1501_; uint64_t v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1495_ = lean_array_get_size(v_x_1487_);
v___x_1496_ = lean_uint64_of_nat(v_key_1489_);
v___x_1497_ = 32ULL;
v___x_1498_ = lean_uint64_shift_right(v___x_1496_, v___x_1497_);
v_fold_1499_ = lean_uint64_xor(v___x_1496_, v___x_1498_);
v___x_1500_ = 16ULL;
v___x_1501_ = lean_uint64_shift_right(v_fold_1499_, v___x_1500_);
v___x_1502_ = lean_uint64_xor(v_fold_1499_, v___x_1501_);
v___x_1503_ = lean_uint64_to_usize(v___x_1502_);
v___x_1504_ = lean_usize_of_nat(v___x_1495_);
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_sub(v___x_1504_, v___x_1505_);
v___x_1507_ = lean_usize_land(v___x_1503_, v___x_1506_);
v___x_1508_ = lean_array_uget_borrowed(v_x_1487_, v___x_1507_);
lean_inc(v___x_1508_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 2, v___x_1508_);
v___x_1510_ = v___x_1493_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_key_1489_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_value_1490_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_array_uset(v_x_1487_, v___x_1507_, v___x_1510_);
v_x_1487_ = v___x_1511_;
v_x_1488_ = v_tail_1491_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(lean_object* v_i_1515_, lean_object* v_source_1516_, lean_object* v_target_1517_){
_start:
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1518_ = lean_array_get_size(v_source_1516_);
v___x_1519_ = lean_nat_dec_lt(v_i_1515_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_dec_ref(v_source_1516_);
lean_dec(v_i_1515_);
return v_target_1517_;
}
else
{
lean_object* v_es_1520_; lean_object* v___x_1521_; lean_object* v_source_1522_; lean_object* v_target_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_es_1520_ = lean_array_fget(v_source_1516_, v_i_1515_);
v___x_1521_ = lean_box(0);
v_source_1522_ = lean_array_fset(v_source_1516_, v_i_1515_, v___x_1521_);
v_target_1523_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(v_target_1517_, v_es_1520_);
v___x_1524_ = lean_unsigned_to_nat(1u);
v___x_1525_ = lean_nat_add(v_i_1515_, v___x_1524_);
lean_dec(v_i_1515_);
v_i_1515_ = v___x_1525_;
v_source_1516_ = v_source_1522_;
v_target_1517_ = v_target_1523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(lean_object* v___x_1527_, lean_object* v_data_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_nbuckets_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1529_ = lean_array_get_size(v_data_1528_);
v___x_1530_ = lean_unsigned_to_nat(2u);
v_nbuckets_1531_ = lean_nat_mul(v___x_1529_, v___x_1530_);
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = lean_box(0);
v___x_1534_ = lean_mk_array(v_nbuckets_1531_, v___x_1533_);
v___x_1535_ = lean_array_propagate_mark(v_data_1528_, v___x_1534_);
v___x_1536_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(v___x_1532_, v_data_1528_, v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg___boxed(lean_object* v___x_1537_, lean_object* v_data_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_1537_, v_data_1538_);
lean_dec(v___x_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(lean_object* v___x_1540_, lean_object* v_m_1541_, lean_object* v_a_1542_, lean_object* v_b_1543_){
_start:
{
lean_object* v_size_1544_; lean_object* v_buckets_1545_; lean_object* v___x_1546_; uint64_t v___x_1547_; uint64_t v___x_1548_; uint64_t v___x_1549_; uint64_t v_fold_1550_; uint64_t v___x_1551_; uint64_t v___x_1552_; uint64_t v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; lean_object* v_bkt_1559_; uint8_t v___x_1560_; 
v_size_1544_ = lean_ctor_get(v_m_1541_, 0);
v_buckets_1545_ = lean_ctor_get(v_m_1541_, 1);
v___x_1546_ = lean_array_get_size(v_buckets_1545_);
v___x_1547_ = lean_uint64_of_nat(v_a_1542_);
v___x_1548_ = 32ULL;
v___x_1549_ = lean_uint64_shift_right(v___x_1547_, v___x_1548_);
v_fold_1550_ = lean_uint64_xor(v___x_1547_, v___x_1549_);
v___x_1551_ = 16ULL;
v___x_1552_ = lean_uint64_shift_right(v_fold_1550_, v___x_1551_);
v___x_1553_ = lean_uint64_xor(v_fold_1550_, v___x_1552_);
v___x_1554_ = lean_uint64_to_usize(v___x_1553_);
v___x_1555_ = lean_usize_of_nat(v___x_1546_);
v___x_1556_ = ((size_t)1ULL);
v___x_1557_ = lean_usize_sub(v___x_1555_, v___x_1556_);
v___x_1558_ = lean_usize_land(v___x_1554_, v___x_1557_);
v_bkt_1559_ = lean_array_uget_borrowed(v_buckets_1545_, v___x_1558_);
v___x_1560_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1542_, v_bkt_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1581_; 
lean_inc_ref(v_buckets_1545_);
lean_inc(v_size_1544_);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_m_1541_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; lean_object* v_unused_1583_; 
v_unused_1582_ = lean_ctor_get(v_m_1541_, 1);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_m_1541_, 0);
lean_dec(v_unused_1583_);
v___x_1562_ = v_m_1541_;
v_isShared_1563_ = v_isSharedCheck_1581_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_m_1541_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1581_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v_size_x27_1565_; lean_object* v___x_1566_; lean_object* v_buckets_x27_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v_size_x27_1565_ = lean_nat_add(v_size_1544_, v___x_1564_);
lean_dec(v_size_1544_);
lean_inc(v_bkt_1559_);
v___x_1566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1566_, 0, v_a_1542_);
lean_ctor_set(v___x_1566_, 1, v_b_1543_);
lean_ctor_set(v___x_1566_, 2, v_bkt_1559_);
v_buckets_x27_1567_ = lean_array_uset(v_buckets_1545_, v___x_1558_, v___x_1566_);
v___x_1568_ = lean_unsigned_to_nat(4u);
v___x_1569_ = lean_nat_mul(v_size_x27_1565_, v___x_1568_);
v___x_1570_ = lean_unsigned_to_nat(3u);
v___x_1571_ = lean_nat_div(v___x_1569_, v___x_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_array_get_size(v_buckets_x27_1567_);
v___x_1573_ = lean_nat_dec_le(v___x_1571_, v___x_1572_);
lean_dec(v___x_1571_);
if (v___x_1573_ == 0)
{
lean_object* v_val_1574_; lean_object* v___x_1576_; 
v_val_1574_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_1540_, v_buckets_x27_1567_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v_val_1574_);
lean_ctor_set(v___x_1562_, 0, v_size_x27_1565_);
v___x_1576_ = v___x_1562_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_size_x27_1565_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_val_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
else
{
lean_object* v___x_1579_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v_buckets_x27_1567_);
lean_ctor_set(v___x_1562_, 0, v_size_x27_1565_);
v___x_1579_ = v___x_1562_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_size_x27_1565_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_buckets_x27_1567_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_dec(v_b_1543_);
lean_dec(v_a_1542_);
return v_m_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg___boxed(lean_object* v___x_1584_, lean_object* v_m_1585_, lean_object* v_a_1586_, lean_object* v_b_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_1584_, v_m_1585_, v_a_1586_, v_b_1587_);
lean_dec(v___x_1584_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(lean_object* v_acc_1592_, lean_object* v_decls_1593_, lean_object* v_idx_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = lean_array_get_size(v_decls_1593_);
v___x_1597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_1596_, v_a_1595_, v_idx_1594_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_box(0);
lean_inc(v_idx_1594_);
v___x_1599_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_1596_, v_a_1595_, v_idx_1594_, v___x_1598_);
v___x_1600_ = lean_array_fget_borrowed(v_decls_1593_, v_idx_1594_);
if (lean_obj_tag(v___x_1600_) == 2)
{
lean_object* v_l_1601_; lean_object* v_r_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; uint8_t v___y_1632_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_l_1601_ = lean_ctor_get(v___x_1600_, 0);
v_r_1602_ = lean_ctor_get(v___x_1600_, 1);
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_nat_shiftr(v_l_1601_, v___x_1603_);
v___x_1638_ = lean_nat_land(v___x_1603_, v_l_1601_);
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_nat_dec_eq(v___x_1638_, v___x_1639_);
lean_dec(v___x_1638_);
if (v___x_1640_ == 0)
{
uint8_t v___x_1641_; 
v___x_1641_ = 1;
v___y_1632_ = v___x_1641_;
goto v___jp_1631_;
}
else
{
v___y_1632_ = v___x_1597_;
goto v___jp_1631_;
}
v___jp_1605_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; 
v___x_1609_ = l_Nat_reprFast(v_idx_1594_);
v___x_1610_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__0));
lean_inc_ref(v___x_1609_);
v___x_1611_ = lean_string_append(v___x_1609_, v___x_1610_);
lean_inc(v___x_1604_);
v___x_1612_ = l_Nat_reprFast(v___x_1604_);
v___x_1613_ = lean_string_append(v___x_1611_, v___x_1612_);
lean_dec_ref(v___x_1612_);
v___x_1614_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1606_);
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__1));
v___x_1617_ = lean_string_append(v___x_1615_, v___x_1616_);
v___x_1618_ = lean_string_append(v___x_1617_, v___x_1609_);
lean_dec_ref(v___x_1609_);
v___x_1619_ = lean_string_append(v___x_1618_, v___x_1610_);
lean_inc(v___y_1607_);
v___x_1620_ = l_Nat_reprFast(v___y_1607_);
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1608_);
v___x_1623_ = lean_string_append(v___x_1621_, v___x_1622_);
lean_dec_ref(v___x_1622_);
v___x_1624_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__2));
v___x_1625_ = lean_string_append(v___x_1623_, v___x_1624_);
v___x_1626_ = lean_string_append(v_acc_1592_, v___x_1625_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v___x_1626_, v_decls_1593_, v___x_1604_, v___x_1599_);
v_fst_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_fst_1628_);
v_snd_1629_ = lean_ctor_get(v___x_1627_, 1);
lean_inc(v_snd_1629_);
lean_dec_ref(v___x_1627_);
v_acc_1592_ = v_fst_1628_;
v_idx_1594_ = v___y_1607_;
v_a_1595_ = v_snd_1629_;
goto _start;
}
v___jp_1631_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1633_ = lean_nat_shiftr(v_r_1602_, v___x_1603_);
v___x_1634_ = lean_nat_land(v___x_1603_, v_r_1602_);
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = lean_nat_dec_eq(v___x_1634_, v___x_1635_);
lean_dec(v___x_1634_);
if (v___x_1636_ == 0)
{
uint8_t v___x_1637_; 
v___x_1637_ = 1;
v___y_1606_ = v___y_1632_;
v___y_1607_ = v___x_1633_;
v___y_1608_ = v___x_1637_;
goto v___jp_1605_;
}
else
{
v___y_1606_ = v___y_1632_;
v___y_1607_ = v___x_1633_;
v___y_1608_ = v___x_1597_;
goto v___jp_1605_;
}
}
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_idx_1594_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_acc_1592_);
lean_ctor_set(v___x_1642_, 1, v___x_1599_);
return v___x_1642_;
}
}
else
{
lean_object* v___x_1643_; 
lean_dec(v_idx_1594_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_acc_1592_);
lean_ctor_set(v___x_1643_, 1, v_a_1595_);
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___boxed(lean_object* v_acc_1644_, lean_object* v_decls_1645_, lean_object* v_idx_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v_acc_1644_, v_decls_1645_, v_idx_1646_, v_a_1647_);
lean_dec_ref(v_decls_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(lean_object* v_decls_1657_, lean_object* v_idx_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_array_fget_borrowed(v_decls_1657_, v_idx_1658_);
switch(lean_obj_tag(v___x_1659_))
{
case 0:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1660_ = l_Nat_reprFast(v_idx_1658_);
v___x_1661_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
v___x_1662_ = lean_string_append(v___x_1660_, v___x_1661_);
v___x_1663_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__1));
v___x_1664_ = lean_string_append(v___x_1662_, v___x_1663_);
v___x_1665_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__2));
v___x_1666_ = lean_string_append(v___x_1664_, v___x_1665_);
return v___x_1666_;
}
case 1:
{
lean_object* v_idx_1667_; lean_object* v_var_1668_; lean_object* v_idx_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_idx_1667_ = lean_ctor_get(v___x_1659_, 0);
v_var_1668_ = lean_ctor_get(v_idx_1667_, 0);
v_idx_1669_ = lean_ctor_get(v_idx_1667_, 2);
v___x_1670_ = l_Nat_reprFast(v_idx_1658_);
v___x_1671_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
v___x_1672_ = lean_string_append(v___x_1670_, v___x_1671_);
v___x_1673_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__3));
lean_inc(v_var_1668_);
v___x_1674_ = l_Nat_reprFast(v_var_1668_);
v___x_1675_ = lean_string_append(v___x_1673_, v___x_1674_);
lean_dec_ref(v___x_1674_);
v___x_1676_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__4));
v___x_1677_ = lean_string_append(v___x_1675_, v___x_1676_);
lean_inc(v_idx_1669_);
v___x_1678_ = l_Nat_reprFast(v_idx_1669_);
v___x_1679_ = lean_string_append(v___x_1677_, v___x_1678_);
lean_dec_ref(v___x_1678_);
v___x_1680_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__5));
v___x_1681_ = lean_string_append(v___x_1679_, v___x_1680_);
v___x_1682_ = lean_string_append(v___x_1672_, v___x_1681_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__6));
v___x_1684_ = lean_string_append(v___x_1682_, v___x_1683_);
return v___x_1684_;
}
default: 
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1685_ = l_Nat_reprFast(v_idx_1658_);
v___x_1686_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
lean_inc_ref(v___x_1685_);
v___x_1687_ = lean_string_append(v___x_1685_, v___x_1686_);
v___x_1688_ = lean_string_append(v___x_1687_, v___x_1685_);
lean_dec_ref(v___x_1685_);
v___x_1689_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__7));
v___x_1690_ = lean_string_append(v___x_1688_, v___x_1689_);
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___boxed(lean_object* v_decls_1691_, lean_object* v_idx_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(v_decls_1691_, v_idx_1692_);
lean_dec_ref(v_decls_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(lean_object* v_decls_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
return v_x_1695_;
}
else
{
lean_object* v_key_1697_; lean_object* v_tail_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_key_1697_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_key_1697_);
v_tail_1698_ = lean_ctor_get(v_x_1696_, 2);
lean_inc(v_tail_1698_);
lean_dec_ref_known(v_x_1696_, 3);
v___x_1699_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(v_decls_1694_, v_key_1697_);
v___x_1700_ = lean_string_append(v_x_1695_, v___x_1699_);
lean_dec_ref(v___x_1699_);
v_x_1695_ = v___x_1700_;
v_x_1696_ = v_tail_1698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17___boxed(lean_object* v_decls_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(v_decls_1702_, v_x_1703_, v_x_1704_);
lean_dec_ref(v_decls_1702_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(lean_object* v_decls_1706_, lean_object* v_as_1707_, size_t v_i_1708_, size_t v_stop_1709_, lean_object* v_b_1710_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_usize_dec_eq(v_i_1708_, v_stop_1709_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; size_t v___x_1714_; size_t v___x_1715_; 
v___x_1712_ = lean_array_uget_borrowed(v_as_1707_, v_i_1708_);
lean_inc(v___x_1712_);
v___x_1713_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(v_decls_1706_, v_b_1710_, v___x_1712_);
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = lean_usize_add(v_i_1708_, v___x_1714_);
v_i_1708_ = v___x_1715_;
v_b_1710_ = v___x_1713_;
goto _start;
}
else
{
return v_b_1710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18___boxed(lean_object* v_decls_1717_, lean_object* v_as_1718_, lean_object* v_i_1719_, lean_object* v_stop_1720_, lean_object* v_b_1721_){
_start:
{
size_t v_i_boxed_1722_; size_t v_stop_boxed_1723_; lean_object* v_res_1724_; 
v_i_boxed_1722_ = lean_unbox_usize(v_i_1719_);
lean_dec(v_i_1719_);
v_stop_boxed_1723_ = lean_unbox_usize(v_stop_1720_);
lean_dec(v_stop_1720_);
v_res_1724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(v_decls_1717_, v_as_1718_, v_i_boxed_1722_, v_stop_boxed_1723_, v_b_1721_);
lean_dec_ref(v_as_1718_);
lean_dec_ref(v_decls_1717_);
return v_res_1724_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_unsigned_to_nat(16u);
v___x_1728_ = lean_mk_array(v___x_1727_, v___x_1726_);
return v___x_1728_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v___x_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(lean_object* v_entry_1734_){
_start:
{
lean_object* v_aig_1735_; lean_object* v_ref_1736_; lean_object* v_decls_1737_; lean_object* v_gate_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v_fst_1743_; lean_object* v_snd_1744_; lean_object* v___y_1746_; lean_object* v_buckets_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_aig_1735_ = lean_ctor_get(v_entry_1734_, 0);
lean_inc_ref(v_aig_1735_);
v_ref_1736_ = lean_ctor_get(v_entry_1734_, 1);
lean_inc_ref(v_ref_1736_);
lean_dec_ref(v_entry_1734_);
v_decls_1737_ = lean_ctor_get(v_aig_1735_, 0);
lean_inc_ref(v_decls_1737_);
lean_dec_ref(v_aig_1735_);
v_gate_1738_ = lean_ctor_get(v_ref_1736_, 0);
lean_inc(v_gate_1738_);
lean_dec_ref(v_ref_1736_);
v___x_1739_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2);
v___x_1742_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v___x_1739_, v_decls_1737_, v_gate_1738_, v___x_1741_);
v_fst_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_fst_1743_);
v_snd_1744_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_snd_1744_);
lean_dec_ref(v___x_1742_);
v_buckets_1752_ = lean_ctor_get(v_snd_1744_, 1);
lean_inc_ref(v_buckets_1752_);
lean_dec(v_snd_1744_);
v___x_1753_ = lean_array_get_size(v_buckets_1752_);
v___x_1754_ = lean_nat_dec_lt(v___x_1740_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec_ref(v_buckets_1752_);
lean_dec_ref(v_decls_1737_);
v___y_1746_ = v___x_1739_;
goto v___jp_1745_;
}
else
{
size_t v___x_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = lean_usize_of_nat(v___x_1753_);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(v_decls_1737_, v_buckets_1752_, v___x_1755_, v___x_1756_, v___x_1739_);
lean_dec_ref(v_buckets_1752_);
lean_dec_ref(v_decls_1737_);
v___y_1746_ = v___x_1757_;
goto v___jp_1745_;
}
v___jp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1747_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__3));
v___x_1748_ = lean_string_append(v___x_1747_, v___y_1746_);
lean_dec_ref(v___y_1746_);
v___x_1749_ = lean_string_append(v___x_1748_, v_fst_1743_);
lean_dec(v_fst_1743_);
v___x_1750_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__4));
v___x_1751_ = lean_string_append(v___x_1749_, v___x_1750_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(lean_object* v_cls_1760_, lean_object* v_msg_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_ref_1767_; lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1814_; 
v_ref_1767_ = lean_ctor_get(v___y_1764_, 2);
v___x_1768_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1814_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1814_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v_traceState_1774_; lean_object* v_env_1775_; lean_object* v_nextMacroScope_1776_; lean_object* v_ngen_1777_; lean_object* v_auxDeclNGen_1778_; lean_object* v_cache_1779_; lean_object* v_recordedDeps_1780_; lean_object* v_messages_1781_; lean_object* v_infoState_1782_; lean_object* v_snapshotTasks_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1813_; 
v___x_1773_ = lean_st_ref_take(v___y_1765_);
v_traceState_1774_ = lean_ctor_get(v___x_1773_, 4);
v_env_1775_ = lean_ctor_get(v___x_1773_, 0);
v_nextMacroScope_1776_ = lean_ctor_get(v___x_1773_, 1);
v_ngen_1777_ = lean_ctor_get(v___x_1773_, 2);
v_auxDeclNGen_1778_ = lean_ctor_get(v___x_1773_, 3);
v_cache_1779_ = lean_ctor_get(v___x_1773_, 5);
v_recordedDeps_1780_ = lean_ctor_get(v___x_1773_, 6);
v_messages_1781_ = lean_ctor_get(v___x_1773_, 7);
v_infoState_1782_ = lean_ctor_get(v___x_1773_, 8);
v_snapshotTasks_1783_ = lean_ctor_get(v___x_1773_, 9);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1785_ = v___x_1773_;
v_isShared_1786_ = v_isSharedCheck_1813_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_snapshotTasks_1783_);
lean_inc(v_infoState_1782_);
lean_inc(v_messages_1781_);
lean_inc(v_recordedDeps_1780_);
lean_inc(v_cache_1779_);
lean_inc(v_traceState_1774_);
lean_inc(v_auxDeclNGen_1778_);
lean_inc(v_ngen_1777_);
lean_inc(v_nextMacroScope_1776_);
lean_inc(v_env_1775_);
lean_dec(v___x_1773_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1813_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
uint64_t v_tid_1787_; lean_object* v_traces_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1812_; 
v_tid_1787_ = lean_ctor_get_uint64(v_traceState_1774_, sizeof(void*)*1);
v_traces_1788_ = lean_ctor_get(v_traceState_1774_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_traceState_1774_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1790_ = v_traceState_1774_;
v_isShared_1791_ = v_isSharedCheck_1812_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_traces_1788_);
lean_dec(v_traceState_1774_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1812_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; double v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
v___x_1795_ = 0;
v___x_1796_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_1797_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1797_, 0, v_cls_1760_);
lean_ctor_set(v___x_1797_, 1, v___x_1793_);
lean_ctor_set(v___x_1797_, 2, v___x_1796_);
lean_ctor_set_float(v___x_1797_, sizeof(void*)*3, v___x_1794_);
lean_ctor_set_float(v___x_1797_, sizeof(void*)*3 + 8, v___x_1794_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*3 + 16, v___x_1795_);
v___x_1798_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___closed__0));
v___x_1799_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v_a_1769_);
lean_ctor_set(v___x_1799_, 2, v___x_1798_);
lean_inc(v_ref_1767_);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v_ref_1767_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = l_Lean_PersistentArray_push___redArg(v_traces_1788_, v___x_1800_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1801_);
v___x_1803_ = v___x_1790_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1801_);
lean_ctor_set_uint64(v_reuseFailAlloc_1811_, sizeof(void*)*1, v_tid_1787_);
v___x_1803_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1805_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 4, v___x_1803_);
v___x_1805_ = v___x_1785_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_env_1775_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_nextMacroScope_1776_);
lean_ctor_set(v_reuseFailAlloc_1810_, 2, v_ngen_1777_);
lean_ctor_set(v_reuseFailAlloc_1810_, 3, v_auxDeclNGen_1778_);
lean_ctor_set(v_reuseFailAlloc_1810_, 4, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1810_, 5, v_cache_1779_);
lean_ctor_set(v_reuseFailAlloc_1810_, 6, v_recordedDeps_1780_);
lean_ctor_set(v_reuseFailAlloc_1810_, 7, v_messages_1781_);
lean_ctor_set(v_reuseFailAlloc_1810_, 8, v_infoState_1782_);
lean_ctor_set(v_reuseFailAlloc_1810_, 9, v_snapshotTasks_1783_);
v___x_1805_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = lean_st_ref_put(v___y_1765_, v___x_1805_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1792_);
v___x_1808_ = v___x_1771_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1792_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___boxed(lean_object* v_cls_1815_, lean_object* v_msg_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_1815_, v_msg_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(lean_object* v_msg_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_ref_1829_; lean_object* v___x_1830_; lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1839_; 
v_ref_1829_ = lean_ctor_get(v___y_1826_, 2);
v___x_1830_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
lean_inc(v_ref_1829_);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_ref_1829_);
lean_ctor_set(v___x_1835_, 1, v_a_1831_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set_tag(v___x_1833_, 1);
lean_ctor_set(v___x_1833_, 0, v___x_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg___boxed(lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v_msg_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
return v_res_1846_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(lean_object* v_e_1847_){
_start:
{
if (lean_obj_tag(v_e_1847_) == 0)
{
uint8_t v___x_1848_; 
v___x_1848_ = 2;
return v___x_1848_;
}
else
{
uint8_t v___x_1849_; 
v___x_1849_ = 0;
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13___boxed(lean_object* v_e_1850_){
_start:
{
uint8_t v_res_1851_; lean_object* v_r_1852_; 
v_res_1851_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(v_e_1850_);
lean_dec_ref(v_e_1850_);
v_r_1852_ = lean_box(v_res_1851_);
return v_r_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(lean_object* v_cls_1853_, uint8_t v_collapsed_1854_, lean_object* v_tag_1855_, lean_object* v_opts_1856_, uint8_t v_clsEnabled_1857_, lean_object* v_oldTraces_1858_, lean_object* v_msg_1859_, lean_object* v_resStartStop_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_fst_1876_; lean_object* v_snd_1877_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v_data_1881_; lean_object* v_fst_1892_; lean_object* v_snd_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___y_1897_; lean_object* v_a_1898_; uint8_t v___y_1913_; double v___y_1945_; 
v_fst_1876_ = lean_ctor_get(v_resStartStop_1860_, 0);
lean_inc(v_fst_1876_);
v_snd_1877_ = lean_ctor_get(v_resStartStop_1860_, 1);
lean_inc(v_snd_1877_);
lean_dec_ref(v_resStartStop_1860_);
v_fst_1892_ = lean_ctor_get(v_snd_1877_, 0);
lean_inc(v_fst_1892_);
v_snd_1893_ = lean_ctor_get(v_snd_1877_, 1);
lean_inc(v_snd_1893_);
lean_dec(v_snd_1877_);
v___x_1894_ = l_Lean_trace_profiler;
v___x_1895_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1856_, v___x_1894_);
if (v___x_1895_ == 0)
{
v___y_1913_ = v___x_1895_;
goto v___jp_1912_;
}
else
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1951_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1856_, v___x_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; double v___x_1954_; double v___x_1955_; double v___x_1956_; 
v___x_1952_ = l_Lean_trace_profiler_threshold;
v___x_1953_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1856_, v___x_1952_);
v___x_1954_ = lean_float_of_nat(v___x_1953_);
v___x_1955_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_1956_ = lean_float_div(v___x_1954_, v___x_1955_);
v___y_1945_ = v___x_1956_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; double v___x_1959_; 
v___x_1957_ = l_Lean_trace_profiler_threshold;
v___x_1958_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1856_, v___x_1957_);
v___x_1959_ = lean_float_of_nat(v___x_1958_);
v___y_1945_ = v___x_1959_;
goto v___jp_1944_;
}
}
v___jp_1878_:
{
lean_object* v___x_1882_; 
lean_inc(v___y_1879_);
v___x_1882_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1858_, v_data_1881_, v___y_1879_, v___y_1880_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v___x_1883_; 
lean_dec_ref_known(v___x_1882_, 1);
v___x_1883_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1876_);
return v___x_1883_;
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_fst_1876_);
v_a_1884_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1882_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1882_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
v___jp_1896_:
{
uint8_t v_result_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; double v___x_1902_; lean_object* v_data_1903_; 
v_result_1899_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(v_fst_1876_);
v___x_1900_ = lean_box(v_result_1899_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
v___x_1902_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_1855_);
lean_inc_ref(v___x_1901_);
lean_inc(v_cls_1853_);
v_data_1903_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1903_, 0, v_cls_1853_);
lean_ctor_set(v_data_1903_, 1, v___x_1901_);
lean_ctor_set(v_data_1903_, 2, v_tag_1855_);
lean_ctor_set_float(v_data_1903_, sizeof(void*)*3, v___x_1902_);
lean_ctor_set_float(v_data_1903_, sizeof(void*)*3 + 8, v___x_1902_);
lean_ctor_set_uint8(v_data_1903_, sizeof(void*)*3 + 16, v_collapsed_1854_);
if (v___x_1895_ == 0)
{
lean_dec_ref_known(v___x_1901_, 1);
lean_dec(v_snd_1893_);
lean_dec(v_fst_1892_);
lean_dec_ref(v_tag_1855_);
lean_dec(v_cls_1853_);
v___y_1879_ = v___y_1897_;
v___y_1880_ = v_a_1898_;
v_data_1881_ = v_data_1903_;
goto v___jp_1878_;
}
else
{
lean_object* v_data_1904_; double v___x_1905_; double v___x_1906_; 
lean_dec_ref_known(v_data_1903_, 3);
v_data_1904_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1904_, 0, v_cls_1853_);
lean_ctor_set(v_data_1904_, 1, v___x_1901_);
lean_ctor_set(v_data_1904_, 2, v_tag_1855_);
v___x_1905_ = lean_unbox_float(v_fst_1892_);
lean_dec(v_fst_1892_);
lean_ctor_set_float(v_data_1904_, sizeof(void*)*3, v___x_1905_);
v___x_1906_ = lean_unbox_float(v_snd_1893_);
lean_dec(v_snd_1893_);
lean_ctor_set_float(v_data_1904_, sizeof(void*)*3 + 8, v___x_1906_);
lean_ctor_set_uint8(v_data_1904_, sizeof(void*)*3 + 16, v_collapsed_1854_);
v___y_1879_ = v___y_1897_;
v___y_1880_ = v_a_1898_;
v_data_1881_ = v_data_1904_;
goto v___jp_1878_;
}
}
v___jp_1907_:
{
lean_object* v_ref_1908_; lean_object* v___x_1909_; 
v_ref_1908_ = lean_ctor_get(v___y_1873_, 2);
lean_inc(v___y_1874_);
lean_inc_ref(v___y_1873_);
lean_inc(v___y_1872_);
lean_inc_ref(v___y_1871_);
lean_inc(v___y_1870_);
lean_inc_ref(v___y_1869_);
lean_inc(v___y_1868_);
lean_inc_ref(v___y_1867_);
lean_inc(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc(v___y_1862_);
lean_inc_ref(v___y_1861_);
lean_inc(v_fst_1876_);
v___x_1909_ = lean_apply_16(v_msg_1859_, v_fst_1876_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, lean_box(0));
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___y_1897_ = v_ref_1908_;
v_a_1898_ = v_a_1910_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1911_; 
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_1897_ = v_ref_1908_;
v_a_1898_ = v___x_1911_;
goto v___jp_1896_;
}
}
v___jp_1912_:
{
if (v_clsEnabled_1857_ == 0)
{
if (v___y_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v_traceState_1915_; lean_object* v_env_1916_; lean_object* v_nextMacroScope_1917_; lean_object* v_ngen_1918_; lean_object* v_auxDeclNGen_1919_; lean_object* v_cache_1920_; lean_object* v_recordedDeps_1921_; lean_object* v_messages_1922_; lean_object* v_infoState_1923_; lean_object* v_snapshotTasks_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_snd_1893_);
lean_dec(v_fst_1892_);
lean_dec_ref(v_msg_1859_);
lean_dec_ref(v_tag_1855_);
lean_dec(v_cls_1853_);
v___x_1914_ = lean_st_ref_take(v___y_1874_);
v_traceState_1915_ = lean_ctor_get(v___x_1914_, 4);
v_env_1916_ = lean_ctor_get(v___x_1914_, 0);
v_nextMacroScope_1917_ = lean_ctor_get(v___x_1914_, 1);
v_ngen_1918_ = lean_ctor_get(v___x_1914_, 2);
v_auxDeclNGen_1919_ = lean_ctor_get(v___x_1914_, 3);
v_cache_1920_ = lean_ctor_get(v___x_1914_, 5);
v_recordedDeps_1921_ = lean_ctor_get(v___x_1914_, 6);
v_messages_1922_ = lean_ctor_get(v___x_1914_, 7);
v_infoState_1923_ = lean_ctor_get(v___x_1914_, 8);
v_snapshotTasks_1924_ = lean_ctor_get(v___x_1914_, 9);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1926_ = v___x_1914_;
v_isShared_1927_ = v_isSharedCheck_1943_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_snapshotTasks_1924_);
lean_inc(v_infoState_1923_);
lean_inc(v_messages_1922_);
lean_inc(v_recordedDeps_1921_);
lean_inc(v_cache_1920_);
lean_inc(v_traceState_1915_);
lean_inc(v_auxDeclNGen_1919_);
lean_inc(v_ngen_1918_);
lean_inc(v_nextMacroScope_1917_);
lean_inc(v_env_1916_);
lean_dec(v___x_1914_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1943_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
uint64_t v_tid_1928_; lean_object* v_traces_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1942_; 
v_tid_1928_ = lean_ctor_get_uint64(v_traceState_1915_, sizeof(void*)*1);
v_traces_1929_ = lean_ctor_get(v_traceState_1915_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_traceState_1915_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1931_ = v_traceState_1915_;
v_isShared_1932_ = v_isSharedCheck_1942_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_traces_1929_);
lean_dec(v_traceState_1915_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1942_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1858_, v_traces_1929_);
lean_dec_ref(v_traces_1929_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1933_);
lean_ctor_set_uint64(v_reuseFailAlloc_1941_, sizeof(void*)*1, v_tid_1928_);
v___x_1935_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1937_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 4, v___x_1935_);
v___x_1937_ = v___x_1926_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_env_1916_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_nextMacroScope_1917_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_ngen_1918_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_auxDeclNGen_1919_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1940_, 5, v_cache_1920_);
lean_ctor_set(v_reuseFailAlloc_1940_, 6, v_recordedDeps_1921_);
lean_ctor_set(v_reuseFailAlloc_1940_, 7, v_messages_1922_);
lean_ctor_set(v_reuseFailAlloc_1940_, 8, v_infoState_1923_);
lean_ctor_set(v_reuseFailAlloc_1940_, 9, v_snapshotTasks_1924_);
v___x_1937_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_st_ref_put(v___y_1874_, v___x_1937_);
v___x_1939_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1876_);
return v___x_1939_;
}
}
}
}
}
else
{
goto v___jp_1907_;
}
}
else
{
goto v___jp_1907_;
}
}
v___jp_1944_:
{
double v___x_1946_; double v___x_1947_; double v___x_1948_; uint8_t v___x_1949_; 
v___x_1946_ = lean_unbox_float(v_snd_1893_);
v___x_1947_ = lean_unbox_float(v_fst_1892_);
v___x_1948_ = lean_float_sub(v___x_1946_, v___x_1947_);
v___x_1949_ = lean_float_decLt(v___y_1945_, v___x_1948_);
v___y_1913_ = v___x_1949_;
goto v___jp_1912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7___boxed(lean_object** _args){
lean_object* v_cls_1960_ = _args[0];
lean_object* v_collapsed_1961_ = _args[1];
lean_object* v_tag_1962_ = _args[2];
lean_object* v_opts_1963_ = _args[3];
lean_object* v_clsEnabled_1964_ = _args[4];
lean_object* v_oldTraces_1965_ = _args[5];
lean_object* v_msg_1966_ = _args[6];
lean_object* v_resStartStop_1967_ = _args[7];
lean_object* v___y_1968_ = _args[8];
lean_object* v___y_1969_ = _args[9];
lean_object* v___y_1970_ = _args[10];
lean_object* v___y_1971_ = _args[11];
lean_object* v___y_1972_ = _args[12];
lean_object* v___y_1973_ = _args[13];
lean_object* v___y_1974_ = _args[14];
lean_object* v___y_1975_ = _args[15];
lean_object* v___y_1976_ = _args[16];
lean_object* v___y_1977_ = _args[17];
lean_object* v___y_1978_ = _args[18];
lean_object* v___y_1979_ = _args[19];
lean_object* v___y_1980_ = _args[20];
lean_object* v___y_1981_ = _args[21];
lean_object* v___y_1982_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_1983_; uint8_t v_clsEnabled_boxed_1984_; lean_object* v_res_1985_; 
v_collapsed_boxed_1983_ = lean_unbox(v_collapsed_1961_);
v_clsEnabled_boxed_1984_ = lean_unbox(v_clsEnabled_1964_);
v_res_1985_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v_cls_1960_, v_collapsed_boxed_1983_, v_tag_1962_, v_opts_1963_, v_clsEnabled_boxed_1984_, v_oldTraces_1965_, v_msg_1966_, v_resStartStop_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v_opts_1963_);
return v_res_1985_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__2));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4(void){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1992_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4);
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5);
v___x_1996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
lean_ctor_set(v___x_1996_, 2, v___x_1995_);
lean_ctor_set(v___x_1996_, 3, v___x_1995_);
return v___x_1996_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__7));
v___x_1999_ = l_Lean_stringToMessageData(v___x_1998_);
return v___x_1999_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9(void){
_start:
{
lean_object* v___x_2000_; double v___x_2001_; 
v___x_2000_ = lean_unsigned_to_nat(1000000000u);
v___x_2001_ = lean_float_of_nat(v___x_2000_);
return v___x_2001_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2008_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__15));
v___x_2009_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__14));
v___x_2010_ = l_System_FilePath_join(v___x_2009_, v___x_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(lean_object* v_tacticContext_2011_, lean_object* v___x_2012_, lean_object* v_aig_2013_, lean_object* v___x_2014_, lean_object* v___x_2015_, lean_object* v___x_2016_, uint8_t v_hasTrace_2017_, lean_object* v___x_2018_, lean_object* v___f_2019_, lean_object* v___x_2020_, lean_object* v_cache_2021_, lean_object* v_ref_2022_, uint8_t v___x_2023_, lean_object* v_cls_2024_, lean_object* v___f_2025_, lean_object* v_cnfCache_2026_, lean_object* v___x_2027_, lean_object* v_result_2028_, lean_object* v___x_2029_, lean_object* v___x_2030_, lean_object* v_____r_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; uint8_t v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v_a_2225_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; uint8_t v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v_a_2257_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; uint8_t v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; uint8_t v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v_a_2517_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; uint8_t v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v_a_2550_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; uint8_t v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v_config_2669_; uint8_t v_graphviz_2670_; 
v_config_2669_ = lean_ctor_get(v_tacticContext_2011_, 5);
v_graphviz_2670_ = lean_ctor_get_uint8(v_config_2669_, sizeof(void*)*3 + 8);
if (v_graphviz_2670_ == 0)
{
v___y_2636_ = v___y_2032_;
v___y_2637_ = v___y_2033_;
v___y_2638_ = v___y_2034_;
v___y_2639_ = v___y_2035_;
v___y_2640_ = v___y_2036_;
v___y_2641_ = v___y_2037_;
v___y_2642_ = v___y_2038_;
v___y_2643_ = v___y_2039_;
v___y_2644_ = v___y_2040_;
v___y_2645_ = v___y_2041_;
v___y_2646_ = v___y_2042_;
v___y_2647_ = v___y_2043_;
v___y_2648_ = v___y_2044_;
v___y_2649_ = v___y_2045_;
goto v___jp_2635_;
}
else
{
lean_object* v_ref_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_ref_2671_ = lean_ctor_get(v___y_2044_, 2);
v___x_2672_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
lean_inc_ref(v_result_2028_);
v___x_2673_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v_result_2028_);
v___x_2674_ = l_IO_FS_writeFile(v___x_2672_, v___x_2673_);
lean_dec_ref(v___x_2673_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_dec_ref_known(v___x_2674_, 1);
v___y_2636_ = v___y_2032_;
v___y_2637_ = v___y_2033_;
v___y_2638_ = v___y_2034_;
v___y_2639_ = v___y_2035_;
v___y_2640_ = v___y_2036_;
v___y_2641_ = v___y_2037_;
v___y_2642_ = v___y_2038_;
v___y_2643_ = v___y_2039_;
v___y_2644_ = v___y_2040_;
v___y_2645_ = v___y_2041_;
v___y_2646_ = v___y_2042_;
v___y_2647_ = v___y_2043_;
v___y_2648_ = v___y_2044_;
v___y_2649_ = v___y_2045_;
goto v___jp_2635_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref(v___x_2030_);
lean_dec_ref(v___x_2029_);
lean_dec_ref(v_result_2028_);
lean_dec_ref(v___x_2027_);
lean_dec_ref(v_cnfCache_2026_);
lean_dec_ref(v___f_2025_);
lean_dec(v_cls_2024_);
lean_dec_ref(v_cache_2021_);
lean_dec_ref(v___f_2019_);
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_aig_2013_);
lean_dec_ref(v_tacticContext_2011_);
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2677_ = v___x_2674_;
v_isShared_2678_ = v_isSharedCheck_2686_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2674_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2686_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2679_ = lean_io_error_to_string(v_a_2675_);
v___x_2680_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
v___x_2681_ = l_Lean_MessageData_ofFormat(v___x_2680_);
lean_inc(v_ref_2671_);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_ref_2671_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2682_);
v___x_2684_ = v___x_2677_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
v___jp_2047_:
{
lean_object* v___x_2062_; 
v___x_2062_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___x_2012_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2052_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2074_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2069_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2013_, v_a_2063_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec(v_a_2063_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2070_);
v___x_2072_ = v___x_2067_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_a_2063_);
lean_dec_ref(v_aig_2013_);
v_a_2075_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2064_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2064_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref(v_aig_2013_);
v_a_2083_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2062_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2062_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
v___jp_2091_:
{
if (lean_obj_tag(v___y_2107_) == 0)
{
lean_object* v_a_2108_; uint8_t v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___y_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___y_2107_, 1);
v___x_2109_ = lean_unbox(v_a_2108_);
lean_dec(v_a_2108_);
switch(v___x_2109_)
{
case 0:
{
lean_object* v_toCold_2110_; lean_object* v_options_2111_; uint8_t v_hasTrace_2112_; 
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_tacticContext_2011_);
v_toCold_2110_ = lean_ctor_get(v___y_2095_, 0);
v_options_2111_ = lean_ctor_get(v_toCold_2110_, 2);
v_hasTrace_2112_ = lean_ctor_get_uint8(v_options_2111_, sizeof(void*)*1);
if (v_hasTrace_2112_ == 0)
{
lean_dec(v___y_2106_);
v___y_2048_ = v___y_2105_;
v___y_2049_ = v___y_2103_;
v___y_2050_ = v___y_2092_;
v___y_2051_ = v___y_2093_;
v___y_2052_ = v___y_2098_;
v___y_2053_ = v___y_2096_;
v___y_2054_ = v___y_2101_;
v___y_2055_ = v___y_2104_;
v___y_2056_ = v___y_2102_;
v___y_2057_ = v___y_2100_;
v___y_2058_ = v___y_2099_;
v___y_2059_ = v___y_2094_;
v___y_2060_ = v___y_2095_;
v___y_2061_ = v___y_2097_;
goto v___jp_2047_;
}
else
{
lean_object* v_inheritedTraceOptions_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_inheritedTraceOptions_2113_ = lean_ctor_get(v_toCold_2110_, 11);
v___x_2114_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2106_);
v___x_2115_ = l_Lean_Name_append(v___x_2114_, v___y_2106_);
v___x_2116_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2113_, v_options_2111_, v___x_2115_);
lean_dec(v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec(v___y_2106_);
v___y_2048_ = v___y_2105_;
v___y_2049_ = v___y_2103_;
v___y_2050_ = v___y_2092_;
v___y_2051_ = v___y_2093_;
v___y_2052_ = v___y_2098_;
v___y_2053_ = v___y_2096_;
v___y_2054_ = v___y_2101_;
v___y_2055_ = v___y_2104_;
v___y_2056_ = v___y_2102_;
v___y_2057_ = v___y_2100_;
v___y_2058_ = v___y_2099_;
v___y_2059_ = v___y_2094_;
v___y_2060_ = v___y_2095_;
v___y_2061_ = v___y_2097_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
v___x_2118_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_2106_, v___x_2117_, v___y_2099_, v___y_2094_, v___y_2095_, v___y_2097_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_dec_ref_known(v___x_2118_, 1);
v___y_2048_ = v___y_2105_;
v___y_2049_ = v___y_2103_;
v___y_2050_ = v___y_2092_;
v___y_2051_ = v___y_2093_;
v___y_2052_ = v___y_2098_;
v___y_2053_ = v___y_2096_;
v___y_2054_ = v___y_2101_;
v___y_2055_ = v___y_2104_;
v___y_2056_ = v___y_2102_;
v___y_2057_ = v___y_2100_;
v___y_2058_ = v___y_2099_;
v___y_2059_ = v___y_2094_;
v___y_2060_ = v___y_2095_;
v___y_2061_ = v___y_2097_;
goto v___jp_2047_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v_aig_2013_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_2127_; lean_object* v_satExpr_2128_; lean_object* v_hypQueue_2129_; lean_object* v_usedHyps_2130_; uint8_t v_didChange_2131_; lean_object* v_theoryState_2132_; lean_object* v_solverTimeBudgetMs_2133_; lean_object* v_roundBudget_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v___y_2106_);
lean_dec_ref(v_aig_2013_);
v___x_2127_ = lean_st_ref_take(v___y_2103_);
v_satExpr_2128_ = lean_ctor_get(v___x_2127_, 0);
v_hypQueue_2129_ = lean_ctor_get(v___x_2127_, 1);
v_usedHyps_2130_ = lean_ctor_get(v___x_2127_, 2);
v_didChange_2131_ = lean_ctor_get_uint8(v___x_2127_, sizeof(void*)*6);
v_theoryState_2132_ = lean_ctor_get(v___x_2127_, 3);
v_solverTimeBudgetMs_2133_ = lean_ctor_get(v___x_2127_, 4);
v_roundBudget_2134_ = lean_ctor_get(v___x_2127_, 5);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2136_ = v___x_2127_;
v_isShared_2137_ = v_isSharedCheck_2195_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_roundBudget_2134_);
lean_inc(v_solverTimeBudgetMs_2133_);
lean_inc(v_theoryState_2132_);
lean_inc(v_usedHyps_2130_);
lean_inc(v_hypQueue_2129_);
lean_inc(v_satExpr_2128_);
lean_dec(v___x_2127_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2195_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v_satSolver_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2191_; 
v___x_2138_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_2139_ = lean_ctor_get(v_theoryState_2132_, 3);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_theoryState_2132_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; lean_object* v_unused_2193_; lean_object* v_unused_2194_; 
v_unused_2192_ = lean_ctor_get(v_theoryState_2132_, 2);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_theoryState_2132_, 1);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_theoryState_2132_, 0);
lean_dec(v_unused_2194_);
v___x_2141_ = v_theoryState_2132_;
v_isShared_2142_ = v_isSharedCheck_2191_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_satSolver_2139_);
lean_dec(v_theoryState_2132_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2191_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2143_ = lean_box(0);
v___x_2144_ = lean_mk_array(v___x_2014_, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2015_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 2, v___x_2138_);
lean_ctor_set(v___x_2141_, 1, v___x_2016_);
lean_ctor_set(v___x_2141_, 0, v___x_2145_);
v___x_2147_ = v___x_2141_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v_satSolver_2139_);
v___x_2147_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2149_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 3, v___x_2147_);
v___x_2149_ = v___x_2136_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_satExpr_2128_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_hypQueue_2129_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_usedHyps_2130_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2189_, 4, v_solverTimeBudgetMs_2133_);
lean_ctor_set(v_reuseFailAlloc_2189_, 5, v_roundBudget_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2189_, sizeof(void*)*6, v_didChange_2131_);
v___x_2149_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = lean_st_ref_put(v___y_2103_, v___x_2149_);
v___x_2151_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_2105_, v___y_2103_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v_goal_2153_; lean_object* v___x_2154_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v_goal_2153_ = lean_ctor_get(v___y_2105_, 0);
lean_inc(v_goal_2153_);
v___x_2154_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_tacticContext_2011_, v_goal_2153_, v_a_2152_, v___y_2092_, v___y_2093_, v___y_2098_, v___y_2096_, v___y_2101_, v___y_2104_, v___y_2102_, v___y_2100_, v___y_2099_, v___y_2094_, v___y_2095_, v___y_2097_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2172_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2172_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2172_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
if (lean_obj_tag(v_a_2155_) == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref_known(v_a_2155_, 1);
lean_del_object(v___x_2157_);
v___x_2159_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_2160_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_2159_, v___y_2099_, v___y_2094_, v___y_2095_, v___y_2097_);
return v___x_2160_;
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2171_; 
v_a_2161_ = lean_ctor_get(v_a_2155_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_a_2155_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2163_ = v_a_2155_;
v_isShared_2164_ = v_isSharedCheck_2171_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v_a_2155_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2171_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2168_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2166_);
v___x_2168_ = v___x_2157_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
v_a_2173_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2154_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2154_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_tacticContext_2011_);
v_a_2181_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2151_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2151_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_2196_; 
lean_dec(v___y_2106_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_aig_2013_);
lean_dec_ref(v_tacticContext_2011_);
v___x_2196_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_2095_, v___y_2097_);
return v___x_2196_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v___y_2106_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_aig_2013_);
lean_dec_ref(v_tacticContext_2011_);
v_a_2197_ = lean_ctor_get(v___y_2107_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___y_2107_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___y_2107_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___y_2107_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
v___jp_2205_:
{
lean_object* v___x_2226_; double v___x_2227_; double v___x_2228_; double v___x_2229_; double v___x_2230_; double v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2226_ = lean_io_mono_nanos_now();
v___x_2227_ = lean_float_of_nat(v___y_2206_);
v___x_2228_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2229_ = lean_float_div(v___x_2227_, v___x_2228_);
v___x_2230_ = lean_float_of_nat(v___x_2226_);
v___x_2231_ = lean_float_div(v___x_2230_, v___x_2228_);
v___x_2232_ = lean_box_float(v___x_2229_);
v___x_2233_ = lean_box_float(v___x_2231_);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_a_2225_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
lean_inc(v___y_2224_);
v___x_2236_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2224_, v_hasTrace_2017_, v___x_2018_, v___y_2217_, v___y_2220_, v___y_2210_, v___f_2019_, v___x_2235_, v___y_2223_, v___y_2221_, v___y_2207_, v___y_2209_, v___y_2214_, v___y_2212_, v___y_2218_, v___y_2222_, v___y_2219_, v___y_2216_, v___y_2215_, v___y_2208_, v___y_2211_, v___y_2213_);
v___y_2092_ = v___y_2207_;
v___y_2093_ = v___y_2209_;
v___y_2094_ = v___y_2208_;
v___y_2095_ = v___y_2211_;
v___y_2096_ = v___y_2212_;
v___y_2097_ = v___y_2213_;
v___y_2098_ = v___y_2214_;
v___y_2099_ = v___y_2215_;
v___y_2100_ = v___y_2216_;
v___y_2101_ = v___y_2218_;
v___y_2102_ = v___y_2219_;
v___y_2103_ = v___y_2221_;
v___y_2104_ = v___y_2222_;
v___y_2105_ = v___y_2223_;
v___y_2106_ = v___y_2224_;
v___y_2107_ = v___x_2236_;
goto v___jp_2091_;
}
v___jp_2237_:
{
lean_object* v___x_2258_; double v___x_2259_; double v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2258_ = lean_io_get_num_heartbeats();
v___x_2259_ = lean_float_of_nat(v___y_2246_);
v___x_2260_ = lean_float_of_nat(v___x_2258_);
v___x_2261_ = lean_box_float(v___x_2259_);
v___x_2262_ = lean_box_float(v___x_2260_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v_a_2257_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
lean_inc(v___y_2256_);
v___x_2265_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2256_, v_hasTrace_2017_, v___x_2018_, v___y_2249_, v___y_2252_, v___y_2241_, v___f_2019_, v___x_2264_, v___y_2255_, v___y_2253_, v___y_2238_, v___y_2240_, v___y_2245_, v___y_2243_, v___y_2250_, v___y_2254_, v___y_2251_, v___y_2248_, v___y_2247_, v___y_2239_, v___y_2242_, v___y_2244_);
v___y_2092_ = v___y_2238_;
v___y_2093_ = v___y_2240_;
v___y_2094_ = v___y_2239_;
v___y_2095_ = v___y_2242_;
v___y_2096_ = v___y_2243_;
v___y_2097_ = v___y_2244_;
v___y_2098_ = v___y_2245_;
v___y_2099_ = v___y_2247_;
v___y_2100_ = v___y_2248_;
v___y_2101_ = v___y_2250_;
v___y_2102_ = v___y_2251_;
v___y_2103_ = v___y_2253_;
v___y_2104_ = v___y_2254_;
v___y_2105_ = v___y_2255_;
v___y_2106_ = v___y_2256_;
v___y_2107_ = v___x_2265_;
goto v___jp_2091_;
}
v___jp_2266_:
{
lean_object* v___x_2285_; lean_object* v_a_2286_; uint8_t v___x_2287_; 
v___x_2285_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_2272_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_2275_, v___x_2020_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_io_mono_nanos_now();
v___x_2289_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2283_, v___y_2282_, v___y_2280_, v___y_2267_, v___y_2268_, v___y_2273_, v___y_2270_, v___y_2277_, v___y_2281_, v___y_2278_, v___y_2276_, v___y_2274_, v___y_2269_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set_tag(v___x_2292_, 1);
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
v___y_2206_ = v___x_2288_;
v___y_2207_ = v___y_2267_;
v___y_2208_ = v___y_2269_;
v___y_2209_ = v___y_2268_;
v___y_2210_ = v_a_2286_;
v___y_2211_ = v___y_2271_;
v___y_2212_ = v___y_2270_;
v___y_2213_ = v___y_2272_;
v___y_2214_ = v___y_2273_;
v___y_2215_ = v___y_2274_;
v___y_2216_ = v___y_2276_;
v___y_2217_ = v___y_2275_;
v___y_2218_ = v___y_2277_;
v___y_2219_ = v___y_2278_;
v___y_2220_ = v___y_2279_;
v___y_2221_ = v___y_2280_;
v___y_2222_ = v___y_2281_;
v___y_2223_ = v___y_2282_;
v___y_2224_ = v___y_2284_;
v_a_2225_ = v___x_2295_;
goto v___jp_2205_;
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
v_a_2298_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2289_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2289_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 0);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
v___y_2206_ = v___x_2288_;
v___y_2207_ = v___y_2267_;
v___y_2208_ = v___y_2269_;
v___y_2209_ = v___y_2268_;
v___y_2210_ = v_a_2286_;
v___y_2211_ = v___y_2271_;
v___y_2212_ = v___y_2270_;
v___y_2213_ = v___y_2272_;
v___y_2214_ = v___y_2273_;
v___y_2215_ = v___y_2274_;
v___y_2216_ = v___y_2276_;
v___y_2217_ = v___y_2275_;
v___y_2218_ = v___y_2277_;
v___y_2219_ = v___y_2278_;
v___y_2220_ = v___y_2279_;
v___y_2221_ = v___y_2280_;
v___y_2222_ = v___y_2281_;
v___y_2223_ = v___y_2282_;
v___y_2224_ = v___y_2284_;
v_a_2225_ = v___x_2303_;
goto v___jp_2205_;
}
}
}
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_io_get_num_heartbeats();
v___x_2307_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2283_, v___y_2282_, v___y_2280_, v___y_2267_, v___y_2268_, v___y_2273_, v___y_2270_, v___y_2277_, v___y_2281_, v___y_2278_, v___y_2276_, v___y_2274_, v___y_2269_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 1);
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
v___y_2238_ = v___y_2267_;
v___y_2239_ = v___y_2269_;
v___y_2240_ = v___y_2268_;
v___y_2241_ = v_a_2286_;
v___y_2242_ = v___y_2271_;
v___y_2243_ = v___y_2270_;
v___y_2244_ = v___y_2272_;
v___y_2245_ = v___y_2273_;
v___y_2246_ = v___x_2306_;
v___y_2247_ = v___y_2274_;
v___y_2248_ = v___y_2276_;
v___y_2249_ = v___y_2275_;
v___y_2250_ = v___y_2277_;
v___y_2251_ = v___y_2278_;
v___y_2252_ = v___y_2279_;
v___y_2253_ = v___y_2280_;
v___y_2254_ = v___y_2281_;
v___y_2255_ = v___y_2282_;
v___y_2256_ = v___y_2284_;
v_a_2257_ = v___x_2313_;
goto v___jp_2237_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
v_a_2316_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2307_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2307_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set_tag(v___x_2318_, 0);
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
v___y_2238_ = v___y_2267_;
v___y_2239_ = v___y_2269_;
v___y_2240_ = v___y_2268_;
v___y_2241_ = v_a_2286_;
v___y_2242_ = v___y_2271_;
v___y_2243_ = v___y_2270_;
v___y_2244_ = v___y_2272_;
v___y_2245_ = v___y_2273_;
v___y_2246_ = v___x_2306_;
v___y_2247_ = v___y_2274_;
v___y_2248_ = v___y_2276_;
v___y_2249_ = v___y_2275_;
v___y_2250_ = v___y_2277_;
v___y_2251_ = v___y_2278_;
v___y_2252_ = v___y_2279_;
v___y_2253_ = v___y_2280_;
v___y_2254_ = v___y_2281_;
v___y_2255_ = v___y_2282_;
v___y_2256_ = v___y_2284_;
v_a_2257_ = v___x_2321_;
goto v___jp_2237_;
}
}
}
}
}
v___jp_2324_:
{
lean_object* v_toCold_2343_; lean_object* v_ref_2344_; lean_object* v___x_2345_; 
v_toCold_2343_ = lean_ctor_get(v___y_2328_, 0);
v_ref_2344_ = lean_ctor_get(v___y_2328_, 2);
lean_inc_ref(v___y_2341_);
v___x_2345_ = l_Lean_Cadical_Solver_assume(v___y_2341_, v___y_2335_, v___y_2342_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_options_2346_; uint8_t v_hasTrace_2347_; 
lean_dec_ref_known(v___x_2345_, 1);
v_options_2346_ = lean_ctor_get(v_toCold_2343_, 2);
v_hasTrace_2347_ = lean_ctor_get_uint8(v_options_2346_, sizeof(void*)*1);
if (v_hasTrace_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec_ref(v___f_2019_);
lean_dec_ref(v___x_2018_);
v___x_2348_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2341_, v___y_2339_, v___y_2337_, v___y_2325_, v___y_2327_, v___y_2331_, v___y_2329_, v___y_2334_, v___y_2338_, v___y_2336_, v___y_2333_, v___y_2332_, v___y_2326_, v___y_2328_, v___y_2330_);
v___y_2092_ = v___y_2325_;
v___y_2093_ = v___y_2327_;
v___y_2094_ = v___y_2326_;
v___y_2095_ = v___y_2328_;
v___y_2096_ = v___y_2329_;
v___y_2097_ = v___y_2330_;
v___y_2098_ = v___y_2331_;
v___y_2099_ = v___y_2332_;
v___y_2100_ = v___y_2333_;
v___y_2101_ = v___y_2334_;
v___y_2102_ = v___y_2336_;
v___y_2103_ = v___y_2337_;
v___y_2104_ = v___y_2338_;
v___y_2105_ = v___y_2339_;
v___y_2106_ = v___y_2340_;
v___y_2107_ = v___x_2348_;
goto v___jp_2091_;
}
else
{
lean_object* v_inheritedTraceOptions_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_inheritedTraceOptions_2349_ = lean_ctor_get(v_toCold_2343_, 11);
v___x_2350_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2340_);
v___x_2351_ = l_Lean_Name_append(v___x_2350_, v___y_2340_);
v___x_2352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2349_, v_options_2346_, v___x_2351_);
lean_dec(v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = l_Lean_trace_profiler;
v___x_2354_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_2346_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
lean_dec_ref(v___f_2019_);
lean_dec_ref(v___x_2018_);
v___x_2355_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2341_, v___y_2339_, v___y_2337_, v___y_2325_, v___y_2327_, v___y_2331_, v___y_2329_, v___y_2334_, v___y_2338_, v___y_2336_, v___y_2333_, v___y_2332_, v___y_2326_, v___y_2328_, v___y_2330_);
v___y_2092_ = v___y_2325_;
v___y_2093_ = v___y_2327_;
v___y_2094_ = v___y_2326_;
v___y_2095_ = v___y_2328_;
v___y_2096_ = v___y_2329_;
v___y_2097_ = v___y_2330_;
v___y_2098_ = v___y_2331_;
v___y_2099_ = v___y_2332_;
v___y_2100_ = v___y_2333_;
v___y_2101_ = v___y_2334_;
v___y_2102_ = v___y_2336_;
v___y_2103_ = v___y_2337_;
v___y_2104_ = v___y_2338_;
v___y_2105_ = v___y_2339_;
v___y_2106_ = v___y_2340_;
v___y_2107_ = v___x_2355_;
goto v___jp_2091_;
}
else
{
v___y_2267_ = v___y_2325_;
v___y_2268_ = v___y_2327_;
v___y_2269_ = v___y_2326_;
v___y_2270_ = v___y_2329_;
v___y_2271_ = v___y_2328_;
v___y_2272_ = v___y_2330_;
v___y_2273_ = v___y_2331_;
v___y_2274_ = v___y_2332_;
v___y_2275_ = v_options_2346_;
v___y_2276_ = v___y_2333_;
v___y_2277_ = v___y_2334_;
v___y_2278_ = v___y_2336_;
v___y_2279_ = v___x_2352_;
v___y_2280_ = v___y_2337_;
v___y_2281_ = v___y_2338_;
v___y_2282_ = v___y_2339_;
v___y_2283_ = v___y_2341_;
v___y_2284_ = v___y_2340_;
goto v___jp_2266_;
}
}
else
{
v___y_2267_ = v___y_2325_;
v___y_2268_ = v___y_2327_;
v___y_2269_ = v___y_2326_;
v___y_2270_ = v___y_2329_;
v___y_2271_ = v___y_2328_;
v___y_2272_ = v___y_2330_;
v___y_2273_ = v___y_2331_;
v___y_2274_ = v___y_2332_;
v___y_2275_ = v_options_2346_;
v___y_2276_ = v___y_2333_;
v___y_2277_ = v___y_2334_;
v___y_2278_ = v___y_2336_;
v___y_2279_ = v___x_2352_;
v___y_2280_ = v___y_2337_;
v___y_2281_ = v___y_2338_;
v___y_2282_ = v___y_2339_;
v___y_2283_ = v___y_2341_;
v___y_2284_ = v___y_2340_;
goto v___jp_2266_;
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___f_2019_);
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_aig_2013_);
lean_dec_ref(v_tacticContext_2011_);
v_a_2356_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2358_ = v___x_2345_;
v_isShared_2359_ = v_isSharedCheck_2367_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2345_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2367_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2360_ = lean_io_error_to_string(v_a_2356_);
v___x_2361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
v___x_2362_ = l_Lean_MessageData_ofFormat(v___x_2361_);
lean_inc(v_ref_2344_);
v___x_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2363_, 0, v_ref_2344_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2363_);
v___x_2365_ = v___x_2358_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
v___jp_2368_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_theoryState_2389_; lean_object* v_satExpr_2390_; lean_object* v_hypQueue_2391_; lean_object* v_usedHyps_2392_; uint8_t v_didChange_2393_; lean_object* v_solverTimeBudgetMs_2394_; lean_object* v_roundBudget_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2437_; 
lean_inc_ref(v_aig_2013_);
v___x_2387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2387_, 0, v_aig_2013_);
lean_ctor_set(v___x_2387_, 1, v_cache_2021_);
lean_ctor_set(v___x_2387_, 2, v___y_2369_);
v___x_2388_ = lean_st_ref_take(v___y_2374_);
v_theoryState_2389_ = lean_ctor_get(v___x_2388_, 3);
v_satExpr_2390_ = lean_ctor_get(v___x_2388_, 0);
v_hypQueue_2391_ = lean_ctor_get(v___x_2388_, 1);
v_usedHyps_2392_ = lean_ctor_get(v___x_2388_, 2);
v_didChange_2393_ = lean_ctor_get_uint8(v___x_2388_, sizeof(void*)*6);
v_solverTimeBudgetMs_2394_ = lean_ctor_get(v___x_2388_, 4);
v_roundBudget_2395_ = lean_ctor_get(v___x_2388_, 5);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2397_ = v___x_2388_;
v_isShared_2398_ = v_isSharedCheck_2437_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_roundBudget_2395_);
lean_inc(v_solverTimeBudgetMs_2394_);
lean_inc(v_theoryState_2389_);
lean_inc(v_usedHyps_2392_);
lean_inc(v_hypQueue_2391_);
lean_inc(v_satExpr_2390_);
lean_dec(v___x_2388_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2437_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_funState_2399_; lean_object* v_preprocessCaches_2400_; lean_object* v_satSolver_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2435_; 
v_funState_2399_ = lean_ctor_get(v_theoryState_2389_, 0);
v_preprocessCaches_2400_ = lean_ctor_get(v_theoryState_2389_, 2);
v_satSolver_2401_ = lean_ctor_get(v_theoryState_2389_, 3);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_theoryState_2389_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; 
v_unused_2436_ = lean_ctor_get(v_theoryState_2389_, 1);
lean_dec(v_unused_2436_);
v___x_2403_ = v_theoryState_2389_;
v_isShared_2404_ = v_isSharedCheck_2435_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_satSolver_2401_);
lean_inc(v_preprocessCaches_2400_);
lean_inc(v_funState_2399_);
lean_dec(v_theoryState_2389_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2435_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v___x_2387_);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_funState_2399_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v_preprocessCaches_2400_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v_satSolver_2401_);
v___x_2406_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2408_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 3, v___x_2406_);
v___x_2408_ = v___x_2397_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_satExpr_2390_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_hypQueue_2391_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_usedHyps_2392_);
lean_ctor_set(v_reuseFailAlloc_2433_, 3, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2433_, 4, v_solverTimeBudgetMs_2394_);
lean_ctor_set(v_reuseFailAlloc_2433_, 5, v_roundBudget_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2433_, sizeof(void*)*6, v_didChange_2393_);
v___x_2408_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_st_ref_put(v___y_2374_, v___x_2408_);
v___x_2410_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_2371_, v___y_2370_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2411_; 
lean_dec_ref_known(v___x_2410_, 1);
v___x_2411_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_2374_);
if (lean_obj_tag(v___x_2411_) == 0)
{
uint8_t v_invert_2412_; 
v_invert_2412_ = lean_ctor_get_uint8(v_ref_2022_, sizeof(void*)*1);
if (v_invert_2412_ == 0)
{
lean_object* v_a_2413_; lean_object* v_gate_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2411_, 1);
v_gate_2414_ = lean_ctor_get(v_ref_2022_, 0);
v___y_2325_ = v___y_2375_;
v___y_2326_ = v___y_2384_;
v___y_2327_ = v___y_2376_;
v___y_2328_ = v___y_2385_;
v___y_2329_ = v___y_2378_;
v___y_2330_ = v___y_2386_;
v___y_2331_ = v___y_2377_;
v___y_2332_ = v___y_2383_;
v___y_2333_ = v___y_2382_;
v___y_2334_ = v___y_2379_;
v___y_2335_ = v_gate_2414_;
v___y_2336_ = v___y_2381_;
v___y_2337_ = v___y_2374_;
v___y_2338_ = v___y_2380_;
v___y_2339_ = v___y_2373_;
v___y_2340_ = v___y_2372_;
v___y_2341_ = v_a_2413_;
v___y_2342_ = v_hasTrace_2017_;
goto v___jp_2324_;
}
else
{
lean_object* v_a_2415_; lean_object* v_gate_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2411_, 1);
v_gate_2416_ = lean_ctor_get(v_ref_2022_, 0);
v___y_2325_ = v___y_2375_;
v___y_2326_ = v___y_2384_;
v___y_2327_ = v___y_2376_;
v___y_2328_ = v___y_2385_;
v___y_2329_ = v___y_2378_;
v___y_2330_ = v___y_2386_;
v___y_2331_ = v___y_2377_;
v___y_2332_ = v___y_2383_;
v___y_2333_ = v___y_2382_;
v___y_2334_ = v___y_2379_;
v___y_2335_ = v_gate_2416_;
v___y_2336_ = v___y_2381_;
v___y_2337_ = v___y_2374_;
v___y_2338_ = v___y_2380_;
v___y_2339_ = v___y_2373_;
v___y_2340_ = v___y_2372_;
v___y_2341_ = v_a_2415_;
v___y_2342_ = v___x_2023_;
goto v___jp_2324_;
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v___y_2372_);
lean_dec_ref(v___f_2019_);
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_aig_2013_);
lean_dec_ref(v_tacticContext_2011_);
v_a_2417_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2411_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2411_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v___y_2372_);
lean_dec_ref(v___f_2019_);
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_aig_2013_);
lean_dec_ref(v_tacticContext_2011_);
v_a_2425_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2410_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2410_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
}
}
v___jp_2438_:
{
if (lean_obj_tag(v___y_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_toCold_2457_; lean_object* v_options_2458_; uint8_t v_hasTrace_2459_; 
v_a_2456_ = lean_ctor_get(v___y_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___y_2455_, 1);
v_toCold_2457_ = lean_ctor_get(v___y_2439_, 0);
v_options_2458_ = lean_ctor_get(v_toCold_2457_, 2);
v_hasTrace_2459_ = lean_ctor_get_uint8(v_options_2458_, sizeof(void*)*1);
if (v_hasTrace_2459_ == 0)
{
lean_object* v_cnf_2460_; 
lean_dec(v_cls_2024_);
v_cnf_2460_ = lean_ctor_get(v_a_2456_, 0);
lean_inc_ref(v_cnf_2460_);
v___y_2369_ = v_a_2456_;
v___y_2370_ = v_cnf_2460_;
v___y_2371_ = v___y_2450_;
v___y_2372_ = v___y_2452_;
v___y_2373_ = v___y_2440_;
v___y_2374_ = v___y_2442_;
v___y_2375_ = v___y_2441_;
v___y_2376_ = v___y_2449_;
v___y_2377_ = v___y_2453_;
v___y_2378_ = v___y_2451_;
v___y_2379_ = v___y_2446_;
v___y_2380_ = v___y_2443_;
v___y_2381_ = v___y_2447_;
v___y_2382_ = v___y_2454_;
v___y_2383_ = v___y_2448_;
v___y_2384_ = v___y_2444_;
v___y_2385_ = v___y_2439_;
v___y_2386_ = v___y_2445_;
goto v___jp_2368_;
}
else
{
lean_object* v_cnf_2461_; lean_object* v_inheritedTraceOptions_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v_cnf_2461_ = lean_ctor_get(v_a_2456_, 0);
lean_inc_ref(v_cnf_2461_);
v_inheritedTraceOptions_2462_ = lean_ctor_get(v_toCold_2457_, 11);
v___x_2463_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v_cls_2024_);
v___x_2464_ = l_Lean_Name_append(v___x_2463_, v_cls_2024_);
v___x_2465_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2462_, v_options_2458_, v___x_2464_);
lean_dec(v___x_2464_);
if (v___x_2465_ == 0)
{
lean_dec(v_cls_2024_);
v___y_2369_ = v_a_2456_;
v___y_2370_ = v_cnf_2461_;
v___y_2371_ = v___y_2450_;
v___y_2372_ = v___y_2452_;
v___y_2373_ = v___y_2440_;
v___y_2374_ = v___y_2442_;
v___y_2375_ = v___y_2441_;
v___y_2376_ = v___y_2449_;
v___y_2377_ = v___y_2453_;
v___y_2378_ = v___y_2451_;
v___y_2379_ = v___y_2446_;
v___y_2380_ = v___y_2443_;
v___y_2381_ = v___y_2447_;
v___y_2382_ = v___y_2454_;
v___y_2383_ = v___y_2448_;
v___y_2384_ = v___y_2444_;
v___y_2385_ = v___y_2439_;
v___y_2386_ = v___y_2445_;
goto v___jp_2368_;
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2466_ = lean_array_get_size(v_cnf_2461_);
v___x_2467_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_2468_ = l_Nat_reprFast(v___x_2466_);
v___x_2469_ = lean_string_append(v___x_2467_, v___x_2468_);
lean_dec_ref(v___x_2468_);
v___x_2470_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_2471_ = lean_string_append(v___x_2469_, v___x_2470_);
v___x_2472_ = lean_nat_sub(v___x_2466_, v___y_2450_);
v___x_2473_ = l_Nat_reprFast(v___x_2472_);
v___x_2474_ = lean_string_append(v___x_2471_, v___x_2473_);
lean_dec_ref(v___x_2473_);
v___x_2475_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_2476_ = lean_string_append(v___x_2474_, v___x_2475_);
v___x_2477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
v___x_2478_ = l_Lean_MessageData_ofFormat(v___x_2477_);
v___x_2479_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_2024_, v___x_2478_, v___y_2448_, v___y_2444_, v___y_2439_, v___y_2445_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_dec_ref_known(v___x_2479_, 1);
v___y_2369_ = v_a_2456_;
v___y_2370_ = v_cnf_2461_;
v___y_2371_ = v___y_2450_;
v___y_2372_ = v___y_2452_;
v___y_2373_ = v___y_2440_;
v___y_2374_ = v___y_2442_;
v___y_2375_ = v___y_2441_;
v___y_2376_ = v___y_2449_;
v___y_2377_ = v___y_2453_;
v___y_2378_ = v___y_2451_;
v___y_2379_ = v___y_2446_;
v___y_2380_ = v___y_2443_;
v___y_2381_ = v___y_2447_;
v___y_2382_ = v___y_2454_;
v___y_2383_ = v___y_2448_;
v___y_2384_ = v___y_2444_;
v___y_2385_ = v___y_2439_;
v___y_2386_ = v___y_2445_;
goto v___jp_2368_;
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec_ref(v_cnf_2461_);
lean_dec(v_a_2456_);
lean_dec(v___y_2452_);
lean_dec(v___y_2450_);
lean_dec_ref(v_cache_2021_);
lean_dec_ref(v___f_2019_);
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_aig_2013_);
lean_dec_ref(v_tacticContext_2011_);
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v___y_2452_);
lean_dec(v___y_2450_);
lean_dec(v_cls_2024_);
lean_dec_ref(v_cache_2021_);
lean_dec_ref(v___f_2019_);
lean_dec_ref(v___x_2018_);
lean_dec_ref(v___x_2016_);
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_aig_2013_);
lean_dec_ref(v_tacticContext_2011_);
v_a_2488_ = lean_ctor_get(v___y_2455_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___y_2455_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___y_2455_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___y_2455_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
v___jp_2496_:
{
lean_object* v___x_2518_; double v___x_2519_; double v___x_2520_; double v___x_2521_; double v___x_2522_; double v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2518_ = lean_io_mono_nanos_now();
v___x_2519_ = lean_float_of_nat(v___y_2504_);
v___x_2520_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2521_ = lean_float_div(v___x_2519_, v___x_2520_);
v___x_2522_ = lean_float_of_nat(v___x_2518_);
v___x_2523_ = lean_float_div(v___x_2522_, v___x_2520_);
v___x_2524_ = lean_box_float(v___x_2521_);
v___x_2525_ = lean_box_float(v___x_2523_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v_a_2517_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
lean_inc_ref(v___x_2018_);
lean_inc(v___y_2515_);
v___x_2528_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_2515_, v_hasTrace_2017_, v___x_2018_, v___y_2509_, v___y_2502_, v___y_2512_, v___f_2025_, v___x_2527_, v___y_2498_, v___y_2500_, v___y_2499_, v___y_2510_, v___y_2516_, v___y_2513_, v___y_2506_, v___y_2501_, v___y_2507_, v___y_2514_, v___y_2508_, v___y_2503_, v___y_2497_, v___y_2505_);
v___y_2439_ = v___y_2497_;
v___y_2440_ = v___y_2498_;
v___y_2441_ = v___y_2499_;
v___y_2442_ = v___y_2500_;
v___y_2443_ = v___y_2501_;
v___y_2444_ = v___y_2503_;
v___y_2445_ = v___y_2505_;
v___y_2446_ = v___y_2506_;
v___y_2447_ = v___y_2507_;
v___y_2448_ = v___y_2508_;
v___y_2449_ = v___y_2510_;
v___y_2450_ = v___y_2511_;
v___y_2451_ = v___y_2513_;
v___y_2452_ = v___y_2515_;
v___y_2453_ = v___y_2516_;
v___y_2454_ = v___y_2514_;
v___y_2455_ = v___x_2528_;
goto v___jp_2438_;
}
v___jp_2529_:
{
lean_object* v___x_2551_; double v___x_2552_; double v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2551_ = lean_io_get_num_heartbeats();
v___x_2552_ = lean_float_of_nat(v___y_2544_);
v___x_2553_ = lean_float_of_nat(v___x_2551_);
v___x_2554_ = lean_box_float(v___x_2552_);
v___x_2555_ = lean_box_float(v___x_2553_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v_a_2550_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
lean_inc_ref(v___x_2018_);
lean_inc(v___y_2548_);
v___x_2558_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_2548_, v_hasTrace_2017_, v___x_2018_, v___y_2541_, v___y_2535_, v___y_2545_, v___f_2025_, v___x_2557_, v___y_2531_, v___y_2533_, v___y_2532_, v___y_2542_, v___y_2549_, v___y_2546_, v___y_2538_, v___y_2534_, v___y_2539_, v___y_2547_, v___y_2540_, v___y_2536_, v___y_2530_, v___y_2537_);
v___y_2439_ = v___y_2530_;
v___y_2440_ = v___y_2531_;
v___y_2441_ = v___y_2532_;
v___y_2442_ = v___y_2533_;
v___y_2443_ = v___y_2534_;
v___y_2444_ = v___y_2536_;
v___y_2445_ = v___y_2537_;
v___y_2446_ = v___y_2538_;
v___y_2447_ = v___y_2539_;
v___y_2448_ = v___y_2540_;
v___y_2449_ = v___y_2542_;
v___y_2450_ = v___y_2543_;
v___y_2451_ = v___y_2546_;
v___y_2452_ = v___y_2548_;
v___y_2453_ = v___y_2549_;
v___y_2454_ = v___y_2547_;
v___y_2455_ = v___x_2558_;
goto v___jp_2438_;
}
v___jp_2559_:
{
lean_object* v___x_2580_; lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2634_; 
v___x_2580_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_2568_);
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2634_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2634_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_2573_, v___x_2020_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_io_mono_nanos_now();
v___x_2587_ = l_IO_lazyPure___redArg(v___y_2562_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_del_object(v___x_2583_);
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 1);
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
v___y_2497_ = v___y_2561_;
v___y_2498_ = v___y_2560_;
v___y_2499_ = v___y_2563_;
v___y_2500_ = v___y_2564_;
v___y_2501_ = v___y_2565_;
v___y_2502_ = v___y_2566_;
v___y_2503_ = v___y_2567_;
v___y_2504_ = v___x_2586_;
v___y_2505_ = v___y_2568_;
v___y_2506_ = v___y_2569_;
v___y_2507_ = v___y_2571_;
v___y_2508_ = v___y_2572_;
v___y_2509_ = v___y_2573_;
v___y_2510_ = v___y_2574_;
v___y_2511_ = v___y_2575_;
v___y_2512_ = v_a_2581_;
v___y_2513_ = v___y_2576_;
v___y_2514_ = v___y_2579_;
v___y_2515_ = v___y_2577_;
v___y_2516_ = v___y_2578_;
v_a_2517_ = v___x_2593_;
goto v___jp_2496_;
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2609_; 
v_a_2596_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2598_ = v___x_2587_;
v_isShared_2599_ = v_isSharedCheck_2609_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2587_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2609_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2600_ = lean_io_error_to_string(v_a_2596_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set_tag(v___x_2598_, 3);
lean_ctor_set(v___x_2598_, 0, v___x_2600_);
v___x_2602_ = v___x_2598_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2603_ = l_Lean_MessageData_ofFormat(v___x_2602_);
lean_inc(v___y_2570_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___y_2570_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2604_);
v___x_2606_ = v___x_2583_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
v___y_2497_ = v___y_2561_;
v___y_2498_ = v___y_2560_;
v___y_2499_ = v___y_2563_;
v___y_2500_ = v___y_2564_;
v___y_2501_ = v___y_2565_;
v___y_2502_ = v___y_2566_;
v___y_2503_ = v___y_2567_;
v___y_2504_ = v___x_2586_;
v___y_2505_ = v___y_2568_;
v___y_2506_ = v___y_2569_;
v___y_2507_ = v___y_2571_;
v___y_2508_ = v___y_2572_;
v___y_2509_ = v___y_2573_;
v___y_2510_ = v___y_2574_;
v___y_2511_ = v___y_2575_;
v___y_2512_ = v_a_2581_;
v___y_2513_ = v___y_2576_;
v___y_2514_ = v___y_2579_;
v___y_2515_ = v___y_2577_;
v___y_2516_ = v___y_2578_;
v_a_2517_ = v___x_2606_;
goto v___jp_2496_;
}
}
}
}
}
else
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_io_get_num_heartbeats();
v___x_2611_ = l_IO_lazyPure___redArg(v___y_2562_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_del_object(v___x_2583_);
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set_tag(v___x_2614_, 1);
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
v___y_2530_ = v___y_2561_;
v___y_2531_ = v___y_2560_;
v___y_2532_ = v___y_2563_;
v___y_2533_ = v___y_2564_;
v___y_2534_ = v___y_2565_;
v___y_2535_ = v___y_2566_;
v___y_2536_ = v___y_2567_;
v___y_2537_ = v___y_2568_;
v___y_2538_ = v___y_2569_;
v___y_2539_ = v___y_2571_;
v___y_2540_ = v___y_2572_;
v___y_2541_ = v___y_2573_;
v___y_2542_ = v___y_2574_;
v___y_2543_ = v___y_2575_;
v___y_2544_ = v___x_2610_;
v___y_2545_ = v_a_2581_;
v___y_2546_ = v___y_2576_;
v___y_2547_ = v___y_2579_;
v___y_2548_ = v___y_2577_;
v___y_2549_ = v___y_2578_;
v_a_2550_ = v___x_2617_;
goto v___jp_2529_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2633_; 
v_a_2620_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2622_ = v___x_2611_;
v_isShared_2623_ = v_isSharedCheck_2633_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2611_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2633_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_io_error_to_string(v_a_2620_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 3);
lean_ctor_set(v___x_2622_, 0, v___x_2624_);
v___x_2626_ = v___x_2622_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2627_ = l_Lean_MessageData_ofFormat(v___x_2626_);
lean_inc(v___y_2570_);
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___y_2570_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2628_);
v___x_2630_ = v___x_2583_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
v___y_2530_ = v___y_2561_;
v___y_2531_ = v___y_2560_;
v___y_2532_ = v___y_2563_;
v___y_2533_ = v___y_2564_;
v___y_2534_ = v___y_2565_;
v___y_2535_ = v___y_2566_;
v___y_2536_ = v___y_2567_;
v___y_2537_ = v___y_2568_;
v___y_2538_ = v___y_2569_;
v___y_2539_ = v___y_2571_;
v___y_2540_ = v___y_2572_;
v___y_2541_ = v___y_2573_;
v___y_2542_ = v___y_2574_;
v___y_2543_ = v___y_2575_;
v___y_2544_ = v___x_2610_;
v___y_2545_ = v_a_2581_;
v___y_2546_ = v___y_2576_;
v___y_2547_ = v___y_2579_;
v___y_2548_ = v___y_2577_;
v___y_2549_ = v___y_2578_;
v_a_2550_ = v___x_2630_;
goto v___jp_2529_;
}
}
}
}
}
}
}
v___jp_2635_:
{
lean_object* v_toCold_2650_; lean_object* v_options_2651_; lean_object* v_cnf_2652_; lean_object* v_ref_2653_; lean_object* v_inheritedTraceOptions_2654_; uint8_t v_hasTrace_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_toCold_2650_ = lean_ctor_get(v___y_2648_, 0);
v_options_2651_ = lean_ctor_get(v_toCold_2650_, 2);
v_cnf_2652_ = lean_ctor_get(v_cnfCache_2026_, 0);
v_ref_2653_ = lean_ctor_get(v___y_2648_, 2);
v_inheritedTraceOptions_2654_ = lean_ctor_get(v_toCold_2650_, 11);
v_hasTrace_2655_ = lean_ctor_get_uint8(v_options_2651_, sizeof(void*)*1);
v___x_2656_ = lean_array_get_size(v_cnf_2652_);
v___x_2657_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_2658_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig_2013_, v_cnfCache_2026_);
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2659_, 0, v___x_2027_);
lean_closure_set(v___f_2659_, 1, v___x_2657_);
lean_closure_set(v___f_2659_, 2, v_result_2028_);
lean_closure_set(v___f_2659_, 3, v___x_2658_);
v___x_2660_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13));
v___x_2661_ = l_Lean_Name_mkStr3(v___x_2029_, v___x_2030_, v___x_2660_);
if (v_hasTrace_2655_ == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref(v___f_2025_);
v___x_2662_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_2659_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
v___y_2439_ = v___y_2648_;
v___y_2440_ = v___y_2636_;
v___y_2441_ = v___y_2638_;
v___y_2442_ = v___y_2637_;
v___y_2443_ = v___y_2643_;
v___y_2444_ = v___y_2647_;
v___y_2445_ = v___y_2649_;
v___y_2446_ = v___y_2642_;
v___y_2447_ = v___y_2644_;
v___y_2448_ = v___y_2646_;
v___y_2449_ = v___y_2639_;
v___y_2450_ = v___x_2656_;
v___y_2451_ = v___y_2641_;
v___y_2452_ = v___x_2661_;
v___y_2453_ = v___y_2640_;
v___y_2454_ = v___y_2645_;
v___y_2455_ = v___x_2662_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2663_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___x_2661_);
v___x_2664_ = l_Lean_Name_append(v___x_2663_, v___x_2661_);
v___x_2665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2654_, v_options_2651_, v___x_2664_);
lean_dec(v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = l_Lean_trace_profiler;
v___x_2667_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_2651_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; 
lean_dec_ref(v___f_2025_);
v___x_2668_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_2659_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
v___y_2439_ = v___y_2648_;
v___y_2440_ = v___y_2636_;
v___y_2441_ = v___y_2638_;
v___y_2442_ = v___y_2637_;
v___y_2443_ = v___y_2643_;
v___y_2444_ = v___y_2647_;
v___y_2445_ = v___y_2649_;
v___y_2446_ = v___y_2642_;
v___y_2447_ = v___y_2644_;
v___y_2448_ = v___y_2646_;
v___y_2449_ = v___y_2639_;
v___y_2450_ = v___x_2656_;
v___y_2451_ = v___y_2641_;
v___y_2452_ = v___x_2661_;
v___y_2453_ = v___y_2640_;
v___y_2454_ = v___y_2645_;
v___y_2455_ = v___x_2668_;
goto v___jp_2438_;
}
else
{
v___y_2560_ = v___y_2636_;
v___y_2561_ = v___y_2648_;
v___y_2562_ = v___f_2659_;
v___y_2563_ = v___y_2638_;
v___y_2564_ = v___y_2637_;
v___y_2565_ = v___y_2643_;
v___y_2566_ = v___x_2665_;
v___y_2567_ = v___y_2647_;
v___y_2568_ = v___y_2649_;
v___y_2569_ = v___y_2642_;
v___y_2570_ = v_ref_2653_;
v___y_2571_ = v___y_2644_;
v___y_2572_ = v___y_2646_;
v___y_2573_ = v_options_2651_;
v___y_2574_ = v___y_2639_;
v___y_2575_ = v___x_2656_;
v___y_2576_ = v___y_2641_;
v___y_2577_ = v___x_2661_;
v___y_2578_ = v___y_2640_;
v___y_2579_ = v___y_2645_;
goto v___jp_2559_;
}
}
else
{
v___y_2560_ = v___y_2636_;
v___y_2561_ = v___y_2648_;
v___y_2562_ = v___f_2659_;
v___y_2563_ = v___y_2638_;
v___y_2564_ = v___y_2637_;
v___y_2565_ = v___y_2643_;
v___y_2566_ = v___x_2665_;
v___y_2567_ = v___y_2647_;
v___y_2568_ = v___y_2649_;
v___y_2569_ = v___y_2642_;
v___y_2570_ = v_ref_2653_;
v___y_2571_ = v___y_2644_;
v___y_2572_ = v___y_2646_;
v___y_2573_ = v_options_2651_;
v___y_2574_ = v___y_2639_;
v___y_2575_ = v___x_2656_;
v___y_2576_ = v___y_2641_;
v___y_2577_ = v___x_2661_;
v___y_2578_ = v___y_2640_;
v___y_2579_ = v___y_2645_;
goto v___jp_2559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___boxed(lean_object** _args){
lean_object* v_tacticContext_2687_ = _args[0];
lean_object* v___x_2688_ = _args[1];
lean_object* v_aig_2689_ = _args[2];
lean_object* v___x_2690_ = _args[3];
lean_object* v___x_2691_ = _args[4];
lean_object* v___x_2692_ = _args[5];
lean_object* v_hasTrace_2693_ = _args[6];
lean_object* v___x_2694_ = _args[7];
lean_object* v___f_2695_ = _args[8];
lean_object* v___x_2696_ = _args[9];
lean_object* v_cache_2697_ = _args[10];
lean_object* v_ref_2698_ = _args[11];
lean_object* v___x_2699_ = _args[12];
lean_object* v_cls_2700_ = _args[13];
lean_object* v___f_2701_ = _args[14];
lean_object* v_cnfCache_2702_ = _args[15];
lean_object* v___x_2703_ = _args[16];
lean_object* v_result_2704_ = _args[17];
lean_object* v___x_2705_ = _args[18];
lean_object* v___x_2706_ = _args[19];
lean_object* v_____r_2707_ = _args[20];
lean_object* v___y_2708_ = _args[21];
lean_object* v___y_2709_ = _args[22];
lean_object* v___y_2710_ = _args[23];
lean_object* v___y_2711_ = _args[24];
lean_object* v___y_2712_ = _args[25];
lean_object* v___y_2713_ = _args[26];
lean_object* v___y_2714_ = _args[27];
lean_object* v___y_2715_ = _args[28];
lean_object* v___y_2716_ = _args[29];
lean_object* v___y_2717_ = _args[30];
lean_object* v___y_2718_ = _args[31];
lean_object* v___y_2719_ = _args[32];
lean_object* v___y_2720_ = _args[33];
lean_object* v___y_2721_ = _args[34];
lean_object* v___y_2722_ = _args[35];
_start:
{
uint8_t v_hasTrace_boxed_2723_; uint8_t v___x_1192843__boxed_2724_; lean_object* v_res_2725_; 
v_hasTrace_boxed_2723_ = lean_unbox(v_hasTrace_2693_);
v___x_1192843__boxed_2724_ = lean_unbox(v___x_2699_);
v_res_2725_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v_tacticContext_2687_, v___x_2688_, v_aig_2689_, v___x_2690_, v___x_2691_, v___x_2692_, v_hasTrace_boxed_2723_, v___x_2694_, v___f_2695_, v___x_2696_, v_cache_2697_, v_ref_2698_, v___x_1192843__boxed_2724_, v_cls_2700_, v___f_2701_, v_cnfCache_2702_, v___x_2703_, v_result_2704_, v___x_2705_, v___x_2706_, v_____r_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec_ref(v_ref_2698_);
lean_dec_ref(v___x_2696_);
lean_dec(v___x_2688_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(lean_object* v_tacticContext_2726_, lean_object* v___x_2727_, lean_object* v_aig_2728_, lean_object* v___x_2729_, lean_object* v___x_2730_, lean_object* v___x_2731_, uint8_t v___x_2732_, lean_object* v___x_2733_, lean_object* v___f_2734_, lean_object* v___x_2735_, lean_object* v_cache_2736_, lean_object* v_ref_2737_, lean_object* v_cls_2738_, lean_object* v___f_2739_, lean_object* v_cnfCache_2740_, lean_object* v___x_2741_, lean_object* v_result_2742_, lean_object* v___x_2743_, lean_object* v___x_2744_, lean_object* v_____r_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; uint8_t v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v_a_2939_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; uint8_t v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v_a_2971_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; uint8_t v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; uint8_t v___y_3056_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v_a_3232_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; uint8_t v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v_a_3265_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v_config_3384_; uint8_t v_graphviz_3385_; 
v_config_3384_ = lean_ctor_get(v_tacticContext_2726_, 5);
v_graphviz_3385_ = lean_ctor_get_uint8(v_config_3384_, sizeof(void*)*3 + 8);
if (v_graphviz_3385_ == 0)
{
v___y_3351_ = v___y_2746_;
v___y_3352_ = v___y_2747_;
v___y_3353_ = v___y_2748_;
v___y_3354_ = v___y_2749_;
v___y_3355_ = v___y_2750_;
v___y_3356_ = v___y_2751_;
v___y_3357_ = v___y_2752_;
v___y_3358_ = v___y_2753_;
v___y_3359_ = v___y_2754_;
v___y_3360_ = v___y_2755_;
v___y_3361_ = v___y_2756_;
v___y_3362_ = v___y_2757_;
v___y_3363_ = v___y_2758_;
v___y_3364_ = v___y_2759_;
goto v___jp_3350_;
}
else
{
lean_object* v_ref_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_ref_3386_ = lean_ctor_get(v___y_2758_, 2);
v___x_3387_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
lean_inc_ref(v_result_2742_);
v___x_3388_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v_result_2742_);
v___x_3389_ = l_IO_FS_writeFile(v___x_3387_, v___x_3388_);
lean_dec_ref(v___x_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_dec_ref_known(v___x_3389_, 1);
v___y_3351_ = v___y_2746_;
v___y_3352_ = v___y_2747_;
v___y_3353_ = v___y_2748_;
v___y_3354_ = v___y_2749_;
v___y_3355_ = v___y_2750_;
v___y_3356_ = v___y_2751_;
v___y_3357_ = v___y_2752_;
v___y_3358_ = v___y_2753_;
v___y_3359_ = v___y_2754_;
v___y_3360_ = v___y_2755_;
v___y_3361_ = v___y_2756_;
v___y_3362_ = v___y_2757_;
v___y_3363_ = v___y_2758_;
v___y_3364_ = v___y_2759_;
goto v___jp_3350_;
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v___x_2744_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v_result_2742_);
lean_dec_ref(v___x_2741_);
lean_dec_ref(v_cnfCache_2740_);
lean_dec_ref(v___f_2739_);
lean_dec(v_cls_2738_);
lean_dec_ref(v_cache_2736_);
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_aig_2728_);
lean_dec_ref(v_tacticContext_2726_);
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3392_ = v___x_3389_;
v_isShared_3393_ = v_isSharedCheck_3401_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3401_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3394_ = lean_io_error_to_string(v_a_3390_);
v___x_3395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
v___x_3396_ = l_Lean_MessageData_ofFormat(v___x_3395_);
lean_inc(v_ref_3386_);
v___x_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3397_, 0, v_ref_3386_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___x_3397_);
v___x_3399_ = v___x_3392_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
v___jp_2761_:
{
lean_object* v___x_2776_; 
v___x_2776_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___x_2727_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2766_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2788_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2788_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2788_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2783_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2728_, v_a_2777_, v_a_2779_);
lean_dec(v_a_2779_);
lean_dec(v_a_2777_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2784_);
v___x_2786_ = v___x_2781_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_a_2777_);
lean_dec_ref(v_aig_2728_);
v_a_2789_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2778_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2778_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
lean_dec_ref(v_aig_2728_);
v_a_2797_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v___x_2776_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2776_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
v___jp_2805_:
{
if (lean_obj_tag(v___y_2821_) == 0)
{
lean_object* v_a_2822_; uint8_t v___x_2823_; 
v_a_2822_ = lean_ctor_get(v___y_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___y_2821_, 1);
v___x_2823_ = lean_unbox(v_a_2822_);
lean_dec(v_a_2822_);
switch(v___x_2823_)
{
case 0:
{
lean_object* v_toCold_2824_; lean_object* v_options_2825_; uint8_t v_hasTrace_2826_; 
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_tacticContext_2726_);
v_toCold_2824_ = lean_ctor_get(v___y_2816_, 0);
v_options_2825_ = lean_ctor_get(v_toCold_2824_, 2);
v_hasTrace_2826_ = lean_ctor_get_uint8(v_options_2825_, sizeof(void*)*1);
if (v_hasTrace_2826_ == 0)
{
lean_dec(v___y_2813_);
v___y_2762_ = v___y_2815_;
v___y_2763_ = v___y_2808_;
v___y_2764_ = v___y_2806_;
v___y_2765_ = v___y_2817_;
v___y_2766_ = v___y_2811_;
v___y_2767_ = v___y_2807_;
v___y_2768_ = v___y_2819_;
v___y_2769_ = v___y_2820_;
v___y_2770_ = v___y_2812_;
v___y_2771_ = v___y_2809_;
v___y_2772_ = v___y_2818_;
v___y_2773_ = v___y_2810_;
v___y_2774_ = v___y_2816_;
v___y_2775_ = v___y_2814_;
goto v___jp_2761_;
}
else
{
lean_object* v_inheritedTraceOptions_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v_inheritedTraceOptions_2827_ = lean_ctor_get(v_toCold_2824_, 11);
v___x_2828_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2813_);
v___x_2829_ = l_Lean_Name_append(v___x_2828_, v___y_2813_);
v___x_2830_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2827_, v_options_2825_, v___x_2829_);
lean_dec(v___x_2829_);
if (v___x_2830_ == 0)
{
lean_dec(v___y_2813_);
v___y_2762_ = v___y_2815_;
v___y_2763_ = v___y_2808_;
v___y_2764_ = v___y_2806_;
v___y_2765_ = v___y_2817_;
v___y_2766_ = v___y_2811_;
v___y_2767_ = v___y_2807_;
v___y_2768_ = v___y_2819_;
v___y_2769_ = v___y_2820_;
v___y_2770_ = v___y_2812_;
v___y_2771_ = v___y_2809_;
v___y_2772_ = v___y_2818_;
v___y_2773_ = v___y_2810_;
v___y_2774_ = v___y_2816_;
v___y_2775_ = v___y_2814_;
goto v___jp_2761_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
v___x_2832_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_2813_, v___x_2831_, v___y_2818_, v___y_2810_, v___y_2816_, v___y_2814_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_dec_ref_known(v___x_2832_, 1);
v___y_2762_ = v___y_2815_;
v___y_2763_ = v___y_2808_;
v___y_2764_ = v___y_2806_;
v___y_2765_ = v___y_2817_;
v___y_2766_ = v___y_2811_;
v___y_2767_ = v___y_2807_;
v___y_2768_ = v___y_2819_;
v___y_2769_ = v___y_2820_;
v___y_2770_ = v___y_2812_;
v___y_2771_ = v___y_2809_;
v___y_2772_ = v___y_2818_;
v___y_2773_ = v___y_2810_;
v___y_2774_ = v___y_2816_;
v___y_2775_ = v___y_2814_;
goto v___jp_2761_;
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec_ref(v_aig_2728_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_2841_; lean_object* v_satExpr_2842_; lean_object* v_hypQueue_2843_; lean_object* v_usedHyps_2844_; uint8_t v_didChange_2845_; lean_object* v_theoryState_2846_; lean_object* v_solverTimeBudgetMs_2847_; lean_object* v_roundBudget_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v___y_2813_);
lean_dec_ref(v_aig_2728_);
v___x_2841_ = lean_st_ref_take(v___y_2808_);
v_satExpr_2842_ = lean_ctor_get(v___x_2841_, 0);
v_hypQueue_2843_ = lean_ctor_get(v___x_2841_, 1);
v_usedHyps_2844_ = lean_ctor_get(v___x_2841_, 2);
v_didChange_2845_ = lean_ctor_get_uint8(v___x_2841_, sizeof(void*)*6);
v_theoryState_2846_ = lean_ctor_get(v___x_2841_, 3);
v_solverTimeBudgetMs_2847_ = lean_ctor_get(v___x_2841_, 4);
v_roundBudget_2848_ = lean_ctor_get(v___x_2841_, 5);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2850_ = v___x_2841_;
v_isShared_2851_ = v_isSharedCheck_2909_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_roundBudget_2848_);
lean_inc(v_solverTimeBudgetMs_2847_);
lean_inc(v_theoryState_2846_);
lean_inc(v_usedHyps_2844_);
lean_inc(v_hypQueue_2843_);
lean_inc(v_satExpr_2842_);
lean_dec(v___x_2841_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2909_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v_satSolver_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2905_; 
v___x_2852_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_2853_ = lean_ctor_get(v_theoryState_2846_, 3);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_theoryState_2846_);
if (v_isSharedCheck_2905_ == 0)
{
lean_object* v_unused_2906_; lean_object* v_unused_2907_; lean_object* v_unused_2908_; 
v_unused_2906_ = lean_ctor_get(v_theoryState_2846_, 2);
lean_dec(v_unused_2906_);
v_unused_2907_ = lean_ctor_get(v_theoryState_2846_, 1);
lean_dec(v_unused_2907_);
v_unused_2908_ = lean_ctor_get(v_theoryState_2846_, 0);
lean_dec(v_unused_2908_);
v___x_2855_ = v_theoryState_2846_;
v_isShared_2856_ = v_isSharedCheck_2905_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_satSolver_2853_);
lean_dec(v_theoryState_2846_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2905_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_mk_array(v___x_2729_, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2730_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 2, v___x_2852_);
lean_ctor_set(v___x_2855_, 1, v___x_2731_);
lean_ctor_set(v___x_2855_, 0, v___x_2859_);
v___x_2861_ = v___x_2855_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2904_, 2, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2904_, 3, v_satSolver_2853_);
v___x_2861_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2863_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 3, v___x_2861_);
v___x_2863_ = v___x_2850_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_satExpr_2842_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_hypQueue_2843_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_usedHyps_2844_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_solverTimeBudgetMs_2847_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_roundBudget_2848_);
lean_ctor_set_uint8(v_reuseFailAlloc_2903_, sizeof(void*)*6, v_didChange_2845_);
v___x_2863_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_st_ref_put(v___y_2808_, v___x_2863_);
v___x_2865_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_2815_, v___y_2808_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v_goal_2867_; lean_object* v___x_2868_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v_goal_2867_ = lean_ctor_get(v___y_2815_, 0);
lean_inc(v_goal_2867_);
v___x_2868_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_tacticContext_2726_, v_goal_2867_, v_a_2866_, v___y_2806_, v___y_2817_, v___y_2811_, v___y_2807_, v___y_2819_, v___y_2820_, v___y_2812_, v___y_2809_, v___y_2818_, v___y_2810_, v___y_2816_, v___y_2814_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2886_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2886_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2886_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
if (lean_obj_tag(v_a_2869_) == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_dec_ref_known(v_a_2869_, 1);
lean_del_object(v___x_2871_);
v___x_2873_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_2874_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_2873_, v___y_2818_, v___y_2810_, v___y_2816_, v___y_2814_);
return v___x_2874_;
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2885_; 
v_a_2875_ = lean_ctor_get(v_a_2869_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_a_2869_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2877_ = v_a_2869_;
v_isShared_2878_ = v_isSharedCheck_2885_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v_a_2869_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2885_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2880_);
v___x_2882_ = v___x_2871_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
v_a_2887_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2868_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2868_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v_tacticContext_2726_);
v_a_2895_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2865_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2865_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_2910_; 
lean_dec(v___y_2813_);
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_aig_2728_);
lean_dec_ref(v_tacticContext_2726_);
v___x_2910_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_2816_, v___y_2814_);
return v___x_2910_;
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v___y_2813_);
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_aig_2728_);
lean_dec_ref(v_tacticContext_2726_);
v_a_2911_ = lean_ctor_get(v___y_2821_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___y_2821_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___y_2821_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___y_2821_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
v___jp_2919_:
{
lean_object* v___x_2940_; double v___x_2941_; double v___x_2942_; double v___x_2943_; double v___x_2944_; double v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2940_ = lean_io_mono_nanos_now();
v___x_2941_ = lean_float_of_nat(v___y_2920_);
v___x_2942_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2943_ = lean_float_div(v___x_2941_, v___x_2942_);
v___x_2944_ = lean_float_of_nat(v___x_2940_);
v___x_2945_ = lean_float_div(v___x_2944_, v___x_2942_);
v___x_2946_ = lean_box_float(v___x_2943_);
v___x_2947_ = lean_box_float(v___x_2945_);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v_a_2939_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
lean_inc(v___y_2931_);
v___x_2950_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2931_, v___x_2732_, v___x_2733_, v___y_2921_, v___y_2924_, v___y_2926_, v___f_2734_, v___x_2949_, v___y_2933_, v___y_2925_, v___y_2922_, v___y_2936_, v___y_2929_, v___y_2923_, v___y_2937_, v___y_2938_, v___y_2930_, v___y_2927_, v___y_2935_, v___y_2928_, v___y_2934_, v___y_2932_);
v___y_2806_ = v___y_2922_;
v___y_2807_ = v___y_2923_;
v___y_2808_ = v___y_2925_;
v___y_2809_ = v___y_2927_;
v___y_2810_ = v___y_2928_;
v___y_2811_ = v___y_2929_;
v___y_2812_ = v___y_2930_;
v___y_2813_ = v___y_2931_;
v___y_2814_ = v___y_2932_;
v___y_2815_ = v___y_2933_;
v___y_2816_ = v___y_2934_;
v___y_2817_ = v___y_2936_;
v___y_2818_ = v___y_2935_;
v___y_2819_ = v___y_2937_;
v___y_2820_ = v___y_2938_;
v___y_2821_ = v___x_2950_;
goto v___jp_2805_;
}
v___jp_2951_:
{
lean_object* v___x_2972_; double v___x_2973_; double v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2972_ = lean_io_get_num_heartbeats();
v___x_2973_ = lean_float_of_nat(v___y_2967_);
v___x_2974_ = lean_float_of_nat(v___x_2972_);
v___x_2975_ = lean_box_float(v___x_2973_);
v___x_2976_ = lean_box_float(v___x_2974_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2975_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_a_2971_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
lean_inc(v___y_2962_);
v___x_2979_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2962_, v___x_2732_, v___x_2733_, v___y_2952_, v___y_2955_, v___y_2957_, v___f_2734_, v___x_2978_, v___y_2964_, v___y_2956_, v___y_2953_, v___y_2968_, v___y_2960_, v___y_2954_, v___y_2969_, v___y_2970_, v___y_2961_, v___y_2958_, v___y_2966_, v___y_2959_, v___y_2965_, v___y_2963_);
v___y_2806_ = v___y_2953_;
v___y_2807_ = v___y_2954_;
v___y_2808_ = v___y_2956_;
v___y_2809_ = v___y_2958_;
v___y_2810_ = v___y_2959_;
v___y_2811_ = v___y_2960_;
v___y_2812_ = v___y_2961_;
v___y_2813_ = v___y_2962_;
v___y_2814_ = v___y_2963_;
v___y_2815_ = v___y_2964_;
v___y_2816_ = v___y_2965_;
v___y_2817_ = v___y_2968_;
v___y_2818_ = v___y_2966_;
v___y_2819_ = v___y_2969_;
v___y_2820_ = v___y_2970_;
v___y_2821_ = v___x_2979_;
goto v___jp_2805_;
}
v___jp_2980_:
{
lean_object* v___x_2999_; lean_object* v_a_3000_; uint8_t v___x_3001_; 
v___x_2999_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_2992_);
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_2982_, v___x_2735_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_io_mono_nanos_now();
v___x_3003_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2981_, v___y_2993_, v___y_2986_, v___y_2983_, v___y_2994_, v___y_2989_, v___y_2984_, v___y_2997_, v___y_2998_, v___y_2990_, v___y_2987_, v___y_2995_, v___y_2988_, v___y_2996_, v___y_2992_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_3003_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set_tag(v___x_3006_, 1);
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
v___y_2920_ = v___x_3002_;
v___y_2921_ = v___y_2982_;
v___y_2922_ = v___y_2983_;
v___y_2923_ = v___y_2984_;
v___y_2924_ = v___y_2985_;
v___y_2925_ = v___y_2986_;
v___y_2926_ = v_a_3000_;
v___y_2927_ = v___y_2987_;
v___y_2928_ = v___y_2988_;
v___y_2929_ = v___y_2989_;
v___y_2930_ = v___y_2990_;
v___y_2931_ = v___y_2991_;
v___y_2932_ = v___y_2992_;
v___y_2933_ = v___y_2993_;
v___y_2934_ = v___y_2996_;
v___y_2935_ = v___y_2995_;
v___y_2936_ = v___y_2994_;
v___y_2937_ = v___y_2997_;
v___y_2938_ = v___y_2998_;
v_a_2939_ = v___x_3009_;
goto v___jp_2919_;
}
}
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
v_a_3012_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3003_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3003_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 0);
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
v___y_2920_ = v___x_3002_;
v___y_2921_ = v___y_2982_;
v___y_2922_ = v___y_2983_;
v___y_2923_ = v___y_2984_;
v___y_2924_ = v___y_2985_;
v___y_2925_ = v___y_2986_;
v___y_2926_ = v_a_3000_;
v___y_2927_ = v___y_2987_;
v___y_2928_ = v___y_2988_;
v___y_2929_ = v___y_2989_;
v___y_2930_ = v___y_2990_;
v___y_2931_ = v___y_2991_;
v___y_2932_ = v___y_2992_;
v___y_2933_ = v___y_2993_;
v___y_2934_ = v___y_2996_;
v___y_2935_ = v___y_2995_;
v___y_2936_ = v___y_2994_;
v___y_2937_ = v___y_2997_;
v___y_2938_ = v___y_2998_;
v_a_2939_ = v___x_3017_;
goto v___jp_2919_;
}
}
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_io_get_num_heartbeats();
v___x_3021_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2981_, v___y_2993_, v___y_2986_, v___y_2983_, v___y_2994_, v___y_2989_, v___y_2984_, v___y_2997_, v___y_2998_, v___y_2990_, v___y_2987_, v___y_2995_, v___y_2988_, v___y_2996_, v___y_2992_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set_tag(v___x_3024_, 1);
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
v___y_2952_ = v___y_2982_;
v___y_2953_ = v___y_2983_;
v___y_2954_ = v___y_2984_;
v___y_2955_ = v___y_2985_;
v___y_2956_ = v___y_2986_;
v___y_2957_ = v_a_3000_;
v___y_2958_ = v___y_2987_;
v___y_2959_ = v___y_2988_;
v___y_2960_ = v___y_2989_;
v___y_2961_ = v___y_2990_;
v___y_2962_ = v___y_2991_;
v___y_2963_ = v___y_2992_;
v___y_2964_ = v___y_2993_;
v___y_2965_ = v___y_2996_;
v___y_2966_ = v___y_2995_;
v___y_2967_ = v___x_3020_;
v___y_2968_ = v___y_2994_;
v___y_2969_ = v___y_2997_;
v___y_2970_ = v___y_2998_;
v_a_2971_ = v___x_3027_;
goto v___jp_2951_;
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
v_a_3030_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3021_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3021_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 0);
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
v___y_2952_ = v___y_2982_;
v___y_2953_ = v___y_2983_;
v___y_2954_ = v___y_2984_;
v___y_2955_ = v___y_2985_;
v___y_2956_ = v___y_2986_;
v___y_2957_ = v_a_3000_;
v___y_2958_ = v___y_2987_;
v___y_2959_ = v___y_2988_;
v___y_2960_ = v___y_2989_;
v___y_2961_ = v___y_2990_;
v___y_2962_ = v___y_2991_;
v___y_2963_ = v___y_2992_;
v___y_2964_ = v___y_2993_;
v___y_2965_ = v___y_2996_;
v___y_2966_ = v___y_2995_;
v___y_2967_ = v___x_3020_;
v___y_2968_ = v___y_2994_;
v___y_2969_ = v___y_2997_;
v___y_2970_ = v___y_2998_;
v_a_2971_ = v___x_3035_;
goto v___jp_2951_;
}
}
}
}
}
v___jp_3038_:
{
lean_object* v_toCold_3057_; lean_object* v_ref_3058_; lean_object* v___x_3059_; 
v_toCold_3057_ = lean_ctor_get(v___y_3052_, 0);
v_ref_3058_ = lean_ctor_get(v___y_3052_, 2);
lean_inc_ref(v___y_3039_);
v___x_3059_ = l_Lean_Cadical_Solver_assume(v___y_3039_, v___y_3042_, v___y_3056_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_options_3060_; uint8_t v_hasTrace_3061_; 
lean_dec_ref_known(v___x_3059_, 1);
v_options_3060_ = lean_ctor_get(v_toCold_3057_, 2);
v_hasTrace_3061_ = lean_ctor_get_uint8(v_options_3060_, sizeof(void*)*1);
if (v_hasTrace_3061_ == 0)
{
lean_object* v___x_3062_; 
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___x_2733_);
v___x_3062_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_3039_, v___y_3050_, v___y_3043_, v___y_3040_, v___y_3053_, v___y_3046_, v___y_3041_, v___y_3054_, v___y_3055_, v___y_3047_, v___y_3044_, v___y_3051_, v___y_3045_, v___y_3052_, v___y_3049_);
v___y_2806_ = v___y_3040_;
v___y_2807_ = v___y_3041_;
v___y_2808_ = v___y_3043_;
v___y_2809_ = v___y_3044_;
v___y_2810_ = v___y_3045_;
v___y_2811_ = v___y_3046_;
v___y_2812_ = v___y_3047_;
v___y_2813_ = v___y_3048_;
v___y_2814_ = v___y_3049_;
v___y_2815_ = v___y_3050_;
v___y_2816_ = v___y_3052_;
v___y_2817_ = v___y_3053_;
v___y_2818_ = v___y_3051_;
v___y_2819_ = v___y_3054_;
v___y_2820_ = v___y_3055_;
v___y_2821_ = v___x_3062_;
goto v___jp_2805_;
}
else
{
lean_object* v_inheritedTraceOptions_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v_inheritedTraceOptions_3063_ = lean_ctor_get(v_toCold_3057_, 11);
v___x_3064_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_3048_);
v___x_3065_ = l_Lean_Name_append(v___x_3064_, v___y_3048_);
v___x_3066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3063_, v_options_3060_, v___x_3065_);
lean_dec(v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; uint8_t v___x_3068_; 
v___x_3067_ = l_Lean_trace_profiler;
v___x_3068_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3060_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; 
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___x_2733_);
v___x_3069_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_3039_, v___y_3050_, v___y_3043_, v___y_3040_, v___y_3053_, v___y_3046_, v___y_3041_, v___y_3054_, v___y_3055_, v___y_3047_, v___y_3044_, v___y_3051_, v___y_3045_, v___y_3052_, v___y_3049_);
v___y_2806_ = v___y_3040_;
v___y_2807_ = v___y_3041_;
v___y_2808_ = v___y_3043_;
v___y_2809_ = v___y_3044_;
v___y_2810_ = v___y_3045_;
v___y_2811_ = v___y_3046_;
v___y_2812_ = v___y_3047_;
v___y_2813_ = v___y_3048_;
v___y_2814_ = v___y_3049_;
v___y_2815_ = v___y_3050_;
v___y_2816_ = v___y_3052_;
v___y_2817_ = v___y_3053_;
v___y_2818_ = v___y_3051_;
v___y_2819_ = v___y_3054_;
v___y_2820_ = v___y_3055_;
v___y_2821_ = v___x_3069_;
goto v___jp_2805_;
}
else
{
v___y_2981_ = v___y_3039_;
v___y_2982_ = v_options_3060_;
v___y_2983_ = v___y_3040_;
v___y_2984_ = v___y_3041_;
v___y_2985_ = v___x_3066_;
v___y_2986_ = v___y_3043_;
v___y_2987_ = v___y_3044_;
v___y_2988_ = v___y_3045_;
v___y_2989_ = v___y_3046_;
v___y_2990_ = v___y_3047_;
v___y_2991_ = v___y_3048_;
v___y_2992_ = v___y_3049_;
v___y_2993_ = v___y_3050_;
v___y_2994_ = v___y_3053_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v___y_3052_;
v___y_2997_ = v___y_3054_;
v___y_2998_ = v___y_3055_;
goto v___jp_2980_;
}
}
else
{
v___y_2981_ = v___y_3039_;
v___y_2982_ = v_options_3060_;
v___y_2983_ = v___y_3040_;
v___y_2984_ = v___y_3041_;
v___y_2985_ = v___x_3066_;
v___y_2986_ = v___y_3043_;
v___y_2987_ = v___y_3044_;
v___y_2988_ = v___y_3045_;
v___y_2989_ = v___y_3046_;
v___y_2990_ = v___y_3047_;
v___y_2991_ = v___y_3048_;
v___y_2992_ = v___y_3049_;
v___y_2993_ = v___y_3050_;
v___y_2994_ = v___y_3053_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v___y_3052_;
v___y_2997_ = v___y_3054_;
v___y_2998_ = v___y_3055_;
goto v___jp_2980_;
}
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3039_);
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_aig_2728_);
lean_dec_ref(v_tacticContext_2726_);
v_a_3070_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3072_ = v___x_3059_;
v_isShared_3073_ = v_isSharedCheck_3081_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3059_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3081_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3074_ = lean_io_error_to_string(v_a_3070_);
v___x_3075_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
v___x_3076_ = l_Lean_MessageData_ofFormat(v___x_3075_);
lean_inc(v_ref_3058_);
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v_ref_3058_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3077_);
v___x_3079_ = v___x_3072_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
v___jp_3082_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v_theoryState_3103_; lean_object* v_satExpr_3104_; lean_object* v_hypQueue_3105_; lean_object* v_usedHyps_3106_; uint8_t v_didChange_3107_; lean_object* v_solverTimeBudgetMs_3108_; lean_object* v_roundBudget_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3152_; 
lean_inc_ref(v_aig_2728_);
v___x_3101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3101_, 0, v_aig_2728_);
lean_ctor_set(v___x_3101_, 1, v_cache_2736_);
lean_ctor_set(v___x_3101_, 2, v___y_3084_);
v___x_3102_ = lean_st_ref_take(v___y_3088_);
v_theoryState_3103_ = lean_ctor_get(v___x_3102_, 3);
v_satExpr_3104_ = lean_ctor_get(v___x_3102_, 0);
v_hypQueue_3105_ = lean_ctor_get(v___x_3102_, 1);
v_usedHyps_3106_ = lean_ctor_get(v___x_3102_, 2);
v_didChange_3107_ = lean_ctor_get_uint8(v___x_3102_, sizeof(void*)*6);
v_solverTimeBudgetMs_3108_ = lean_ctor_get(v___x_3102_, 4);
v_roundBudget_3109_ = lean_ctor_get(v___x_3102_, 5);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3111_ = v___x_3102_;
v_isShared_3112_ = v_isSharedCheck_3152_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_roundBudget_3109_);
lean_inc(v_solverTimeBudgetMs_3108_);
lean_inc(v_theoryState_3103_);
lean_inc(v_usedHyps_3106_);
lean_inc(v_hypQueue_3105_);
lean_inc(v_satExpr_3104_);
lean_dec(v___x_3102_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3152_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v_funState_3113_; lean_object* v_preprocessCaches_3114_; lean_object* v_satSolver_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3150_; 
v_funState_3113_ = lean_ctor_get(v_theoryState_3103_, 0);
v_preprocessCaches_3114_ = lean_ctor_get(v_theoryState_3103_, 2);
v_satSolver_3115_ = lean_ctor_get(v_theoryState_3103_, 3);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_theoryState_3103_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v_theoryState_3103_, 1);
lean_dec(v_unused_3151_);
v___x_3117_ = v_theoryState_3103_;
v_isShared_3118_ = v_isSharedCheck_3150_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_satSolver_3115_);
lean_inc(v_preprocessCaches_3114_);
lean_inc(v_funState_3113_);
lean_dec(v_theoryState_3103_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3150_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3101_);
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_funState_3113_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_preprocessCaches_3114_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v_satSolver_3115_);
v___x_3120_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3122_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 3, v___x_3120_);
v___x_3122_ = v___x_3111_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_satExpr_3104_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_hypQueue_3105_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_usedHyps_3106_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v_solverTimeBudgetMs_3108_);
lean_ctor_set(v_reuseFailAlloc_3148_, 5, v_roundBudget_3109_);
lean_ctor_set_uint8(v_reuseFailAlloc_3148_, sizeof(void*)*6, v_didChange_3107_);
v___x_3122_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = lean_st_ref_put(v___y_3088_, v___x_3122_);
v___x_3124_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_3086_, v___y_3083_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v___x_3125_; 
lean_dec_ref_known(v___x_3124_, 1);
v___x_3125_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_3088_);
if (lean_obj_tag(v___x_3125_) == 0)
{
uint8_t v_invert_3126_; 
v_invert_3126_ = lean_ctor_get_uint8(v_ref_2737_, sizeof(void*)*1);
if (v_invert_3126_ == 0)
{
lean_object* v_a_3127_; lean_object* v_gate_3128_; 
v_a_3127_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3125_, 1);
v_gate_3128_ = lean_ctor_get(v_ref_2737_, 0);
v___y_3039_ = v_a_3127_;
v___y_3040_ = v___y_3089_;
v___y_3041_ = v___y_3092_;
v___y_3042_ = v_gate_3128_;
v___y_3043_ = v___y_3088_;
v___y_3044_ = v___y_3096_;
v___y_3045_ = v___y_3098_;
v___y_3046_ = v___y_3091_;
v___y_3047_ = v___y_3095_;
v___y_3048_ = v___y_3085_;
v___y_3049_ = v___y_3100_;
v___y_3050_ = v___y_3087_;
v___y_3051_ = v___y_3097_;
v___y_3052_ = v___y_3099_;
v___y_3053_ = v___y_3090_;
v___y_3054_ = v___y_3093_;
v___y_3055_ = v___y_3094_;
v___y_3056_ = v___x_2732_;
goto v___jp_3038_;
}
else
{
lean_object* v_a_3129_; lean_object* v_gate_3130_; uint8_t v___x_3131_; 
v_a_3129_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3125_, 1);
v_gate_3130_ = lean_ctor_get(v_ref_2737_, 0);
v___x_3131_ = 0;
v___y_3039_ = v_a_3129_;
v___y_3040_ = v___y_3089_;
v___y_3041_ = v___y_3092_;
v___y_3042_ = v_gate_3130_;
v___y_3043_ = v___y_3088_;
v___y_3044_ = v___y_3096_;
v___y_3045_ = v___y_3098_;
v___y_3046_ = v___y_3091_;
v___y_3047_ = v___y_3095_;
v___y_3048_ = v___y_3085_;
v___y_3049_ = v___y_3100_;
v___y_3050_ = v___y_3087_;
v___y_3051_ = v___y_3097_;
v___y_3052_ = v___y_3099_;
v___y_3053_ = v___y_3090_;
v___y_3054_ = v___y_3093_;
v___y_3055_ = v___y_3094_;
v___y_3056_ = v___x_3131_;
goto v___jp_3038_;
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v___y_3085_);
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_aig_2728_);
lean_dec_ref(v_tacticContext_2726_);
v_a_3132_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3125_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3125_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v___y_3085_);
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_aig_2728_);
lean_dec_ref(v_tacticContext_2726_);
v_a_3140_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3124_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3124_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
}
}
}
v___jp_3153_:
{
if (lean_obj_tag(v___y_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v_toCold_3172_; lean_object* v_options_3173_; uint8_t v_hasTrace_3174_; 
v_a_3171_ = lean_ctor_get(v___y_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___y_3170_, 1);
v_toCold_3172_ = lean_ctor_get(v___y_3168_, 0);
v_options_3173_ = lean_ctor_get(v_toCold_3172_, 2);
v_hasTrace_3174_ = lean_ctor_get_uint8(v_options_3173_, sizeof(void*)*1);
if (v_hasTrace_3174_ == 0)
{
lean_object* v_cnf_3175_; 
lean_dec(v_cls_2738_);
v_cnf_3175_ = lean_ctor_get(v_a_3171_, 0);
lean_inc_ref(v_cnf_3175_);
v___y_3083_ = v_cnf_3175_;
v___y_3084_ = v_a_3171_;
v___y_3085_ = v___y_3165_;
v___y_3086_ = v___y_3159_;
v___y_3087_ = v___y_3163_;
v___y_3088_ = v___y_3169_;
v___y_3089_ = v___y_3166_;
v___y_3090_ = v___y_3164_;
v___y_3091_ = v___y_3154_;
v___y_3092_ = v___y_3160_;
v___y_3093_ = v___y_3158_;
v___y_3094_ = v___y_3161_;
v___y_3095_ = v___y_3167_;
v___y_3096_ = v___y_3162_;
v___y_3097_ = v___y_3157_;
v___y_3098_ = v___y_3156_;
v___y_3099_ = v___y_3168_;
v___y_3100_ = v___y_3155_;
goto v___jp_3082_;
}
else
{
lean_object* v_cnf_3176_; lean_object* v_inheritedTraceOptions_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v_cnf_3176_ = lean_ctor_get(v_a_3171_, 0);
lean_inc_ref(v_cnf_3176_);
v_inheritedTraceOptions_3177_ = lean_ctor_get(v_toCold_3172_, 11);
v___x_3178_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v_cls_2738_);
v___x_3179_ = l_Lean_Name_append(v___x_3178_, v_cls_2738_);
v___x_3180_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3177_, v_options_3173_, v___x_3179_);
lean_dec(v___x_3179_);
if (v___x_3180_ == 0)
{
lean_dec(v_cls_2738_);
v___y_3083_ = v_cnf_3176_;
v___y_3084_ = v_a_3171_;
v___y_3085_ = v___y_3165_;
v___y_3086_ = v___y_3159_;
v___y_3087_ = v___y_3163_;
v___y_3088_ = v___y_3169_;
v___y_3089_ = v___y_3166_;
v___y_3090_ = v___y_3164_;
v___y_3091_ = v___y_3154_;
v___y_3092_ = v___y_3160_;
v___y_3093_ = v___y_3158_;
v___y_3094_ = v___y_3161_;
v___y_3095_ = v___y_3167_;
v___y_3096_ = v___y_3162_;
v___y_3097_ = v___y_3157_;
v___y_3098_ = v___y_3156_;
v___y_3099_ = v___y_3168_;
v___y_3100_ = v___y_3155_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3181_ = lean_array_get_size(v_cnf_3176_);
v___x_3182_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_3183_ = l_Nat_reprFast(v___x_3181_);
v___x_3184_ = lean_string_append(v___x_3182_, v___x_3183_);
lean_dec_ref(v___x_3183_);
v___x_3185_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_3186_ = lean_string_append(v___x_3184_, v___x_3185_);
v___x_3187_ = lean_nat_sub(v___x_3181_, v___y_3159_);
v___x_3188_ = l_Nat_reprFast(v___x_3187_);
v___x_3189_ = lean_string_append(v___x_3186_, v___x_3188_);
lean_dec_ref(v___x_3188_);
v___x_3190_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_3191_ = lean_string_append(v___x_3189_, v___x_3190_);
v___x_3192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
v___x_3193_ = l_Lean_MessageData_ofFormat(v___x_3192_);
v___x_3194_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_2738_, v___x_3193_, v___y_3157_, v___y_3156_, v___y_3168_, v___y_3155_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_dec_ref_known(v___x_3194_, 1);
v___y_3083_ = v_cnf_3176_;
v___y_3084_ = v_a_3171_;
v___y_3085_ = v___y_3165_;
v___y_3086_ = v___y_3159_;
v___y_3087_ = v___y_3163_;
v___y_3088_ = v___y_3169_;
v___y_3089_ = v___y_3166_;
v___y_3090_ = v___y_3164_;
v___y_3091_ = v___y_3154_;
v___y_3092_ = v___y_3160_;
v___y_3093_ = v___y_3158_;
v___y_3094_ = v___y_3161_;
v___y_3095_ = v___y_3167_;
v___y_3096_ = v___y_3162_;
v___y_3097_ = v___y_3157_;
v___y_3098_ = v___y_3156_;
v___y_3099_ = v___y_3168_;
v___y_3100_ = v___y_3155_;
goto v___jp_3082_;
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec_ref(v_cnf_3176_);
lean_dec(v_a_3171_);
lean_dec(v___y_3165_);
lean_dec(v___y_3159_);
lean_dec_ref(v_cache_2736_);
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_aig_2728_);
lean_dec_ref(v_tacticContext_2726_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v___y_3165_);
lean_dec(v___y_3159_);
lean_dec(v_cls_2738_);
lean_dec_ref(v_cache_2736_);
lean_dec_ref(v___f_2734_);
lean_dec_ref(v___x_2733_);
lean_dec_ref(v___x_2731_);
lean_dec(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec_ref(v_aig_2728_);
lean_dec_ref(v_tacticContext_2726_);
v_a_3203_ = lean_ctor_get(v___y_3170_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___y_3170_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___y_3170_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___y_3170_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
v___jp_3211_:
{
lean_object* v___x_3233_; double v___x_3234_; double v___x_3235_; double v___x_3236_; double v___x_3237_; double v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3233_ = lean_io_mono_nanos_now();
v___x_3234_ = lean_float_of_nat(v___y_3216_);
v___x_3235_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_3236_ = lean_float_div(v___x_3234_, v___x_3235_);
v___x_3237_ = lean_float_of_nat(v___x_3233_);
v___x_3238_ = lean_float_div(v___x_3237_, v___x_3235_);
v___x_3239_ = lean_box_float(v___x_3236_);
v___x_3240_ = lean_box_float(v___x_3238_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_a_3232_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
lean_inc_ref(v___x_2733_);
lean_inc(v___y_3227_);
v___x_3243_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_3227_, v___x_2732_, v___x_2733_, v___y_3215_, v___y_3220_, v___y_3213_, v___f_2739_, v___x_3242_, v___y_3225_, v___y_3231_, v___y_3228_, v___y_3226_, v___y_3212_, v___y_3222_, v___y_3219_, v___y_3223_, v___y_3229_, v___y_3224_, v___y_3218_, v___y_3217_, v___y_3230_, v___y_3214_);
v___y_3154_ = v___y_3212_;
v___y_3155_ = v___y_3214_;
v___y_3156_ = v___y_3217_;
v___y_3157_ = v___y_3218_;
v___y_3158_ = v___y_3219_;
v___y_3159_ = v___y_3221_;
v___y_3160_ = v___y_3222_;
v___y_3161_ = v___y_3223_;
v___y_3162_ = v___y_3224_;
v___y_3163_ = v___y_3225_;
v___y_3164_ = v___y_3226_;
v___y_3165_ = v___y_3227_;
v___y_3166_ = v___y_3228_;
v___y_3167_ = v___y_3229_;
v___y_3168_ = v___y_3230_;
v___y_3169_ = v___y_3231_;
v___y_3170_ = v___x_3243_;
goto v___jp_3153_;
}
v___jp_3244_:
{
lean_object* v___x_3266_; double v___x_3267_; double v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3266_ = lean_io_get_num_heartbeats();
v___x_3267_ = lean_float_of_nat(v___y_3245_);
v___x_3268_ = lean_float_of_nat(v___x_3266_);
v___x_3269_ = lean_box_float(v___x_3267_);
v___x_3270_ = lean_box_float(v___x_3268_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_a_3265_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
lean_inc_ref(v___x_2733_);
lean_inc(v___y_3260_);
v___x_3273_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_3260_, v___x_2732_, v___x_2733_, v___y_3249_, v___y_3253_, v___y_3247_, v___f_2739_, v___x_3272_, v___y_3258_, v___y_3264_, v___y_3261_, v___y_3259_, v___y_3246_, v___y_3255_, v___y_3252_, v___y_3256_, v___y_3262_, v___y_3257_, v___y_3251_, v___y_3250_, v___y_3263_, v___y_3248_);
v___y_3154_ = v___y_3246_;
v___y_3155_ = v___y_3248_;
v___y_3156_ = v___y_3250_;
v___y_3157_ = v___y_3251_;
v___y_3158_ = v___y_3252_;
v___y_3159_ = v___y_3254_;
v___y_3160_ = v___y_3255_;
v___y_3161_ = v___y_3256_;
v___y_3162_ = v___y_3257_;
v___y_3163_ = v___y_3258_;
v___y_3164_ = v___y_3259_;
v___y_3165_ = v___y_3260_;
v___y_3166_ = v___y_3261_;
v___y_3167_ = v___y_3262_;
v___y_3168_ = v___y_3263_;
v___y_3169_ = v___y_3264_;
v___y_3170_ = v___x_3273_;
goto v___jp_3153_;
}
v___jp_3274_:
{
lean_object* v___x_3295_; lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3349_; 
v___x_3295_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_3276_);
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3349_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3349_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
uint8_t v___x_3300_; 
v___x_3300_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_3277_, v___x_2735_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_io_mono_nanos_now();
v___x_3302_ = l_IO_lazyPure___redArg(v___y_3285_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_del_object(v___x_3298_);
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 1);
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
v___y_3212_ = v___y_3275_;
v___y_3213_ = v_a_3296_;
v___y_3214_ = v___y_3276_;
v___y_3215_ = v___y_3277_;
v___y_3216_ = v___x_3301_;
v___y_3217_ = v___y_3279_;
v___y_3218_ = v___y_3278_;
v___y_3219_ = v___y_3280_;
v___y_3220_ = v___y_3281_;
v___y_3221_ = v___y_3282_;
v___y_3222_ = v___y_3283_;
v___y_3223_ = v___y_3284_;
v___y_3224_ = v___y_3286_;
v___y_3225_ = v___y_3287_;
v___y_3226_ = v___y_3288_;
v___y_3227_ = v___y_3290_;
v___y_3228_ = v___y_3291_;
v___y_3229_ = v___y_3292_;
v___y_3230_ = v___y_3293_;
v___y_3231_ = v___y_3294_;
v_a_3232_ = v___x_3308_;
goto v___jp_3211_;
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3324_; 
v_a_3311_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3313_ = v___x_3302_;
v_isShared_3314_ = v_isSharedCheck_3324_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3302_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3324_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3315_ = lean_io_error_to_string(v_a_3311_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set_tag(v___x_3313_, 3);
lean_ctor_set(v___x_3313_, 0, v___x_3315_);
v___x_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3321_; 
v___x_3318_ = l_Lean_MessageData_ofFormat(v___x_3317_);
lean_inc(v___y_3289_);
v___x_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___y_3289_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v___x_3319_);
v___x_3321_ = v___x_3298_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
v___y_3212_ = v___y_3275_;
v___y_3213_ = v_a_3296_;
v___y_3214_ = v___y_3276_;
v___y_3215_ = v___y_3277_;
v___y_3216_ = v___x_3301_;
v___y_3217_ = v___y_3279_;
v___y_3218_ = v___y_3278_;
v___y_3219_ = v___y_3280_;
v___y_3220_ = v___y_3281_;
v___y_3221_ = v___y_3282_;
v___y_3222_ = v___y_3283_;
v___y_3223_ = v___y_3284_;
v___y_3224_ = v___y_3286_;
v___y_3225_ = v___y_3287_;
v___y_3226_ = v___y_3288_;
v___y_3227_ = v___y_3290_;
v___y_3228_ = v___y_3291_;
v___y_3229_ = v___y_3292_;
v___y_3230_ = v___y_3293_;
v___y_3231_ = v___y_3294_;
v_a_3232_ = v___x_3321_;
goto v___jp_3211_;
}
}
}
}
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_io_get_num_heartbeats();
v___x_3326_ = l_IO_lazyPure___redArg(v___y_3285_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_del_object(v___x_3298_);
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set_tag(v___x_3329_, 1);
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
v___y_3245_ = v___x_3325_;
v___y_3246_ = v___y_3275_;
v___y_3247_ = v_a_3296_;
v___y_3248_ = v___y_3276_;
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3279_;
v___y_3251_ = v___y_3278_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___y_3281_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3283_;
v___y_3256_ = v___y_3284_;
v___y_3257_ = v___y_3286_;
v___y_3258_ = v___y_3287_;
v___y_3259_ = v___y_3288_;
v___y_3260_ = v___y_3290_;
v___y_3261_ = v___y_3291_;
v___y_3262_ = v___y_3292_;
v___y_3263_ = v___y_3293_;
v___y_3264_ = v___y_3294_;
v_a_3265_ = v___x_3332_;
goto v___jp_3244_;
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3348_; 
v_a_3335_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3337_ = v___x_3326_;
v_isShared_3338_ = v_isSharedCheck_3348_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3326_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3348_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3339_ = lean_io_error_to_string(v_a_3335_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set_tag(v___x_3337_, 3);
lean_ctor_set(v___x_3337_, 0, v___x_3339_);
v___x_3341_ = v___x_3337_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3342_ = l_Lean_MessageData_ofFormat(v___x_3341_);
lean_inc(v___y_3289_);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___y_3289_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v___x_3343_);
v___x_3345_ = v___x_3298_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
v___y_3245_ = v___x_3325_;
v___y_3246_ = v___y_3275_;
v___y_3247_ = v_a_3296_;
v___y_3248_ = v___y_3276_;
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3279_;
v___y_3251_ = v___y_3278_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___y_3281_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___y_3283_;
v___y_3256_ = v___y_3284_;
v___y_3257_ = v___y_3286_;
v___y_3258_ = v___y_3287_;
v___y_3259_ = v___y_3288_;
v___y_3260_ = v___y_3290_;
v___y_3261_ = v___y_3291_;
v___y_3262_ = v___y_3292_;
v___y_3263_ = v___y_3293_;
v___y_3264_ = v___y_3294_;
v_a_3265_ = v___x_3345_;
goto v___jp_3244_;
}
}
}
}
}
}
}
v___jp_3350_:
{
lean_object* v_toCold_3365_; lean_object* v_options_3366_; lean_object* v_cnf_3367_; lean_object* v_ref_3368_; lean_object* v_inheritedTraceOptions_3369_; uint8_t v_hasTrace_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___f_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_toCold_3365_ = lean_ctor_get(v___y_3363_, 0);
v_options_3366_ = lean_ctor_get(v_toCold_3365_, 2);
v_cnf_3367_ = lean_ctor_get(v_cnfCache_2740_, 0);
v_ref_3368_ = lean_ctor_get(v___y_3363_, 2);
v_inheritedTraceOptions_3369_ = lean_ctor_get(v_toCold_3365_, 11);
v_hasTrace_3370_ = lean_ctor_get_uint8(v_options_3366_, sizeof(void*)*1);
v___x_3371_ = lean_array_get_size(v_cnf_3367_);
v___x_3372_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_3373_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig_2728_, v_cnfCache_2740_);
v___f_3374_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3374_, 0, v___x_2741_);
lean_closure_set(v___f_3374_, 1, v___x_3372_);
lean_closure_set(v___f_3374_, 2, v_result_2742_);
lean_closure_set(v___f_3374_, 3, v___x_3373_);
v___x_3375_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13));
v___x_3376_ = l_Lean_Name_mkStr3(v___x_2743_, v___x_2744_, v___x_3375_);
if (v_hasTrace_3370_ == 0)
{
lean_object* v___x_3377_; 
lean_dec_ref(v___f_2739_);
v___x_3377_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_3374_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
v___y_3154_ = v___y_3355_;
v___y_3155_ = v___y_3364_;
v___y_3156_ = v___y_3362_;
v___y_3157_ = v___y_3361_;
v___y_3158_ = v___y_3357_;
v___y_3159_ = v___x_3371_;
v___y_3160_ = v___y_3356_;
v___y_3161_ = v___y_3358_;
v___y_3162_ = v___y_3360_;
v___y_3163_ = v___y_3351_;
v___y_3164_ = v___y_3354_;
v___y_3165_ = v___x_3376_;
v___y_3166_ = v___y_3353_;
v___y_3167_ = v___y_3359_;
v___y_3168_ = v___y_3363_;
v___y_3169_ = v___y_3352_;
v___y_3170_ = v___x_3377_;
goto v___jp_3153_;
}
else
{
lean_object* v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3378_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___x_3376_);
v___x_3379_ = l_Lean_Name_append(v___x_3378_, v___x_3376_);
v___x_3380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3369_, v_options_3366_, v___x_3379_);
lean_dec(v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3381_ = l_Lean_trace_profiler;
v___x_3382_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3366_, v___x_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; 
lean_dec_ref(v___f_2739_);
v___x_3383_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_3374_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
v___y_3154_ = v___y_3355_;
v___y_3155_ = v___y_3364_;
v___y_3156_ = v___y_3362_;
v___y_3157_ = v___y_3361_;
v___y_3158_ = v___y_3357_;
v___y_3159_ = v___x_3371_;
v___y_3160_ = v___y_3356_;
v___y_3161_ = v___y_3358_;
v___y_3162_ = v___y_3360_;
v___y_3163_ = v___y_3351_;
v___y_3164_ = v___y_3354_;
v___y_3165_ = v___x_3376_;
v___y_3166_ = v___y_3353_;
v___y_3167_ = v___y_3359_;
v___y_3168_ = v___y_3363_;
v___y_3169_ = v___y_3352_;
v___y_3170_ = v___x_3383_;
goto v___jp_3153_;
}
else
{
v___y_3275_ = v___y_3355_;
v___y_3276_ = v___y_3364_;
v___y_3277_ = v_options_3366_;
v___y_3278_ = v___y_3361_;
v___y_3279_ = v___y_3362_;
v___y_3280_ = v___y_3357_;
v___y_3281_ = v___x_3380_;
v___y_3282_ = v___x_3371_;
v___y_3283_ = v___y_3356_;
v___y_3284_ = v___y_3358_;
v___y_3285_ = v___f_3374_;
v___y_3286_ = v___y_3360_;
v___y_3287_ = v___y_3351_;
v___y_3288_ = v___y_3354_;
v___y_3289_ = v_ref_3368_;
v___y_3290_ = v___x_3376_;
v___y_3291_ = v___y_3353_;
v___y_3292_ = v___y_3359_;
v___y_3293_ = v___y_3363_;
v___y_3294_ = v___y_3352_;
goto v___jp_3274_;
}
}
else
{
v___y_3275_ = v___y_3355_;
v___y_3276_ = v___y_3364_;
v___y_3277_ = v_options_3366_;
v___y_3278_ = v___y_3361_;
v___y_3279_ = v___y_3362_;
v___y_3280_ = v___y_3357_;
v___y_3281_ = v___x_3380_;
v___y_3282_ = v___x_3371_;
v___y_3283_ = v___y_3356_;
v___y_3284_ = v___y_3358_;
v___y_3285_ = v___f_3374_;
v___y_3286_ = v___y_3360_;
v___y_3287_ = v___y_3351_;
v___y_3288_ = v___y_3354_;
v___y_3289_ = v_ref_3368_;
v___y_3290_ = v___x_3376_;
v___y_3291_ = v___y_3353_;
v___y_3292_ = v___y_3359_;
v___y_3293_ = v___y_3363_;
v___y_3294_ = v___y_3352_;
goto v___jp_3274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11___boxed(lean_object** _args){
lean_object* v_tacticContext_3402_ = _args[0];
lean_object* v___x_3403_ = _args[1];
lean_object* v_aig_3404_ = _args[2];
lean_object* v___x_3405_ = _args[3];
lean_object* v___x_3406_ = _args[4];
lean_object* v___x_3407_ = _args[5];
lean_object* v___x_3408_ = _args[6];
lean_object* v___x_3409_ = _args[7];
lean_object* v___f_3410_ = _args[8];
lean_object* v___x_3411_ = _args[9];
lean_object* v_cache_3412_ = _args[10];
lean_object* v_ref_3413_ = _args[11];
lean_object* v_cls_3414_ = _args[12];
lean_object* v___f_3415_ = _args[13];
lean_object* v_cnfCache_3416_ = _args[14];
lean_object* v___x_3417_ = _args[15];
lean_object* v_result_3418_ = _args[16];
lean_object* v___x_3419_ = _args[17];
lean_object* v___x_3420_ = _args[18];
lean_object* v_____r_3421_ = _args[19];
lean_object* v___y_3422_ = _args[20];
lean_object* v___y_3423_ = _args[21];
lean_object* v___y_3424_ = _args[22];
lean_object* v___y_3425_ = _args[23];
lean_object* v___y_3426_ = _args[24];
lean_object* v___y_3427_ = _args[25];
lean_object* v___y_3428_ = _args[26];
lean_object* v___y_3429_ = _args[27];
lean_object* v___y_3430_ = _args[28];
lean_object* v___y_3431_ = _args[29];
lean_object* v___y_3432_ = _args[30];
lean_object* v___y_3433_ = _args[31];
lean_object* v___y_3434_ = _args[32];
lean_object* v___y_3435_ = _args[33];
lean_object* v___y_3436_ = _args[34];
_start:
{
uint8_t v___x_1194189__boxed_3437_; lean_object* v_res_3438_; 
v___x_1194189__boxed_3437_ = lean_unbox(v___x_3408_);
v_res_3438_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v_tacticContext_3402_, v___x_3403_, v_aig_3404_, v___x_3405_, v___x_3406_, v___x_3407_, v___x_1194189__boxed_3437_, v___x_3409_, v___f_3410_, v___x_3411_, v_cache_3412_, v_ref_3413_, v_cls_3414_, v___f_3415_, v_cnfCache_3416_, v___x_3417_, v_result_3418_, v___x_3419_, v___x_3420_, v_____r_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v_ref_3413_);
lean_dec_ref(v___x_3411_);
lean_dec(v___x_3403_);
return v_res_3438_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(lean_object* v_e_3439_){
_start:
{
if (lean_obj_tag(v_e_3439_) == 0)
{
uint8_t v___x_3440_; 
v___x_3440_ = 2;
return v___x_3440_;
}
else
{
uint8_t v___x_3441_; 
v___x_3441_ = 0;
return v___x_3441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20___boxed(lean_object* v_e_3442_){
_start:
{
uint8_t v_res_3443_; lean_object* v_r_3444_; 
v_res_3443_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(v_e_3442_);
lean_dec_ref(v_e_3442_);
v_r_3444_ = lean_box(v_res_3443_);
return v_r_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(lean_object* v_cls_3445_, uint8_t v_collapsed_3446_, lean_object* v_tag_3447_, lean_object* v_opts_3448_, uint8_t v_clsEnabled_3449_, lean_object* v_oldTraces_3450_, lean_object* v_msg_3451_, lean_object* v_resStartStop_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_fst_3468_; lean_object* v_snd_3469_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v_data_3473_; lean_object* v_fst_3484_; lean_object* v_snd_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; lean_object* v___y_3489_; lean_object* v_a_3490_; uint8_t v___y_3505_; double v___y_3537_; 
v_fst_3468_ = lean_ctor_get(v_resStartStop_3452_, 0);
lean_inc(v_fst_3468_);
v_snd_3469_ = lean_ctor_get(v_resStartStop_3452_, 1);
lean_inc(v_snd_3469_);
lean_dec_ref(v_resStartStop_3452_);
v_fst_3484_ = lean_ctor_get(v_snd_3469_, 0);
lean_inc(v_fst_3484_);
v_snd_3485_ = lean_ctor_get(v_snd_3469_, 1);
lean_inc(v_snd_3485_);
lean_dec(v_snd_3469_);
v___x_3486_ = l_Lean_trace_profiler;
v___x_3487_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3448_, v___x_3486_);
if (v___x_3487_ == 0)
{
v___y_3505_ = v___x_3487_;
goto v___jp_3504_;
}
else
{
lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3542_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3543_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3448_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; double v___x_3546_; double v___x_3547_; double v___x_3548_; 
v___x_3544_ = l_Lean_trace_profiler_threshold;
v___x_3545_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3448_, v___x_3544_);
v___x_3546_ = lean_float_of_nat(v___x_3545_);
v___x_3547_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_3548_ = lean_float_div(v___x_3546_, v___x_3547_);
v___y_3537_ = v___x_3548_;
goto v___jp_3536_;
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; double v___x_3551_; 
v___x_3549_ = l_Lean_trace_profiler_threshold;
v___x_3550_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3448_, v___x_3549_);
v___x_3551_ = lean_float_of_nat(v___x_3550_);
v___y_3537_ = v___x_3551_;
goto v___jp_3536_;
}
}
v___jp_3470_:
{
lean_object* v___x_3474_; 
lean_inc(v___y_3472_);
v___x_3474_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_3450_, v_data_3473_, v___y_3472_, v___y_3471_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v___x_3475_; 
lean_dec_ref_known(v___x_3474_, 1);
v___x_3475_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3468_);
return v___x_3475_;
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec(v_fst_3468_);
v_a_3476_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3474_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3474_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
v___jp_3488_:
{
uint8_t v_result_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; double v___x_3494_; lean_object* v_data_3495_; 
v_result_3491_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(v_fst_3468_);
v___x_3492_ = lean_box(v_result_3491_);
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
v___x_3494_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_3447_);
lean_inc_ref(v___x_3493_);
lean_inc(v_cls_3445_);
v_data_3495_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3495_, 0, v_cls_3445_);
lean_ctor_set(v_data_3495_, 1, v___x_3493_);
lean_ctor_set(v_data_3495_, 2, v_tag_3447_);
lean_ctor_set_float(v_data_3495_, sizeof(void*)*3, v___x_3494_);
lean_ctor_set_float(v_data_3495_, sizeof(void*)*3 + 8, v___x_3494_);
lean_ctor_set_uint8(v_data_3495_, sizeof(void*)*3 + 16, v_collapsed_3446_);
if (v___x_3487_ == 0)
{
lean_dec_ref_known(v___x_3493_, 1);
lean_dec(v_snd_3485_);
lean_dec(v_fst_3484_);
lean_dec_ref(v_tag_3447_);
lean_dec(v_cls_3445_);
v___y_3471_ = v_a_3490_;
v___y_3472_ = v___y_3489_;
v_data_3473_ = v_data_3495_;
goto v___jp_3470_;
}
else
{
lean_object* v_data_3496_; double v___x_3497_; double v___x_3498_; 
lean_dec_ref_known(v_data_3495_, 3);
v_data_3496_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3496_, 0, v_cls_3445_);
lean_ctor_set(v_data_3496_, 1, v___x_3493_);
lean_ctor_set(v_data_3496_, 2, v_tag_3447_);
v___x_3497_ = lean_unbox_float(v_fst_3484_);
lean_dec(v_fst_3484_);
lean_ctor_set_float(v_data_3496_, sizeof(void*)*3, v___x_3497_);
v___x_3498_ = lean_unbox_float(v_snd_3485_);
lean_dec(v_snd_3485_);
lean_ctor_set_float(v_data_3496_, sizeof(void*)*3 + 8, v___x_3498_);
lean_ctor_set_uint8(v_data_3496_, sizeof(void*)*3 + 16, v_collapsed_3446_);
v___y_3471_ = v_a_3490_;
v___y_3472_ = v___y_3489_;
v_data_3473_ = v_data_3496_;
goto v___jp_3470_;
}
}
v___jp_3499_:
{
lean_object* v_ref_3500_; lean_object* v___x_3501_; 
v_ref_3500_ = lean_ctor_get(v___y_3465_, 2);
lean_inc(v___y_3466_);
lean_inc_ref(v___y_3465_);
lean_inc(v___y_3464_);
lean_inc_ref(v___y_3463_);
lean_inc(v___y_3462_);
lean_inc_ref(v___y_3461_);
lean_inc(v___y_3460_);
lean_inc_ref(v___y_3459_);
lean_inc(v___y_3458_);
lean_inc(v___y_3457_);
lean_inc_ref(v___y_3456_);
lean_inc(v___y_3455_);
lean_inc(v___y_3454_);
lean_inc_ref(v___y_3453_);
lean_inc(v_fst_3468_);
v___x_3501_ = lean_apply_16(v_msg_3451_, v_fst_3468_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, lean_box(0));
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___y_3489_ = v_ref_3500_;
v_a_3490_ = v_a_3502_;
goto v___jp_3488_;
}
else
{
lean_object* v___x_3503_; 
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_3489_ = v_ref_3500_;
v_a_3490_ = v___x_3503_;
goto v___jp_3488_;
}
}
v___jp_3504_:
{
if (v_clsEnabled_3449_ == 0)
{
if (v___y_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v_traceState_3507_; lean_object* v_env_3508_; lean_object* v_nextMacroScope_3509_; lean_object* v_ngen_3510_; lean_object* v_auxDeclNGen_3511_; lean_object* v_cache_3512_; lean_object* v_recordedDeps_3513_; lean_object* v_messages_3514_; lean_object* v_infoState_3515_; lean_object* v_snapshotTasks_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v_snd_3485_);
lean_dec(v_fst_3484_);
lean_dec_ref(v_msg_3451_);
lean_dec_ref(v_tag_3447_);
lean_dec(v_cls_3445_);
v___x_3506_ = lean_st_ref_take(v___y_3466_);
v_traceState_3507_ = lean_ctor_get(v___x_3506_, 4);
v_env_3508_ = lean_ctor_get(v___x_3506_, 0);
v_nextMacroScope_3509_ = lean_ctor_get(v___x_3506_, 1);
v_ngen_3510_ = lean_ctor_get(v___x_3506_, 2);
v_auxDeclNGen_3511_ = lean_ctor_get(v___x_3506_, 3);
v_cache_3512_ = lean_ctor_get(v___x_3506_, 5);
v_recordedDeps_3513_ = lean_ctor_get(v___x_3506_, 6);
v_messages_3514_ = lean_ctor_get(v___x_3506_, 7);
v_infoState_3515_ = lean_ctor_get(v___x_3506_, 8);
v_snapshotTasks_3516_ = lean_ctor_get(v___x_3506_, 9);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3518_ = v___x_3506_;
v_isShared_3519_ = v_isSharedCheck_3535_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_snapshotTasks_3516_);
lean_inc(v_infoState_3515_);
lean_inc(v_messages_3514_);
lean_inc(v_recordedDeps_3513_);
lean_inc(v_cache_3512_);
lean_inc(v_traceState_3507_);
lean_inc(v_auxDeclNGen_3511_);
lean_inc(v_ngen_3510_);
lean_inc(v_nextMacroScope_3509_);
lean_inc(v_env_3508_);
lean_dec(v___x_3506_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3535_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
uint64_t v_tid_3520_; lean_object* v_traces_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3534_; 
v_tid_3520_ = lean_ctor_get_uint64(v_traceState_3507_, sizeof(void*)*1);
v_traces_3521_ = lean_ctor_get(v_traceState_3507_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_traceState_3507_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3523_ = v_traceState_3507_;
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_traces_3521_);
lean_dec(v_traceState_3507_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3534_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3525_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3450_, v_traces_3521_);
lean_dec_ref(v_traces_3521_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3525_);
v___x_3527_ = v___x_3523_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3525_);
lean_ctor_set_uint64(v_reuseFailAlloc_3533_, sizeof(void*)*1, v_tid_3520_);
v___x_3527_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3529_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v___x_3527_);
v___x_3529_ = v___x_3518_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_env_3508_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_nextMacroScope_3509_);
lean_ctor_set(v_reuseFailAlloc_3532_, 2, v_ngen_3510_);
lean_ctor_set(v_reuseFailAlloc_3532_, 3, v_auxDeclNGen_3511_);
lean_ctor_set(v_reuseFailAlloc_3532_, 4, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3532_, 5, v_cache_3512_);
lean_ctor_set(v_reuseFailAlloc_3532_, 6, v_recordedDeps_3513_);
lean_ctor_set(v_reuseFailAlloc_3532_, 7, v_messages_3514_);
lean_ctor_set(v_reuseFailAlloc_3532_, 8, v_infoState_3515_);
lean_ctor_set(v_reuseFailAlloc_3532_, 9, v_snapshotTasks_3516_);
v___x_3529_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_st_ref_put(v___y_3466_, v___x_3529_);
v___x_3531_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3468_);
return v___x_3531_;
}
}
}
}
}
else
{
goto v___jp_3499_;
}
}
else
{
goto v___jp_3499_;
}
}
v___jp_3536_:
{
double v___x_3538_; double v___x_3539_; double v___x_3540_; uint8_t v___x_3541_; 
v___x_3538_ = lean_unbox_float(v_snd_3485_);
v___x_3539_ = lean_unbox_float(v_fst_3484_);
v___x_3540_ = lean_float_sub(v___x_3538_, v___x_3539_);
v___x_3541_ = lean_float_decLt(v___y_3537_, v___x_3540_);
v___y_3505_ = v___x_3541_;
goto v___jp_3504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9___boxed(lean_object** _args){
lean_object* v_cls_3552_ = _args[0];
lean_object* v_collapsed_3553_ = _args[1];
lean_object* v_tag_3554_ = _args[2];
lean_object* v_opts_3555_ = _args[3];
lean_object* v_clsEnabled_3556_ = _args[4];
lean_object* v_oldTraces_3557_ = _args[5];
lean_object* v_msg_3558_ = _args[6];
lean_object* v_resStartStop_3559_ = _args[7];
lean_object* v___y_3560_ = _args[8];
lean_object* v___y_3561_ = _args[9];
lean_object* v___y_3562_ = _args[10];
lean_object* v___y_3563_ = _args[11];
lean_object* v___y_3564_ = _args[12];
lean_object* v___y_3565_ = _args[13];
lean_object* v___y_3566_ = _args[14];
lean_object* v___y_3567_ = _args[15];
lean_object* v___y_3568_ = _args[16];
lean_object* v___y_3569_ = _args[17];
lean_object* v___y_3570_ = _args[18];
lean_object* v___y_3571_ = _args[19];
lean_object* v___y_3572_ = _args[20];
lean_object* v___y_3573_ = _args[21];
lean_object* v___y_3574_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_3575_; uint8_t v_clsEnabled_boxed_3576_; lean_object* v_res_3577_; 
v_collapsed_boxed_3575_ = lean_unbox(v_collapsed_3553_);
v_clsEnabled_boxed_3576_ = lean_unbox(v_clsEnabled_3556_);
v_res_3577_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_3552_, v_collapsed_boxed_3575_, v_tag_3554_, v_opts_3555_, v_clsEnabled_boxed_3576_, v_oldTraces_3557_, v_msg_3558_, v_resStartStop_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v_opts_3555_);
return v_res_3577_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(lean_object* v_e_3578_){
_start:
{
if (lean_obj_tag(v_e_3578_) == 0)
{
uint8_t v___x_3579_; 
v___x_3579_ = 2;
return v___x_3579_;
}
else
{
uint8_t v___x_3580_; 
v___x_3580_ = 0;
return v___x_3580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22___boxed(lean_object* v_e_3581_){
_start:
{
uint8_t v_res_3582_; lean_object* v_r_3583_; 
v_res_3582_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(v_e_3581_);
lean_dec_ref(v_e_3581_);
v_r_3583_ = lean_box(v_res_3582_);
return v_r_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(lean_object* v_cls_3584_, uint8_t v_collapsed_3585_, lean_object* v_tag_3586_, lean_object* v_opts_3587_, uint8_t v_clsEnabled_3588_, lean_object* v_oldTraces_3589_, lean_object* v_msg_3590_, lean_object* v_resStartStop_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v_fst_3607_; lean_object* v_snd_3608_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v_data_3612_; lean_object* v_fst_3623_; lean_object* v_snd_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; lean_object* v___y_3628_; lean_object* v_a_3629_; uint8_t v___y_3644_; double v___y_3676_; 
v_fst_3607_ = lean_ctor_get(v_resStartStop_3591_, 0);
lean_inc(v_fst_3607_);
v_snd_3608_ = lean_ctor_get(v_resStartStop_3591_, 1);
lean_inc(v_snd_3608_);
lean_dec_ref(v_resStartStop_3591_);
v_fst_3623_ = lean_ctor_get(v_snd_3608_, 0);
lean_inc(v_fst_3623_);
v_snd_3624_ = lean_ctor_get(v_snd_3608_, 1);
lean_inc(v_snd_3624_);
lean_dec(v_snd_3608_);
v___x_3625_ = l_Lean_trace_profiler;
v___x_3626_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3587_, v___x_3625_);
if (v___x_3626_ == 0)
{
v___y_3644_ = v___x_3626_;
goto v___jp_3643_;
}
else
{
lean_object* v___x_3681_; uint8_t v___x_3682_; 
v___x_3681_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3682_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3587_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; double v___x_3685_; double v___x_3686_; double v___x_3687_; 
v___x_3683_ = l_Lean_trace_profiler_threshold;
v___x_3684_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3587_, v___x_3683_);
v___x_3685_ = lean_float_of_nat(v___x_3684_);
v___x_3686_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_3687_ = lean_float_div(v___x_3685_, v___x_3686_);
v___y_3676_ = v___x_3687_;
goto v___jp_3675_;
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; double v___x_3690_; 
v___x_3688_ = l_Lean_trace_profiler_threshold;
v___x_3689_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3587_, v___x_3688_);
v___x_3690_ = lean_float_of_nat(v___x_3689_);
v___y_3676_ = v___x_3690_;
goto v___jp_3675_;
}
}
v___jp_3609_:
{
lean_object* v___x_3613_; 
lean_inc(v___y_3610_);
v___x_3613_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_3589_, v_data_3612_, v___y_3610_, v___y_3611_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v___x_3614_; 
lean_dec_ref_known(v___x_3613_, 1);
v___x_3614_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3607_);
return v___x_3614_;
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_fst_3607_);
v_a_3615_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3613_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3613_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
v___jp_3627_:
{
uint8_t v_result_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; double v___x_3633_; lean_object* v_data_3634_; 
v_result_3630_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(v_fst_3607_);
v___x_3631_ = lean_box(v_result_3630_);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
v___x_3633_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_3586_);
lean_inc_ref(v___x_3632_);
lean_inc(v_cls_3584_);
v_data_3634_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3634_, 0, v_cls_3584_);
lean_ctor_set(v_data_3634_, 1, v___x_3632_);
lean_ctor_set(v_data_3634_, 2, v_tag_3586_);
lean_ctor_set_float(v_data_3634_, sizeof(void*)*3, v___x_3633_);
lean_ctor_set_float(v_data_3634_, sizeof(void*)*3 + 8, v___x_3633_);
lean_ctor_set_uint8(v_data_3634_, sizeof(void*)*3 + 16, v_collapsed_3585_);
if (v___x_3626_ == 0)
{
lean_dec_ref_known(v___x_3632_, 1);
lean_dec(v_snd_3624_);
lean_dec(v_fst_3623_);
lean_dec_ref(v_tag_3586_);
lean_dec(v_cls_3584_);
v___y_3610_ = v___y_3628_;
v___y_3611_ = v_a_3629_;
v_data_3612_ = v_data_3634_;
goto v___jp_3609_;
}
else
{
lean_object* v_data_3635_; double v___x_3636_; double v___x_3637_; 
lean_dec_ref_known(v_data_3634_, 3);
v_data_3635_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3635_, 0, v_cls_3584_);
lean_ctor_set(v_data_3635_, 1, v___x_3632_);
lean_ctor_set(v_data_3635_, 2, v_tag_3586_);
v___x_3636_ = lean_unbox_float(v_fst_3623_);
lean_dec(v_fst_3623_);
lean_ctor_set_float(v_data_3635_, sizeof(void*)*3, v___x_3636_);
v___x_3637_ = lean_unbox_float(v_snd_3624_);
lean_dec(v_snd_3624_);
lean_ctor_set_float(v_data_3635_, sizeof(void*)*3 + 8, v___x_3637_);
lean_ctor_set_uint8(v_data_3635_, sizeof(void*)*3 + 16, v_collapsed_3585_);
v___y_3610_ = v___y_3628_;
v___y_3611_ = v_a_3629_;
v_data_3612_ = v_data_3635_;
goto v___jp_3609_;
}
}
v___jp_3638_:
{
lean_object* v_ref_3639_; lean_object* v___x_3640_; 
v_ref_3639_ = lean_ctor_get(v___y_3604_, 2);
lean_inc(v___y_3605_);
lean_inc_ref(v___y_3604_);
lean_inc(v___y_3603_);
lean_inc_ref(v___y_3602_);
lean_inc(v___y_3601_);
lean_inc_ref(v___y_3600_);
lean_inc(v___y_3599_);
lean_inc_ref(v___y_3598_);
lean_inc(v___y_3597_);
lean_inc(v___y_3596_);
lean_inc_ref(v___y_3595_);
lean_inc(v___y_3594_);
lean_inc(v___y_3593_);
lean_inc_ref(v___y_3592_);
lean_inc(v_fst_3607_);
v___x_3640_ = lean_apply_16(v_msg_3590_, v_fst_3607_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, lean_box(0));
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3640_, 1);
v___y_3628_ = v_ref_3639_;
v_a_3629_ = v_a_3641_;
goto v___jp_3627_;
}
else
{
lean_object* v___x_3642_; 
lean_dec_ref_known(v___x_3640_, 1);
v___x_3642_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_3628_ = v_ref_3639_;
v_a_3629_ = v___x_3642_;
goto v___jp_3627_;
}
}
v___jp_3643_:
{
if (v_clsEnabled_3588_ == 0)
{
if (v___y_3644_ == 0)
{
lean_object* v___x_3645_; lean_object* v_traceState_3646_; lean_object* v_env_3647_; lean_object* v_nextMacroScope_3648_; lean_object* v_ngen_3649_; lean_object* v_auxDeclNGen_3650_; lean_object* v_cache_3651_; lean_object* v_recordedDeps_3652_; lean_object* v_messages_3653_; lean_object* v_infoState_3654_; lean_object* v_snapshotTasks_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3674_; 
lean_dec(v_snd_3624_);
lean_dec(v_fst_3623_);
lean_dec_ref(v_msg_3590_);
lean_dec_ref(v_tag_3586_);
lean_dec(v_cls_3584_);
v___x_3645_ = lean_st_ref_take(v___y_3605_);
v_traceState_3646_ = lean_ctor_get(v___x_3645_, 4);
v_env_3647_ = lean_ctor_get(v___x_3645_, 0);
v_nextMacroScope_3648_ = lean_ctor_get(v___x_3645_, 1);
v_ngen_3649_ = lean_ctor_get(v___x_3645_, 2);
v_auxDeclNGen_3650_ = lean_ctor_get(v___x_3645_, 3);
v_cache_3651_ = lean_ctor_get(v___x_3645_, 5);
v_recordedDeps_3652_ = lean_ctor_get(v___x_3645_, 6);
v_messages_3653_ = lean_ctor_get(v___x_3645_, 7);
v_infoState_3654_ = lean_ctor_get(v___x_3645_, 8);
v_snapshotTasks_3655_ = lean_ctor_get(v___x_3645_, 9);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3657_ = v___x_3645_;
v_isShared_3658_ = v_isSharedCheck_3674_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_snapshotTasks_3655_);
lean_inc(v_infoState_3654_);
lean_inc(v_messages_3653_);
lean_inc(v_recordedDeps_3652_);
lean_inc(v_cache_3651_);
lean_inc(v_traceState_3646_);
lean_inc(v_auxDeclNGen_3650_);
lean_inc(v_ngen_3649_);
lean_inc(v_nextMacroScope_3648_);
lean_inc(v_env_3647_);
lean_dec(v___x_3645_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3674_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
uint64_t v_tid_3659_; lean_object* v_traces_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3673_; 
v_tid_3659_ = lean_ctor_get_uint64(v_traceState_3646_, sizeof(void*)*1);
v_traces_3660_ = lean_ctor_get(v_traceState_3646_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_traceState_3646_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3662_ = v_traceState_3646_;
v_isShared_3663_ = v_isSharedCheck_3673_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_traces_3660_);
lean_dec(v_traceState_3646_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3673_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3589_, v_traces_3660_);
lean_dec_ref(v_traces_3660_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3664_);
v___x_3666_ = v___x_3662_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3664_);
lean_ctor_set_uint64(v_reuseFailAlloc_3672_, sizeof(void*)*1, v_tid_3659_);
v___x_3666_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 4, v___x_3666_);
v___x_3668_ = v___x_3657_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_env_3647_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_nextMacroScope_3648_);
lean_ctor_set(v_reuseFailAlloc_3671_, 2, v_ngen_3649_);
lean_ctor_set(v_reuseFailAlloc_3671_, 3, v_auxDeclNGen_3650_);
lean_ctor_set(v_reuseFailAlloc_3671_, 4, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3671_, 5, v_cache_3651_);
lean_ctor_set(v_reuseFailAlloc_3671_, 6, v_recordedDeps_3652_);
lean_ctor_set(v_reuseFailAlloc_3671_, 7, v_messages_3653_);
lean_ctor_set(v_reuseFailAlloc_3671_, 8, v_infoState_3654_);
lean_ctor_set(v_reuseFailAlloc_3671_, 9, v_snapshotTasks_3655_);
v___x_3668_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = lean_st_ref_put(v___y_3605_, v___x_3668_);
v___x_3670_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3607_);
return v___x_3670_;
}
}
}
}
}
else
{
goto v___jp_3638_;
}
}
else
{
goto v___jp_3638_;
}
}
v___jp_3675_:
{
double v___x_3677_; double v___x_3678_; double v___x_3679_; uint8_t v___x_3680_; 
v___x_3677_ = lean_unbox_float(v_snd_3624_);
v___x_3678_ = lean_unbox_float(v_fst_3623_);
v___x_3679_ = lean_float_sub(v___x_3677_, v___x_3678_);
v___x_3680_ = lean_float_decLt(v___y_3676_, v___x_3679_);
v___y_3644_ = v___x_3680_;
goto v___jp_3643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10___boxed(lean_object** _args){
lean_object* v_cls_3691_ = _args[0];
lean_object* v_collapsed_3692_ = _args[1];
lean_object* v_tag_3693_ = _args[2];
lean_object* v_opts_3694_ = _args[3];
lean_object* v_clsEnabled_3695_ = _args[4];
lean_object* v_oldTraces_3696_ = _args[5];
lean_object* v_msg_3697_ = _args[6];
lean_object* v_resStartStop_3698_ = _args[7];
lean_object* v___y_3699_ = _args[8];
lean_object* v___y_3700_ = _args[9];
lean_object* v___y_3701_ = _args[10];
lean_object* v___y_3702_ = _args[11];
lean_object* v___y_3703_ = _args[12];
lean_object* v___y_3704_ = _args[13];
lean_object* v___y_3705_ = _args[14];
lean_object* v___y_3706_ = _args[15];
lean_object* v___y_3707_ = _args[16];
lean_object* v___y_3708_ = _args[17];
lean_object* v___y_3709_ = _args[18];
lean_object* v___y_3710_ = _args[19];
lean_object* v___y_3711_ = _args[20];
lean_object* v___y_3712_ = _args[21];
lean_object* v___y_3713_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_3714_; uint8_t v_clsEnabled_boxed_3715_; lean_object* v_res_3716_; 
v_collapsed_boxed_3714_ = lean_unbox(v_collapsed_3692_);
v_clsEnabled_boxed_3715_ = lean_unbox(v_clsEnabled_3695_);
v_res_3716_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_3691_, v_collapsed_boxed_3714_, v_tag_3693_, v_opts_3694_, v_clsEnabled_boxed_3715_, v_oldTraces_3696_, v_msg_3697_, v_resStartStop_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v_opts_3694_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(lean_object* v_aig_3717_){
_start:
{
lean_object* v_decls_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_decls_3718_ = lean_ctor_get(v_aig_3717_, 0);
v___x_3719_ = lean_array_get_size(v_decls_3718_);
v___x_3720_ = 0;
v___x_3721_ = lean_box(v___x_3720_);
v___x_3722_ = lean_mk_array(v___x_3719_, v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1___boxed(lean_object* v_aig_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(v_aig_3723_);
lean_dec_ref(v_aig_3723_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(lean_object* v_aig_3727_){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___closed__0));
v___x_3729_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(v_aig_3727_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___boxed(lean_object* v_aig_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(v_aig_3731_);
lean_dec_ref(v_aig_3731_);
return v_res_3732_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8(void){
_start:
{
lean_object* v_cls_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v_cls_3744_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7));
v___x_3745_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
v___x_3746_ = l_Lean_Name_append(v___x_3745_, v_cls_3744_);
return v___x_3746_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10(void){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3751_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9));
v___x_3752_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
v___x_3753_ = l_Lean_Name_append(v___x_3752_, v___x_3751_);
return v___x_3753_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0;
v___x_3758_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(v___x_3757_);
return v___x_3758_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15(void){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3759_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14);
v___x_3760_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2);
v___x_3761_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0;
v___x_3762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___x_3760_);
lean_ctor_set(v___x_3762_, 2, v___x_3759_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v_toCold_3945_; lean_object* v_options_3946_; lean_object* v_ref_3947_; lean_object* v_inheritedTraceOptions_3948_; uint8_t v_hasTrace_3949_; lean_object* v___f_3950_; lean_object* v___f_3951_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; uint8_t v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; uint8_t v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v_a_3980_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; uint8_t v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v_a_4017_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; uint8_t v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; uint8_t v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; uint8_t v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; uint8_t v___y_4122_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; uint8_t v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___f_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v_cls_4233_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; uint8_t v___y_4317_; uint8_t v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v_a_4332_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; uint8_t v___y_4360_; uint8_t v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v_a_4375_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; uint8_t v___y_4399_; uint8_t v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; uint8_t v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; uint8_t v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; uint8_t v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; uint8_t v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; uint8_t v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v_a_4654_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; uint8_t v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; uint8_t v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v_a_4690_; lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___y_4705_; lean_object* v___y_4706_; lean_object* v___y_4707_; lean_object* v___y_4708_; lean_object* v___y_4709_; uint8_t v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; uint8_t v___y_4714_; lean_object* v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v_ctx_4786_; lean_object* v___y_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v___y_4794_; lean_object* v___y_4795_; lean_object* v___y_4796_; lean_object* v___y_4797_; lean_object* v___y_4798_; lean_object* v___y_4799_; lean_object* v___y_4800_; 
v_toCold_3945_ = lean_ctor_get(v_a_3776_, 0);
v_options_3946_ = lean_ctor_get(v_toCold_3945_, 2);
v_ref_3947_ = lean_ctor_get(v_a_3776_, 2);
v_inheritedTraceOptions_3948_ = lean_ctor_get(v_toCold_3945_, 11);
v_hasTrace_3949_ = lean_ctor_get_uint8(v_options_3946_, sizeof(void*)*1);
v___f_3950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__0));
v___f_3951_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__1));
v___f_4229_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__2));
v___x_4230_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__3));
v___x_4231_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__4));
v___x_4232_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__5));
v_cls_4233_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7));
if (v_hasTrace_3949_ == 0)
{
lean_object* v_tacticContext_4856_; 
v_tacticContext_4856_ = lean_ctor_get(v_a_3764_, 2);
v_ctx_4786_ = v_tacticContext_4856_;
v___y_4787_ = v_a_3764_;
v___y_4788_ = v_a_3765_;
v___y_4789_ = v_a_3766_;
v___y_4790_ = v_a_3767_;
v___y_4791_ = v_a_3768_;
v___y_4792_ = v_a_3769_;
v___y_4793_ = v_a_3770_;
v___y_4794_ = v_a_3771_;
v___y_4795_ = v_a_3772_;
v___y_4796_ = v_a_3773_;
v___y_4797_ = v_a_3774_;
v___y_4798_ = v_a_3775_;
v___y_4799_ = v_a_3776_;
v___y_4800_ = v_a_3777_;
goto v___jp_4785_;
}
else
{
lean_object* v___f_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; lean_object* v___y_4862_; lean_object* v___y_4863_; lean_object* v_a_4864_; lean_object* v___y_4874_; lean_object* v___y_4875_; lean_object* v_a_4876_; lean_object* v___y_4879_; lean_object* v___y_4880_; lean_object* v___y_4881_; lean_object* v___y_4892_; lean_object* v___y_4893_; lean_object* v___y_4894_; lean_object* v___y_4895_; uint8_t v___y_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4899_; lean_object* v___y_4900_; lean_object* v___y_4901_; lean_object* v_a_4902_; lean_object* v___y_4928_; lean_object* v___y_4929_; lean_object* v___y_4930_; lean_object* v___y_4931_; uint8_t v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___y_4942_; lean_object* v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4945_; uint8_t v___y_4946_; lean_object* v___y_4947_; lean_object* v___y_4948_; uint8_t v___y_4949_; lean_object* v___y_4950_; lean_object* v___y_4951_; lean_object* v___y_4952_; uint8_t v___y_4953_; lean_object* v___y_4954_; lean_object* v___y_4955_; lean_object* v_a_4956_; lean_object* v___y_4966_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; uint8_t v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; uint8_t v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; uint8_t v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v_a_4980_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4996_; uint8_t v___y_4997_; lean_object* v___y_4998_; lean_object* v___y_4999_; uint8_t v___y_5000_; lean_object* v___y_5001_; uint8_t v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v_a_5068_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v_a_5083_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5103_; uint8_t v___y_5104_; lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v_a_5109_; lean_object* v___y_5135_; lean_object* v___y_5136_; lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v___y_5139_; uint8_t v___y_5140_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v___y_5143_; lean_object* v___y_5144_; lean_object* v___y_5145_; lean_object* v___y_5149_; lean_object* v___y_5150_; lean_object* v___y_5151_; lean_object* v___y_5152_; lean_object* v___y_5153_; uint8_t v___y_5154_; lean_object* v___y_5155_; lean_object* v___y_5156_; lean_object* v___y_5157_; lean_object* v___y_5158_; uint8_t v___y_5159_; lean_object* v___y_5160_; lean_object* v___y_5161_; lean_object* v_a_5162_; lean_object* v___y_5172_; lean_object* v___y_5173_; lean_object* v___y_5174_; lean_object* v___y_5175_; lean_object* v___y_5176_; uint8_t v___y_5177_; lean_object* v___y_5178_; lean_object* v___y_5179_; lean_object* v___y_5180_; uint8_t v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___y_5184_; lean_object* v_a_5185_; lean_object* v___y_5198_; lean_object* v___y_5199_; lean_object* v___y_5200_; lean_object* v___y_5201_; lean_object* v___y_5202_; uint8_t v___y_5203_; lean_object* v___y_5204_; lean_object* v___y_5205_; lean_object* v___y_5206_; lean_object* v___y_5207_; uint8_t v___y_5208_; uint8_t v___y_5209_; lean_object* v___y_5210_; 
v___f_4857_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__16));
v___x_4858_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_4859_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4860_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3948_, v_options_3946_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_5393_; uint8_t v___x_5394_; 
v___x_5393_ = l_Lean_trace_profiler;
v___x_5394_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3946_, v___x_5393_);
if (v___x_5394_ == 0)
{
lean_object* v_tacticContext_5395_; 
v_tacticContext_5395_ = lean_ctor_get(v_a_3764_, 2);
v_ctx_4786_ = v_tacticContext_5395_;
v___y_4787_ = v_a_3764_;
v___y_4788_ = v_a_3765_;
v___y_4789_ = v_a_3766_;
v___y_4790_ = v_a_3767_;
v___y_4791_ = v_a_3768_;
v___y_4792_ = v_a_3769_;
v___y_4793_ = v_a_3770_;
v___y_4794_ = v_a_3771_;
v___y_4795_ = v_a_3772_;
v___y_4796_ = v_a_3773_;
v___y_4797_ = v_a_3774_;
v___y_4798_ = v_a_3775_;
v___y_4799_ = v_a_3776_;
v___y_4800_ = v_a_3777_;
goto v___jp_4785_;
}
else
{
goto v___jp_5270_;
}
}
else
{
goto v___jp_5270_;
}
v___jp_4861_:
{
lean_object* v___x_4865_; double v___x_4866_; double v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4865_ = lean_io_get_num_heartbeats();
v___x_4866_ = lean_float_of_nat(v___y_4862_);
v___x_4867_ = lean_float_of_nat(v___x_4865_);
v___x_4868_ = lean_box_float(v___x_4866_);
v___x_4869_ = lean_box_float(v___x_4867_);
v___x_4870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4868_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4871_, 0, v_a_4864_);
lean_ctor_set(v___x_4871_, 1, v___x_4870_);
v___x_4872_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_4233_, v_hasTrace_3949_, v___x_4858_, v_options_3946_, v___x_4860_, v___y_4863_, v___f_4857_, v___x_4871_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
return v___x_4872_;
}
v___jp_4873_:
{
lean_object* v___x_4877_; 
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v_a_4876_);
v___y_4862_ = v___y_4874_;
v___y_4863_ = v___y_4875_;
v_a_4864_ = v___x_4877_;
goto v___jp_4861_;
}
v___jp_4878_:
{
if (lean_obj_tag(v___y_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
v_a_4882_ = lean_ctor_get(v___y_4881_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___y_4881_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___y_4881_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___y_4881_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
lean_ctor_set_tag(v___x_4884_, 1);
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
v___y_4862_ = v___y_4879_;
v___y_4863_ = v___y_4880_;
v_a_4864_ = v___x_4887_;
goto v___jp_4861_;
}
}
}
else
{
lean_object* v_a_4890_; 
v_a_4890_ = lean_ctor_get(v___y_4881_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___y_4881_, 1);
v___y_4874_ = v___y_4879_;
v___y_4875_ = v___y_4880_;
v_a_4876_ = v_a_4890_;
goto v___jp_4873_;
}
}
v___jp_4891_:
{
lean_object* v_result_4903_; lean_object* v_aig_4904_; lean_object* v_cache_4905_; lean_object* v_ref_4906_; lean_object* v_decls_4907_; lean_object* v___x_4908_; 
v_result_4903_ = lean_ctor_get(v_a_4902_, 0);
lean_inc_ref(v_result_4903_);
v_aig_4904_ = lean_ctor_get(v_result_4903_, 0);
lean_inc_ref(v_aig_4904_);
v_cache_4905_ = lean_ctor_get(v_a_4902_, 1);
lean_inc_ref(v_cache_4905_);
lean_dec_ref(v_a_4902_);
v_ref_4906_ = lean_ctor_get(v_result_4903_, 1);
lean_inc_ref(v_ref_4906_);
v_decls_4907_ = lean_ctor_get(v_aig_4904_, 0);
v___x_4908_ = lean_array_get_size(v_decls_4907_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
lean_dec(v___y_4900_);
v___x_4909_ = lean_box(0);
lean_inc_ref(v___y_4897_);
lean_inc_ref(v___y_4895_);
v___x_4910_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v___y_4895_, v___x_4908_, v_aig_4904_, v___y_4898_, v___y_4894_, v___y_4897_, v___y_4896_, v___x_4858_, v___f_3951_, v___y_4893_, v_cache_4905_, v_ref_4906_, v_cls_4233_, v___f_3950_, v___y_4892_, v___x_4230_, v_result_4903_, v___x_4231_, v___x_4232_, v___x_4909_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec_ref(v_ref_4906_);
v___y_4879_ = v___y_4899_;
v___y_4880_ = v___y_4901_;
v___y_4881_ = v___x_4910_;
goto v___jp_4878_;
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4911_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_4912_ = l_Nat_reprFast(v___x_4908_);
v___x_4913_ = lean_string_append(v___x_4911_, v___x_4912_);
lean_dec_ref(v___x_4912_);
v___x_4914_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_4915_ = lean_string_append(v___x_4913_, v___x_4914_);
v___x_4916_ = lean_nat_sub(v___x_4908_, v___y_4900_);
lean_dec(v___y_4900_);
v___x_4917_ = l_Nat_reprFast(v___x_4916_);
v___x_4918_ = lean_string_append(v___x_4915_, v___x_4917_);
lean_dec_ref(v___x_4917_);
v___x_4919_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_4920_ = lean_string_append(v___x_4918_, v___x_4919_);
v___x_4921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
v___x_4922_ = l_Lean_MessageData_ofFormat(v___x_4921_);
v___x_4923_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4233_, v___x_4922_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; lean_object* v___x_4925_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref_known(v___x_4923_, 1);
lean_inc_ref(v___y_4897_);
lean_inc_ref(v___y_4895_);
v___x_4925_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v___y_4895_, v___x_4908_, v_aig_4904_, v___y_4898_, v___y_4894_, v___y_4897_, v___y_4896_, v___x_4858_, v___f_3951_, v___y_4893_, v_cache_4905_, v_ref_4906_, v_cls_4233_, v___f_3950_, v___y_4892_, v___x_4230_, v_result_4903_, v___x_4231_, v___x_4232_, v_a_4924_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec_ref(v_ref_4906_);
v___y_4879_ = v___y_4899_;
v___y_4880_ = v___y_4901_;
v___y_4881_ = v___x_4925_;
goto v___jp_4878_;
}
else
{
lean_object* v_a_4926_; 
lean_dec_ref(v_ref_4906_);
lean_dec_ref(v_cache_4905_);
lean_dec_ref(v_aig_4904_);
lean_dec_ref(v_result_4903_);
lean_dec(v___y_4898_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4892_);
v_a_4926_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4926_);
lean_dec_ref_known(v___x_4923_, 1);
v___y_4874_ = v___y_4899_;
v___y_4875_ = v___y_4901_;
v_a_4876_ = v_a_4926_;
goto v___jp_4873_;
}
}
}
v___jp_4927_:
{
if (lean_obj_tag(v___y_4938_) == 0)
{
lean_object* v_a_4939_; 
v_a_4939_ = lean_ctor_get(v___y_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___y_4938_, 1);
v___y_4892_ = v___y_4928_;
v___y_4893_ = v___y_4930_;
v___y_4894_ = v___y_4929_;
v___y_4895_ = v___y_4931_;
v___y_4896_ = v___y_4932_;
v___y_4897_ = v___y_4933_;
v___y_4898_ = v___y_4934_;
v___y_4899_ = v___y_4935_;
v___y_4900_ = v___y_4937_;
v___y_4901_ = v___y_4936_;
v_a_4902_ = v_a_4939_;
goto v___jp_4891_;
}
else
{
lean_object* v_a_4940_; 
lean_dec(v___y_4937_);
lean_dec(v___y_4934_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
v_a_4940_ = lean_ctor_get(v___y_4938_, 0);
lean_inc(v_a_4940_);
lean_dec_ref_known(v___y_4938_, 1);
v___y_4874_ = v___y_4935_;
v___y_4875_ = v___y_4936_;
v_a_4876_ = v_a_4940_;
goto v___jp_4873_;
}
}
v___jp_4941_:
{
lean_object* v___x_4957_; double v___x_4958_; double v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4957_ = lean_io_get_num_heartbeats();
v___x_4958_ = lean_float_of_nat(v___y_4951_);
v___x_4959_ = lean_float_of_nat(v___x_4957_);
v___x_4960_ = lean_box_float(v___x_4958_);
v___x_4961_ = lean_box_float(v___x_4959_);
v___x_4962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4963_, 0, v_a_4956_);
lean_ctor_set(v___x_4963_, 1, v___x_4962_);
v___x_4964_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4233_, v___y_4953_, v___x_4858_, v_options_3946_, v___y_4949_, v___y_4952_, v___f_4229_, v___x_4963_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
v___y_4928_ = v___y_4942_;
v___y_4929_ = v___y_4944_;
v___y_4930_ = v___y_4943_;
v___y_4931_ = v___y_4945_;
v___y_4932_ = v___y_4946_;
v___y_4933_ = v___y_4947_;
v___y_4934_ = v___y_4948_;
v___y_4935_ = v___y_4950_;
v___y_4936_ = v___y_4955_;
v___y_4937_ = v___y_4954_;
v___y_4938_ = v___x_4964_;
goto v___jp_4927_;
}
v___jp_4965_:
{
lean_object* v___x_4981_; double v___x_4982_; double v___x_4983_; double v___x_4984_; double v___x_4985_; double v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4981_ = lean_io_mono_nanos_now();
v___x_4982_ = lean_float_of_nat(v___y_4977_);
v___x_4983_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4984_ = lean_float_div(v___x_4982_, v___x_4983_);
v___x_4985_ = lean_float_of_nat(v___x_4981_);
v___x_4986_ = lean_float_div(v___x_4985_, v___x_4983_);
v___x_4987_ = lean_box_float(v___x_4984_);
v___x_4988_ = lean_box_float(v___x_4986_);
v___x_4989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4987_);
lean_ctor_set(v___x_4989_, 1, v___x_4988_);
v___x_4990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4990_, 0, v_a_4980_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
v___x_4991_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4233_, v___y_4976_, v___x_4858_, v_options_3946_, v___y_4973_, v___y_4975_, v___f_4229_, v___x_4990_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
v___y_4928_ = v___y_4966_;
v___y_4929_ = v___y_4968_;
v___y_4930_ = v___y_4967_;
v___y_4931_ = v___y_4969_;
v___y_4932_ = v___y_4970_;
v___y_4933_ = v___y_4971_;
v___y_4934_ = v___y_4972_;
v___y_4935_ = v___y_4974_;
v___y_4936_ = v___y_4979_;
v___y_4937_ = v___y_4978_;
v___y_4938_ = v___x_4991_;
goto v___jp_4927_;
}
v___jp_4992_:
{
lean_object* v___x_5006_; 
v___x_5006_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3777_);
if (v___y_5002_ == 0)
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5035_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5009_ = v___x_5006_;
v_isShared_5010_ = v_isSharedCheck_5035_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_5006_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5035_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = lean_io_mono_nanos_now();
v___x_5012_ = l_IO_lazyPure___redArg(v___y_5003_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_del_object(v___x_5009_);
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_5012_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5012_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
lean_ctor_set_tag(v___x_5015_, 1);
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_5013_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
v___y_4966_ = v___y_4993_;
v___y_4967_ = v___y_4995_;
v___y_4968_ = v___y_4994_;
v___y_4969_ = v___y_4996_;
v___y_4970_ = v___y_4997_;
v___y_4971_ = v___y_4998_;
v___y_4972_ = v___y_4999_;
v___y_4973_ = v___y_5000_;
v___y_4974_ = v___y_5001_;
v___y_4975_ = v_a_5007_;
v___y_4976_ = v___y_5002_;
v___y_4977_ = v___x_5011_;
v___y_4978_ = v___y_5005_;
v___y_4979_ = v___y_5004_;
v_a_4980_ = v___x_5018_;
goto v___jp_4965_;
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5034_; 
v_a_5021_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5023_ = v___x_5012_;
v_isShared_5024_ = v_isSharedCheck_5034_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5012_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5034_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5025_; lean_object* v___x_5027_; 
v___x_5025_ = lean_io_error_to_string(v_a_5021_);
if (v_isShared_5024_ == 0)
{
lean_ctor_set_tag(v___x_5023_, 3);
lean_ctor_set(v___x_5023_, 0, v___x_5025_);
v___x_5027_ = v___x_5023_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5031_; 
v___x_5028_ = l_Lean_MessageData_ofFormat(v___x_5027_);
lean_inc(v_ref_3947_);
v___x_5029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5029_, 0, v_ref_3947_);
lean_ctor_set(v___x_5029_, 1, v___x_5028_);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 0, v___x_5029_);
v___x_5031_ = v___x_5009_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5029_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
v___y_4966_ = v___y_4993_;
v___y_4967_ = v___y_4995_;
v___y_4968_ = v___y_4994_;
v___y_4969_ = v___y_4996_;
v___y_4970_ = v___y_4997_;
v___y_4971_ = v___y_4998_;
v___y_4972_ = v___y_4999_;
v___y_4973_ = v___y_5000_;
v___y_4974_ = v___y_5001_;
v___y_4975_ = v_a_5007_;
v___y_4976_ = v___y_5002_;
v___y_4977_ = v___x_5011_;
v___y_4978_ = v___y_5005_;
v___y_4979_ = v___y_5004_;
v_a_4980_ = v___x_5031_;
goto v___jp_4965_;
}
}
}
}
}
}
else
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5064_; 
v_a_5036_ = lean_ctor_get(v___x_5006_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5038_ = v___x_5006_;
v_isShared_5039_ = v_isSharedCheck_5064_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_5006_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5064_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5040_ = lean_io_get_num_heartbeats();
v___x_5041_ = l_IO_lazyPure___redArg(v___y_5003_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5049_; 
lean_del_object(v___x_5038_);
v_a_5042_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5044_ = v___x_5041_;
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5041_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5047_; 
if (v_isShared_5045_ == 0)
{
lean_ctor_set_tag(v___x_5044_, 1);
v___x_5047_ = v___x_5044_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
v___y_4942_ = v___y_4993_;
v___y_4943_ = v___y_4995_;
v___y_4944_ = v___y_4994_;
v___y_4945_ = v___y_4996_;
v___y_4946_ = v___y_4997_;
v___y_4947_ = v___y_4998_;
v___y_4948_ = v___y_4999_;
v___y_4949_ = v___y_5000_;
v___y_4950_ = v___y_5001_;
v___y_4951_ = v___x_5040_;
v___y_4952_ = v_a_5036_;
v___y_4953_ = v___y_5002_;
v___y_4954_ = v___y_5005_;
v___y_4955_ = v___y_5004_;
v_a_4956_ = v___x_5047_;
goto v___jp_4941_;
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5063_; 
v_a_5050_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5052_ = v___x_5041_;
v_isShared_5053_ = v_isSharedCheck_5063_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5041_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5063_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5054_; lean_object* v___x_5056_; 
v___x_5054_ = lean_io_error_to_string(v_a_5050_);
if (v_isShared_5053_ == 0)
{
lean_ctor_set_tag(v___x_5052_, 3);
lean_ctor_set(v___x_5052_, 0, v___x_5054_);
v___x_5056_ = v___x_5052_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v___x_5054_);
v___x_5056_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5060_; 
v___x_5057_ = l_Lean_MessageData_ofFormat(v___x_5056_);
lean_inc(v_ref_3947_);
v___x_5058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5058_, 0, v_ref_3947_);
lean_ctor_set(v___x_5058_, 1, v___x_5057_);
if (v_isShared_5039_ == 0)
{
lean_ctor_set(v___x_5038_, 0, v___x_5058_);
v___x_5060_ = v___x_5038_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5058_);
v___x_5060_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
v___y_4942_ = v___y_4993_;
v___y_4943_ = v___y_4995_;
v___y_4944_ = v___y_4994_;
v___y_4945_ = v___y_4996_;
v___y_4946_ = v___y_4997_;
v___y_4947_ = v___y_4998_;
v___y_4948_ = v___y_4999_;
v___y_4949_ = v___y_5000_;
v___y_4950_ = v___y_5001_;
v___y_4951_ = v___x_5040_;
v___y_4952_ = v_a_5036_;
v___y_4953_ = v___y_5002_;
v___y_4954_ = v___y_5005_;
v___y_4955_ = v___y_5004_;
v_a_4956_ = v___x_5060_;
goto v___jp_4941_;
}
}
}
}
}
}
}
v___jp_5065_:
{
lean_object* v___x_5069_; double v___x_5070_; double v___x_5071_; double v___x_5072_; double v___x_5073_; double v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5069_ = lean_io_mono_nanos_now();
v___x_5070_ = lean_float_of_nat(v___y_5066_);
v___x_5071_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_5072_ = lean_float_div(v___x_5070_, v___x_5071_);
v___x_5073_ = lean_float_of_nat(v___x_5069_);
v___x_5074_ = lean_float_div(v___x_5073_, v___x_5071_);
v___x_5075_ = lean_box_float(v___x_5072_);
v___x_5076_ = lean_box_float(v___x_5074_);
v___x_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5075_);
lean_ctor_set(v___x_5077_, 1, v___x_5076_);
v___x_5078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5078_, 0, v_a_5068_);
lean_ctor_set(v___x_5078_, 1, v___x_5077_);
v___x_5079_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_4233_, v_hasTrace_3949_, v___x_4858_, v_options_3946_, v___x_4860_, v___y_5067_, v___f_4857_, v___x_5078_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
return v___x_5079_;
}
v___jp_5080_:
{
lean_object* v___x_5084_; 
v___x_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5084_, 0, v_a_5083_);
v___y_5066_ = v___y_5081_;
v___y_5067_ = v___y_5082_;
v_a_5068_ = v___x_5084_;
goto v___jp_5065_;
}
v___jp_5085_:
{
if (lean_obj_tag(v___y_5088_) == 0)
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
v_a_5089_ = lean_ctor_get(v___y_5088_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___y_5088_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___y_5088_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___y_5088_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set_tag(v___x_5091_, 1);
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
v___y_5066_ = v___y_5086_;
v___y_5067_ = v___y_5087_;
v_a_5068_ = v___x_5094_;
goto v___jp_5065_;
}
}
}
else
{
lean_object* v_a_5097_; 
v_a_5097_ = lean_ctor_get(v___y_5088_, 0);
lean_inc(v_a_5097_);
lean_dec_ref_known(v___y_5088_, 1);
v___y_5081_ = v___y_5086_;
v___y_5082_ = v___y_5087_;
v_a_5083_ = v_a_5097_;
goto v___jp_5080_;
}
}
v___jp_5098_:
{
lean_object* v_result_5110_; lean_object* v_aig_5111_; lean_object* v_cache_5112_; lean_object* v_ref_5113_; lean_object* v_decls_5114_; lean_object* v___x_5115_; 
v_result_5110_ = lean_ctor_get(v_a_5109_, 0);
lean_inc_ref(v_result_5110_);
v_aig_5111_ = lean_ctor_get(v_result_5110_, 0);
lean_inc_ref(v_aig_5111_);
v_cache_5112_ = lean_ctor_get(v_a_5109_, 1);
lean_inc_ref(v_cache_5112_);
lean_dec_ref(v_a_5109_);
v_ref_5113_ = lean_ctor_get(v_result_5110_, 1);
lean_inc_ref(v_ref_5113_);
v_decls_5114_ = lean_ctor_get(v_aig_5111_, 0);
v___x_5115_ = lean_array_get_size(v_decls_5114_);
if (v___x_4860_ == 0)
{
lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_dec(v___y_5107_);
v___x_5116_ = lean_box(0);
lean_inc_ref(v___y_5102_);
lean_inc_ref(v___y_5105_);
v___x_5117_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v___y_5105_, v___x_5115_, v_aig_5111_, v___y_5103_, v___y_5100_, v___y_5102_, v_hasTrace_3949_, v___x_4858_, v___f_3951_, v___y_5099_, v_cache_5112_, v_ref_5113_, v___y_5104_, v_cls_4233_, v___f_3950_, v___y_5101_, v___x_4230_, v_result_5110_, v___x_4231_, v___x_4232_, v___x_5116_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec_ref(v_ref_5113_);
v___y_5086_ = v___y_5106_;
v___y_5087_ = v___y_5108_;
v___y_5088_ = v___x_5117_;
goto v___jp_5085_;
}
else
{
lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5118_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_5119_ = l_Nat_reprFast(v___x_5115_);
v___x_5120_ = lean_string_append(v___x_5118_, v___x_5119_);
lean_dec_ref(v___x_5119_);
v___x_5121_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_5122_ = lean_string_append(v___x_5120_, v___x_5121_);
v___x_5123_ = lean_nat_sub(v___x_5115_, v___y_5107_);
lean_dec(v___y_5107_);
v___x_5124_ = l_Nat_reprFast(v___x_5123_);
v___x_5125_ = lean_string_append(v___x_5122_, v___x_5124_);
lean_dec_ref(v___x_5124_);
v___x_5126_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_5127_ = lean_string_append(v___x_5125_, v___x_5126_);
v___x_5128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5127_);
v___x_5129_ = l_Lean_MessageData_ofFormat(v___x_5128_);
v___x_5130_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4233_, v___x_5129_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v___x_5132_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5130_, 1);
lean_inc_ref(v___y_5102_);
lean_inc_ref(v___y_5105_);
v___x_5132_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v___y_5105_, v___x_5115_, v_aig_5111_, v___y_5103_, v___y_5100_, v___y_5102_, v_hasTrace_3949_, v___x_4858_, v___f_3951_, v___y_5099_, v_cache_5112_, v_ref_5113_, v___y_5104_, v_cls_4233_, v___f_3950_, v___y_5101_, v___x_4230_, v_result_5110_, v___x_4231_, v___x_4232_, v_a_5131_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec_ref(v_ref_5113_);
v___y_5086_ = v___y_5106_;
v___y_5087_ = v___y_5108_;
v___y_5088_ = v___x_5132_;
goto v___jp_5085_;
}
else
{
lean_object* v_a_5133_; 
lean_dec_ref(v_ref_5113_);
lean_dec_ref(v_cache_5112_);
lean_dec_ref(v_aig_5111_);
lean_dec_ref(v_result_5110_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5101_);
lean_dec(v___y_5100_);
v_a_5133_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5130_, 1);
v___y_5081_ = v___y_5106_;
v___y_5082_ = v___y_5108_;
v_a_5083_ = v_a_5133_;
goto v___jp_5080_;
}
}
}
v___jp_5134_:
{
if (lean_obj_tag(v___y_5145_) == 0)
{
lean_object* v_a_5146_; 
v_a_5146_ = lean_ctor_get(v___y_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref_known(v___y_5145_, 1);
v___y_5099_ = v___y_5135_;
v___y_5100_ = v___y_5136_;
v___y_5101_ = v___y_5137_;
v___y_5102_ = v___y_5139_;
v___y_5103_ = v___y_5138_;
v___y_5104_ = v___y_5140_;
v___y_5105_ = v___y_5141_;
v___y_5106_ = v___y_5142_;
v___y_5107_ = v___y_5143_;
v___y_5108_ = v___y_5144_;
v_a_5109_ = v_a_5146_;
goto v___jp_5098_;
}
else
{
lean_object* v_a_5147_; 
lean_dec(v___y_5143_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5137_);
lean_dec(v___y_5136_);
v_a_5147_ = lean_ctor_get(v___y_5145_, 0);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___y_5145_, 1);
v___y_5081_ = v___y_5142_;
v___y_5082_ = v___y_5144_;
v_a_5083_ = v_a_5147_;
goto v___jp_5080_;
}
}
v___jp_5148_:
{
lean_object* v___x_5163_; double v___x_5164_; double v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___x_5163_ = lean_io_get_num_heartbeats();
v___x_5164_ = lean_float_of_nat(v___y_5158_);
v___x_5165_ = lean_float_of_nat(v___x_5163_);
v___x_5166_ = lean_box_float(v___x_5164_);
v___x_5167_ = lean_box_float(v___x_5165_);
v___x_5168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5166_);
lean_ctor_set(v___x_5168_, 1, v___x_5167_);
v___x_5169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5169_, 0, v_a_5162_);
lean_ctor_set(v___x_5169_, 1, v___x_5168_);
v___x_5170_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4233_, v_hasTrace_3949_, v___x_4858_, v_options_3946_, v___y_5159_, v___y_5160_, v___f_4229_, v___x_5169_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
v___y_5135_ = v___y_5149_;
v___y_5136_ = v___y_5150_;
v___y_5137_ = v___y_5151_;
v___y_5138_ = v___y_5153_;
v___y_5139_ = v___y_5152_;
v___y_5140_ = v___y_5154_;
v___y_5141_ = v___y_5155_;
v___y_5142_ = v___y_5156_;
v___y_5143_ = v___y_5157_;
v___y_5144_ = v___y_5161_;
v___y_5145_ = v___x_5170_;
goto v___jp_5134_;
}
v___jp_5171_:
{
lean_object* v___x_5186_; double v___x_5187_; double v___x_5188_; double v___x_5189_; double v___x_5190_; double v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5186_ = lean_io_mono_nanos_now();
v___x_5187_ = lean_float_of_nat(v___y_5182_);
v___x_5188_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_5189_ = lean_float_div(v___x_5187_, v___x_5188_);
v___x_5190_ = lean_float_of_nat(v___x_5186_);
v___x_5191_ = lean_float_div(v___x_5190_, v___x_5188_);
v___x_5192_ = lean_box_float(v___x_5189_);
v___x_5193_ = lean_box_float(v___x_5191_);
v___x_5194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5192_);
lean_ctor_set(v___x_5194_, 1, v___x_5193_);
v___x_5195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5195_, 0, v_a_5185_);
lean_ctor_set(v___x_5195_, 1, v___x_5194_);
v___x_5196_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4233_, v_hasTrace_3949_, v___x_4858_, v_options_3946_, v___y_5181_, v___y_5183_, v___f_4229_, v___x_5195_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
v___y_5135_ = v___y_5172_;
v___y_5136_ = v___y_5173_;
v___y_5137_ = v___y_5174_;
v___y_5138_ = v___y_5176_;
v___y_5139_ = v___y_5175_;
v___y_5140_ = v___y_5177_;
v___y_5141_ = v___y_5178_;
v___y_5142_ = v___y_5179_;
v___y_5143_ = v___y_5180_;
v___y_5144_ = v___y_5184_;
v___y_5145_ = v___x_5196_;
goto v___jp_5134_;
}
v___jp_5197_:
{
lean_object* v___x_5211_; 
v___x_5211_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3777_);
if (v___y_5209_ == 0)
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5240_; 
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5214_ = v___x_5211_;
v_isShared_5215_ = v_isSharedCheck_5240_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5211_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5240_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5216_ = lean_io_mono_nanos_now();
v___x_5217_ = l_IO_lazyPure___redArg(v___y_5205_);
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
lean_del_object(v___x_5214_);
v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5217_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5217_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
lean_ctor_set_tag(v___x_5220_, 1);
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
v___y_5172_ = v___y_5198_;
v___y_5173_ = v___y_5199_;
v___y_5174_ = v___y_5200_;
v___y_5175_ = v___y_5202_;
v___y_5176_ = v___y_5201_;
v___y_5177_ = v___y_5203_;
v___y_5178_ = v___y_5204_;
v___y_5179_ = v___y_5206_;
v___y_5180_ = v___y_5207_;
v___y_5181_ = v___y_5208_;
v___y_5182_ = v___x_5216_;
v___y_5183_ = v_a_5212_;
v___y_5184_ = v___y_5210_;
v_a_5185_ = v___x_5223_;
goto v___jp_5171_;
}
}
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5239_; 
v_a_5226_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5228_ = v___x_5217_;
v_isShared_5229_ = v_isSharedCheck_5239_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5217_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5239_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5230_; lean_object* v___x_5232_; 
v___x_5230_ = lean_io_error_to_string(v_a_5226_);
if (v_isShared_5229_ == 0)
{
lean_ctor_set_tag(v___x_5228_, 3);
lean_ctor_set(v___x_5228_, 0, v___x_5230_);
v___x_5232_ = v___x_5228_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5230_);
v___x_5232_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5236_; 
v___x_5233_ = l_Lean_MessageData_ofFormat(v___x_5232_);
lean_inc(v_ref_3947_);
v___x_5234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5234_, 0, v_ref_3947_);
lean_ctor_set(v___x_5234_, 1, v___x_5233_);
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 0, v___x_5234_);
v___x_5236_ = v___x_5214_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5234_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
v___y_5172_ = v___y_5198_;
v___y_5173_ = v___y_5199_;
v___y_5174_ = v___y_5200_;
v___y_5175_ = v___y_5202_;
v___y_5176_ = v___y_5201_;
v___y_5177_ = v___y_5203_;
v___y_5178_ = v___y_5204_;
v___y_5179_ = v___y_5206_;
v___y_5180_ = v___y_5207_;
v___y_5181_ = v___y_5208_;
v___y_5182_ = v___x_5216_;
v___y_5183_ = v_a_5212_;
v___y_5184_ = v___y_5210_;
v_a_5185_ = v___x_5236_;
goto v___jp_5171_;
}
}
}
}
}
}
else
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5269_; 
v_a_5241_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5243_ = v___x_5211_;
v_isShared_5244_ = v_isSharedCheck_5269_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v___x_5211_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5269_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5245_ = lean_io_get_num_heartbeats();
v___x_5246_ = l_IO_lazyPure___redArg(v___y_5205_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
lean_del_object(v___x_5243_);
v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_5246_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5246_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
lean_ctor_set_tag(v___x_5249_, 1);
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
v___y_5149_ = v___y_5198_;
v___y_5150_ = v___y_5199_;
v___y_5151_ = v___y_5200_;
v___y_5152_ = v___y_5202_;
v___y_5153_ = v___y_5201_;
v___y_5154_ = v___y_5203_;
v___y_5155_ = v___y_5204_;
v___y_5156_ = v___y_5206_;
v___y_5157_ = v___y_5207_;
v___y_5158_ = v___x_5245_;
v___y_5159_ = v___y_5208_;
v___y_5160_ = v_a_5241_;
v___y_5161_ = v___y_5210_;
v_a_5162_ = v___x_5252_;
goto v___jp_5148_;
}
}
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5268_; 
v_a_5255_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5257_ = v___x_5246_;
v_isShared_5258_ = v_isSharedCheck_5268_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5246_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5268_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5259_; lean_object* v___x_5261_; 
v___x_5259_ = lean_io_error_to_string(v_a_5255_);
if (v_isShared_5258_ == 0)
{
lean_ctor_set_tag(v___x_5257_, 3);
lean_ctor_set(v___x_5257_, 0, v___x_5259_);
v___x_5261_ = v___x_5257_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v___x_5259_);
v___x_5261_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5265_; 
v___x_5262_ = l_Lean_MessageData_ofFormat(v___x_5261_);
lean_inc(v_ref_3947_);
v___x_5263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5263_, 0, v_ref_3947_);
lean_ctor_set(v___x_5263_, 1, v___x_5262_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v___x_5263_);
v___x_5265_ = v___x_5243_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5263_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
v___y_5149_ = v___y_5198_;
v___y_5150_ = v___y_5199_;
v___y_5151_ = v___y_5200_;
v___y_5152_ = v___y_5202_;
v___y_5153_ = v___y_5201_;
v___y_5154_ = v___y_5203_;
v___y_5155_ = v___y_5204_;
v___y_5156_ = v___y_5206_;
v___y_5157_ = v___y_5207_;
v___y_5158_ = v___x_5245_;
v___y_5159_ = v___y_5208_;
v___y_5160_ = v_a_5241_;
v___y_5161_ = v___y_5210_;
v_a_5162_ = v___x_5265_;
goto v___jp_5148_;
}
}
}
}
}
}
}
v___jp_5270_:
{
lean_object* v___x_5271_; lean_object* v_a_5272_; lean_object* v___x_5273_; uint8_t v___x_5274_; 
v___x_5271_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3777_);
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
lean_inc(v_a_5272_);
lean_dec_ref(v___x_5271_);
v___x_5273_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5274_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3946_, v___x_5273_);
if (v___x_5274_ == 0)
{
lean_object* v___x_5275_; lean_object* v_tacticContext_5276_; lean_object* v___x_5277_; lean_object* v_satExpr_5278_; lean_object* v_bvExpr_5279_; lean_object* v___x_5280_; lean_object* v_theoryState_5281_; lean_object* v_bitvecState_5282_; lean_object* v___x_5283_; lean_object* v_theoryState_5284_; lean_object* v_satExpr_5285_; lean_object* v_hypQueue_5286_; lean_object* v_usedHyps_5287_; uint8_t v_didChange_5288_; lean_object* v_solverTimeBudgetMs_5289_; lean_object* v_roundBudget_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5333_; 
v___x_5275_ = lean_io_mono_nanos_now();
v_tacticContext_5276_ = lean_ctor_get(v_a_3764_, 2);
v___x_5277_ = lean_st_ref_get(v_a_3765_);
v_satExpr_5278_ = lean_ctor_get(v___x_5277_, 0);
lean_inc_ref(v_satExpr_5278_);
lean_dec(v___x_5277_);
v_bvExpr_5279_ = lean_ctor_get(v_satExpr_5278_, 0);
lean_inc_ref(v_bvExpr_5279_);
lean_dec_ref(v_satExpr_5278_);
v___x_5280_ = lean_st_ref_get(v_a_3765_);
v_theoryState_5281_ = lean_ctor_get(v___x_5280_, 3);
lean_inc_ref(v_theoryState_5281_);
lean_dec(v___x_5280_);
v_bitvecState_5282_ = lean_ctor_get(v_theoryState_5281_, 1);
lean_inc_ref(v_bitvecState_5282_);
lean_dec_ref(v_theoryState_5281_);
v___x_5283_ = lean_st_ref_take(v_a_3765_);
v_theoryState_5284_ = lean_ctor_get(v___x_5283_, 3);
v_satExpr_5285_ = lean_ctor_get(v___x_5283_, 0);
v_hypQueue_5286_ = lean_ctor_get(v___x_5283_, 1);
v_usedHyps_5287_ = lean_ctor_get(v___x_5283_, 2);
v_didChange_5288_ = lean_ctor_get_uint8(v___x_5283_, sizeof(void*)*6);
v_solverTimeBudgetMs_5289_ = lean_ctor_get(v___x_5283_, 4);
v_roundBudget_5290_ = lean_ctor_get(v___x_5283_, 5);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5292_ = v___x_5283_;
v_isShared_5293_ = v_isSharedCheck_5333_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_roundBudget_5290_);
lean_inc(v_solverTimeBudgetMs_5289_);
lean_inc(v_theoryState_5284_);
lean_inc(v_usedHyps_5287_);
lean_inc(v_hypQueue_5286_);
lean_inc(v_satExpr_5285_);
lean_dec(v___x_5283_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5333_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v_funState_5294_; lean_object* v_preprocessCaches_5295_; lean_object* v_satSolver_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5331_; 
v_funState_5294_ = lean_ctor_get(v_theoryState_5284_, 0);
v_preprocessCaches_5295_ = lean_ctor_get(v_theoryState_5284_, 2);
v_satSolver_5296_ = lean_ctor_get(v_theoryState_5284_, 3);
v_isSharedCheck_5331_ = !lean_is_exclusive(v_theoryState_5284_);
if (v_isSharedCheck_5331_ == 0)
{
lean_object* v_unused_5332_; 
v_unused_5332_ = lean_ctor_get(v_theoryState_5284_, 1);
lean_dec(v_unused_5332_);
v___x_5298_ = v_theoryState_5284_;
v_isShared_5299_ = v_isSharedCheck_5331_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_satSolver_5296_);
lean_inc(v_preprocessCaches_5295_);
lean_inc(v_funState_5294_);
lean_dec(v_theoryState_5284_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5331_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5304_; 
v___x_5300_ = lean_unsigned_to_nat(0u);
v___x_5301_ = lean_unsigned_to_nat(16u);
v___x_5302_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_5299_ == 0)
{
lean_ctor_set(v___x_5298_, 1, v___x_5302_);
v___x_5304_ = v___x_5298_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_funState_5294_);
lean_ctor_set(v_reuseFailAlloc_5330_, 1, v___x_5302_);
lean_ctor_set(v_reuseFailAlloc_5330_, 2, v_preprocessCaches_5295_);
lean_ctor_set(v_reuseFailAlloc_5330_, 3, v_satSolver_5296_);
v___x_5304_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
lean_object* v___x_5306_; 
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 3, v___x_5304_);
v___x_5306_ = v___x_5292_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_satExpr_5285_);
lean_ctor_set(v_reuseFailAlloc_5329_, 1, v_hypQueue_5286_);
lean_ctor_set(v_reuseFailAlloc_5329_, 2, v_usedHyps_5287_);
lean_ctor_set(v_reuseFailAlloc_5329_, 3, v___x_5304_);
lean_ctor_set(v_reuseFailAlloc_5329_, 4, v_solverTimeBudgetMs_5289_);
lean_ctor_set(v_reuseFailAlloc_5329_, 5, v_roundBudget_5290_);
lean_ctor_set_uint8(v_reuseFailAlloc_5329_, sizeof(void*)*6, v_didChange_5288_);
v___x_5306_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
lean_object* v___x_5307_; lean_object* v_aig_5308_; lean_object* v_blastCache_5309_; lean_object* v_cnfCache_5310_; lean_object* v_decls_5311_; lean_object* v___f_5312_; lean_object* v___x_5313_; 
v___x_5307_ = lean_st_ref_put(v_a_3765_, v___x_5306_);
v_aig_5308_ = lean_ctor_get(v_bitvecState_5282_, 0);
lean_inc_ref(v_aig_5308_);
v_blastCache_5309_ = lean_ctor_get(v_bitvecState_5282_, 1);
lean_inc_ref(v_blastCache_5309_);
v_cnfCache_5310_ = lean_ctor_get(v_bitvecState_5282_, 2);
lean_inc_ref(v_cnfCache_5310_);
lean_dec_ref(v_bitvecState_5282_);
v_decls_5311_ = lean_ctor_get(v_aig_5308_, 0);
lean_inc_ref(v_decls_5311_);
v___f_5312_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_5312_, 0, v_aig_5308_);
lean_closure_set(v___f_5312_, 1, v_bvExpr_5279_);
lean_closure_set(v___f_5312_, 2, v_blastCache_5309_);
v___x_5313_ = lean_array_get_size(v_decls_5311_);
lean_dec_ref(v_decls_5311_);
if (v___x_4860_ == 0)
{
lean_object* v___x_5314_; uint8_t v___x_5315_; 
v___x_5314_ = l_Lean_trace_profiler;
v___x_5315_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3946_, v___x_5314_);
if (v___x_5315_ == 0)
{
lean_object* v___x_5316_; 
v___x_5316_ = l_IO_lazyPure___redArg(v___f_5312_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_a_5317_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
lean_inc(v_a_5317_);
lean_dec_ref_known(v___x_5316_, 1);
v___y_5099_ = v___x_5273_;
v___y_5100_ = v___x_5300_;
v___y_5101_ = v_cnfCache_5310_;
v___y_5102_ = v___x_5302_;
v___y_5103_ = v___x_5301_;
v___y_5104_ = v___x_5274_;
v___y_5105_ = v_tacticContext_5276_;
v___y_5106_ = v___x_5275_;
v___y_5107_ = v___x_5313_;
v___y_5108_ = v_a_5272_;
v_a_5109_ = v_a_5317_;
goto v___jp_5098_;
}
else
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5328_; 
lean_dec_ref(v_cnfCache_5310_);
v_a_5318_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5320_ = v___x_5316_;
v_isShared_5321_ = v_isSharedCheck_5328_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5316_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5328_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5322_; lean_object* v___x_5324_; 
v___x_5322_ = lean_io_error_to_string(v_a_5318_);
if (v_isShared_5321_ == 0)
{
lean_ctor_set_tag(v___x_5320_, 3);
lean_ctor_set(v___x_5320_, 0, v___x_5322_);
v___x_5324_ = v___x_5320_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5322_);
v___x_5324_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; 
v___x_5325_ = l_Lean_MessageData_ofFormat(v___x_5324_);
lean_inc(v_ref_3947_);
v___x_5326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5326_, 0, v_ref_3947_);
lean_ctor_set(v___x_5326_, 1, v___x_5325_);
v___y_5081_ = v___x_5275_;
v___y_5082_ = v_a_5272_;
v_a_5083_ = v___x_5326_;
goto v___jp_5080_;
}
}
}
}
else
{
v___y_5198_ = v___x_5273_;
v___y_5199_ = v___x_5300_;
v___y_5200_ = v_cnfCache_5310_;
v___y_5201_ = v___x_5301_;
v___y_5202_ = v___x_5302_;
v___y_5203_ = v___x_5274_;
v___y_5204_ = v_tacticContext_5276_;
v___y_5205_ = v___f_5312_;
v___y_5206_ = v___x_5275_;
v___y_5207_ = v___x_5313_;
v___y_5208_ = v___x_4860_;
v___y_5209_ = v___x_5274_;
v___y_5210_ = v_a_5272_;
goto v___jp_5197_;
}
}
else
{
v___y_5198_ = v___x_5273_;
v___y_5199_ = v___x_5300_;
v___y_5200_ = v_cnfCache_5310_;
v___y_5201_ = v___x_5301_;
v___y_5202_ = v___x_5302_;
v___y_5203_ = v___x_5274_;
v___y_5204_ = v_tacticContext_5276_;
v___y_5205_ = v___f_5312_;
v___y_5206_ = v___x_5275_;
v___y_5207_ = v___x_5313_;
v___y_5208_ = v___x_4860_;
v___y_5209_ = v___x_5274_;
v___y_5210_ = v_a_5272_;
goto v___jp_5197_;
}
}
}
}
}
}
else
{
lean_object* v___x_5334_; lean_object* v_tacticContext_5335_; lean_object* v___x_5336_; lean_object* v_satExpr_5337_; lean_object* v_bvExpr_5338_; lean_object* v___x_5339_; lean_object* v_theoryState_5340_; lean_object* v_bitvecState_5341_; lean_object* v___x_5342_; lean_object* v_theoryState_5343_; lean_object* v_satExpr_5344_; lean_object* v_hypQueue_5345_; lean_object* v_usedHyps_5346_; uint8_t v_didChange_5347_; lean_object* v_solverTimeBudgetMs_5348_; lean_object* v_roundBudget_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5392_; 
v___x_5334_ = lean_io_get_num_heartbeats();
v_tacticContext_5335_ = lean_ctor_get(v_a_3764_, 2);
v___x_5336_ = lean_st_ref_get(v_a_3765_);
v_satExpr_5337_ = lean_ctor_get(v___x_5336_, 0);
lean_inc_ref(v_satExpr_5337_);
lean_dec(v___x_5336_);
v_bvExpr_5338_ = lean_ctor_get(v_satExpr_5337_, 0);
lean_inc_ref(v_bvExpr_5338_);
lean_dec_ref(v_satExpr_5337_);
v___x_5339_ = lean_st_ref_get(v_a_3765_);
v_theoryState_5340_ = lean_ctor_get(v___x_5339_, 3);
lean_inc_ref(v_theoryState_5340_);
lean_dec(v___x_5339_);
v_bitvecState_5341_ = lean_ctor_get(v_theoryState_5340_, 1);
lean_inc_ref(v_bitvecState_5341_);
lean_dec_ref(v_theoryState_5340_);
v___x_5342_ = lean_st_ref_take(v_a_3765_);
v_theoryState_5343_ = lean_ctor_get(v___x_5342_, 3);
v_satExpr_5344_ = lean_ctor_get(v___x_5342_, 0);
v_hypQueue_5345_ = lean_ctor_get(v___x_5342_, 1);
v_usedHyps_5346_ = lean_ctor_get(v___x_5342_, 2);
v_didChange_5347_ = lean_ctor_get_uint8(v___x_5342_, sizeof(void*)*6);
v_solverTimeBudgetMs_5348_ = lean_ctor_get(v___x_5342_, 4);
v_roundBudget_5349_ = lean_ctor_get(v___x_5342_, 5);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5351_ = v___x_5342_;
v_isShared_5352_ = v_isSharedCheck_5392_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_roundBudget_5349_);
lean_inc(v_solverTimeBudgetMs_5348_);
lean_inc(v_theoryState_5343_);
lean_inc(v_usedHyps_5346_);
lean_inc(v_hypQueue_5345_);
lean_inc(v_satExpr_5344_);
lean_dec(v___x_5342_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5392_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v_funState_5353_; lean_object* v_preprocessCaches_5354_; lean_object* v_satSolver_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5390_; 
v_funState_5353_ = lean_ctor_get(v_theoryState_5343_, 0);
v_preprocessCaches_5354_ = lean_ctor_get(v_theoryState_5343_, 2);
v_satSolver_5355_ = lean_ctor_get(v_theoryState_5343_, 3);
v_isSharedCheck_5390_ = !lean_is_exclusive(v_theoryState_5343_);
if (v_isSharedCheck_5390_ == 0)
{
lean_object* v_unused_5391_; 
v_unused_5391_ = lean_ctor_get(v_theoryState_5343_, 1);
lean_dec(v_unused_5391_);
v___x_5357_ = v_theoryState_5343_;
v_isShared_5358_ = v_isSharedCheck_5390_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_satSolver_5355_);
lean_inc(v_preprocessCaches_5354_);
lean_inc(v_funState_5353_);
lean_dec(v_theoryState_5343_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5390_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5363_; 
v___x_5359_ = lean_unsigned_to_nat(0u);
v___x_5360_ = lean_unsigned_to_nat(16u);
v___x_5361_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v___x_5361_);
v___x_5363_ = v___x_5357_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_funState_5353_);
lean_ctor_set(v_reuseFailAlloc_5389_, 1, v___x_5361_);
lean_ctor_set(v_reuseFailAlloc_5389_, 2, v_preprocessCaches_5354_);
lean_ctor_set(v_reuseFailAlloc_5389_, 3, v_satSolver_5355_);
v___x_5363_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
lean_object* v___x_5365_; 
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 3, v___x_5363_);
v___x_5365_ = v___x_5351_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_satExpr_5344_);
lean_ctor_set(v_reuseFailAlloc_5388_, 1, v_hypQueue_5345_);
lean_ctor_set(v_reuseFailAlloc_5388_, 2, v_usedHyps_5346_);
lean_ctor_set(v_reuseFailAlloc_5388_, 3, v___x_5363_);
lean_ctor_set(v_reuseFailAlloc_5388_, 4, v_solverTimeBudgetMs_5348_);
lean_ctor_set(v_reuseFailAlloc_5388_, 5, v_roundBudget_5349_);
lean_ctor_set_uint8(v_reuseFailAlloc_5388_, sizeof(void*)*6, v_didChange_5347_);
v___x_5365_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
lean_object* v___x_5366_; lean_object* v_aig_5367_; lean_object* v_blastCache_5368_; lean_object* v_cnfCache_5369_; lean_object* v_decls_5370_; lean_object* v___f_5371_; lean_object* v___x_5372_; 
v___x_5366_ = lean_st_ref_put(v_a_3765_, v___x_5365_);
v_aig_5367_ = lean_ctor_get(v_bitvecState_5341_, 0);
lean_inc_ref(v_aig_5367_);
v_blastCache_5368_ = lean_ctor_get(v_bitvecState_5341_, 1);
lean_inc_ref(v_blastCache_5368_);
v_cnfCache_5369_ = lean_ctor_get(v_bitvecState_5341_, 2);
lean_inc_ref(v_cnfCache_5369_);
lean_dec_ref(v_bitvecState_5341_);
v_decls_5370_ = lean_ctor_get(v_aig_5367_, 0);
lean_inc_ref(v_decls_5370_);
v___f_5371_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_5371_, 0, v_aig_5367_);
lean_closure_set(v___f_5371_, 1, v_bvExpr_5338_);
lean_closure_set(v___f_5371_, 2, v_blastCache_5368_);
v___x_5372_ = lean_array_get_size(v_decls_5370_);
lean_dec_ref(v_decls_5370_);
if (v___x_4860_ == 0)
{
lean_object* v___x_5373_; uint8_t v___x_5374_; 
v___x_5373_ = l_Lean_trace_profiler;
v___x_5374_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3946_, v___x_5373_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; 
v___x_5375_ = l_IO_lazyPure___redArg(v___f_5371_);
if (lean_obj_tag(v___x_5375_) == 0)
{
lean_object* v_a_5376_; 
v_a_5376_ = lean_ctor_get(v___x_5375_, 0);
lean_inc(v_a_5376_);
lean_dec_ref_known(v___x_5375_, 1);
v___y_4892_ = v_cnfCache_5369_;
v___y_4893_ = v___x_5273_;
v___y_4894_ = v___x_5359_;
v___y_4895_ = v_tacticContext_5335_;
v___y_4896_ = v___x_5274_;
v___y_4897_ = v___x_5361_;
v___y_4898_ = v___x_5360_;
v___y_4899_ = v___x_5334_;
v___y_4900_ = v___x_5372_;
v___y_4901_ = v_a_5272_;
v_a_4902_ = v_a_5376_;
goto v___jp_4891_;
}
else
{
lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5387_; 
lean_dec_ref(v_cnfCache_5369_);
v_a_5377_ = lean_ctor_get(v___x_5375_, 0);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5375_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5379_ = v___x_5375_;
v_isShared_5380_ = v_isSharedCheck_5387_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v___x_5375_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5387_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5381_; lean_object* v___x_5383_; 
v___x_5381_ = lean_io_error_to_string(v_a_5377_);
if (v_isShared_5380_ == 0)
{
lean_ctor_set_tag(v___x_5379_, 3);
lean_ctor_set(v___x_5379_, 0, v___x_5381_);
v___x_5383_ = v___x_5379_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v___x_5381_);
v___x_5383_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5384_ = l_Lean_MessageData_ofFormat(v___x_5383_);
lean_inc(v_ref_3947_);
v___x_5385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5385_, 0, v_ref_3947_);
lean_ctor_set(v___x_5385_, 1, v___x_5384_);
v___y_4874_ = v___x_5334_;
v___y_4875_ = v_a_5272_;
v_a_4876_ = v___x_5385_;
goto v___jp_4873_;
}
}
}
}
else
{
v___y_4993_ = v_cnfCache_5369_;
v___y_4994_ = v___x_5359_;
v___y_4995_ = v___x_5273_;
v___y_4996_ = v_tacticContext_5335_;
v___y_4997_ = v___x_5274_;
v___y_4998_ = v___x_5361_;
v___y_4999_ = v___x_5360_;
v___y_5000_ = v___x_4860_;
v___y_5001_ = v___x_5334_;
v___y_5002_ = v___x_5274_;
v___y_5003_ = v___f_5371_;
v___y_5004_ = v_a_5272_;
v___y_5005_ = v___x_5372_;
goto v___jp_4992_;
}
}
else
{
v___y_4993_ = v_cnfCache_5369_;
v___y_4994_ = v___x_5359_;
v___y_4995_ = v___x_5273_;
v___y_4996_ = v_tacticContext_5335_;
v___y_4997_ = v___x_5274_;
v___y_4998_ = v___x_5361_;
v___y_4999_ = v___x_5360_;
v___y_5000_ = v___x_4860_;
v___y_5001_ = v___x_5334_;
v___y_5002_ = v___x_5274_;
v___y_5003_ = v___f_5371_;
v___y_5004_ = v_a_5272_;
v___y_5005_ = v___x_5372_;
goto v___jp_4992_;
}
}
}
}
}
}
}
}
v___jp_3779_:
{
lean_object* v___x_3796_; 
v___x_3796_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3781_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v___x_3798_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_3786_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3808_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3808_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3808_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3803_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3780_, v_a_3797_, v_a_3799_);
lean_dec(v_a_3799_);
lean_dec(v_a_3797_);
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3804_);
v___x_3806_ = v___x_3801_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_a_3797_);
lean_dec_ref(v___y_3780_);
v_a_3809_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3798_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3798_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec_ref(v___y_3780_);
v_a_3817_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3796_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3796_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
v___jp_3825_:
{
if (lean_obj_tag(v___y_3847_) == 0)
{
lean_object* v_a_3848_; uint8_t v___x_3849_; 
v_a_3848_ = lean_ctor_get(v___y_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___y_3847_, 1);
v___x_3849_ = lean_unbox(v_a_3848_);
lean_dec(v_a_3848_);
switch(v___x_3849_)
{
case 0:
{
lean_object* v_toCold_3850_; lean_object* v_options_3851_; uint8_t v_hasTrace_3852_; 
lean_dec(v___y_3830_);
lean_dec(v___y_3828_);
v_toCold_3850_ = lean_ctor_get(v___y_3834_, 0);
v_options_3851_ = lean_ctor_get(v_toCold_3850_, 2);
v_hasTrace_3852_ = lean_ctor_get_uint8(v_options_3851_, sizeof(void*)*1);
if (v_hasTrace_3852_ == 0)
{
v___y_3780_ = v___y_3831_;
v___y_3781_ = v___y_3839_;
v___y_3782_ = v___y_3840_;
v___y_3783_ = v___y_3835_;
v___y_3784_ = v___y_3837_;
v___y_3785_ = v___y_3841_;
v___y_3786_ = v___y_3833_;
v___y_3787_ = v___y_3832_;
v___y_3788_ = v___y_3843_;
v___y_3789_ = v___y_3838_;
v___y_3790_ = v___y_3836_;
v___y_3791_ = v___y_3845_;
v___y_3792_ = v___y_3827_;
v___y_3793_ = v___y_3842_;
v___y_3794_ = v___y_3834_;
v___y_3795_ = v___y_3846_;
goto v___jp_3779_;
}
else
{
lean_object* v_inheritedTraceOptions_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v_inheritedTraceOptions_3853_ = lean_ctor_get(v_toCold_3850_, 11);
v___x_3854_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_3829_);
v___x_3855_ = l_Lean_Name_append(v___x_3854_, v___y_3829_);
v___x_3856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3853_, v_options_3851_, v___x_3855_);
lean_dec(v___x_3855_);
if (v___x_3856_ == 0)
{
v___y_3780_ = v___y_3831_;
v___y_3781_ = v___y_3839_;
v___y_3782_ = v___y_3840_;
v___y_3783_ = v___y_3835_;
v___y_3784_ = v___y_3837_;
v___y_3785_ = v___y_3841_;
v___y_3786_ = v___y_3833_;
v___y_3787_ = v___y_3832_;
v___y_3788_ = v___y_3843_;
v___y_3789_ = v___y_3838_;
v___y_3790_ = v___y_3836_;
v___y_3791_ = v___y_3845_;
v___y_3792_ = v___y_3827_;
v___y_3793_ = v___y_3842_;
v___y_3794_ = v___y_3834_;
v___y_3795_ = v___y_3846_;
goto v___jp_3779_;
}
else
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
lean_inc(v___y_3829_);
v___x_3858_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_3829_, v___x_3857_, v___y_3827_, v___y_3842_, v___y_3834_, v___y_3846_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_dec_ref_known(v___x_3858_, 1);
v___y_3780_ = v___y_3831_;
v___y_3781_ = v___y_3839_;
v___y_3782_ = v___y_3840_;
v___y_3783_ = v___y_3835_;
v___y_3784_ = v___y_3837_;
v___y_3785_ = v___y_3841_;
v___y_3786_ = v___y_3833_;
v___y_3787_ = v___y_3832_;
v___y_3788_ = v___y_3843_;
v___y_3789_ = v___y_3838_;
v___y_3790_ = v___y_3836_;
v___y_3791_ = v___y_3845_;
v___y_3792_ = v___y_3827_;
v___y_3793_ = v___y_3842_;
v___y_3794_ = v___y_3834_;
v___y_3795_ = v___y_3846_;
goto v___jp_3779_;
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3831_);
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3858_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3858_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3867_; lean_object* v_satExpr_3868_; lean_object* v_hypQueue_3869_; lean_object* v_usedHyps_3870_; uint8_t v_didChange_3871_; lean_object* v_theoryState_3872_; lean_object* v_solverTimeBudgetMs_3873_; lean_object* v_roundBudget_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3831_);
v___x_3867_ = lean_st_ref_take(v___y_3835_);
v_satExpr_3868_ = lean_ctor_get(v___x_3867_, 0);
v_hypQueue_3869_ = lean_ctor_get(v___x_3867_, 1);
v_usedHyps_3870_ = lean_ctor_get(v___x_3867_, 2);
v_didChange_3871_ = lean_ctor_get_uint8(v___x_3867_, sizeof(void*)*6);
v_theoryState_3872_ = lean_ctor_get(v___x_3867_, 3);
v_solverTimeBudgetMs_3873_ = lean_ctor_get(v___x_3867_, 4);
v_roundBudget_3874_ = lean_ctor_get(v___x_3867_, 5);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3876_ = v___x_3867_;
v_isShared_3877_ = v_isSharedCheck_3935_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_roundBudget_3874_);
lean_inc(v_solverTimeBudgetMs_3873_);
lean_inc(v_theoryState_3872_);
lean_inc(v_usedHyps_3870_);
lean_inc(v_hypQueue_3869_);
lean_inc(v_satExpr_3868_);
lean_dec(v___x_3867_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3935_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3878_; lean_object* v_satSolver_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3931_; 
v___x_3878_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_3879_ = lean_ctor_get(v_theoryState_3872_, 3);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_theoryState_3872_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; lean_object* v_unused_3933_; lean_object* v_unused_3934_; 
v_unused_3932_ = lean_ctor_get(v_theoryState_3872_, 2);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_theoryState_3872_, 1);
lean_dec(v_unused_3933_);
v_unused_3934_ = lean_ctor_get(v_theoryState_3872_, 0);
lean_dec(v_unused_3934_);
v___x_3881_ = v_theoryState_3872_;
v_isShared_3882_ = v_isSharedCheck_3931_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_satSolver_3879_);
lean_dec(v_theoryState_3872_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3931_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3883_ = lean_box(0);
v___x_3884_ = lean_mk_array(v___y_3828_, v___x_3883_);
v___x_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___y_3830_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
lean_inc_ref(v___y_3844_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 2, v___x_3878_);
lean_ctor_set(v___x_3881_, 1, v___y_3844_);
lean_ctor_set(v___x_3881_, 0, v___x_3885_);
v___x_3887_ = v___x_3881_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v___y_3844_);
lean_ctor_set(v_reuseFailAlloc_3930_, 2, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_satSolver_3879_);
v___x_3887_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3889_; 
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 3, v___x_3887_);
v___x_3889_ = v___x_3876_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_satExpr_3868_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_hypQueue_3869_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_usedHyps_3870_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v___x_3887_);
lean_ctor_set(v_reuseFailAlloc_3929_, 4, v_solverTimeBudgetMs_3873_);
lean_ctor_set(v_reuseFailAlloc_3929_, 5, v_roundBudget_3874_);
lean_ctor_set_uint8(v_reuseFailAlloc_3929_, sizeof(void*)*6, v_didChange_3871_);
v___x_3889_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_st_ref_put(v___y_3835_, v___x_3889_);
v___x_3891_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_3840_, v___y_3835_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v_goal_3893_; lean_object* v___x_3894_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v_goal_3893_ = lean_ctor_get(v___y_3840_, 0);
lean_inc(v_goal_3893_);
lean_inc_ref(v___y_3826_);
v___x_3894_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v___y_3826_, v_goal_3893_, v_a_3892_, v___y_3837_, v___y_3841_, v___y_3833_, v___y_3832_, v___y_3843_, v___y_3838_, v___y_3836_, v___y_3845_, v___y_3827_, v___y_3842_, v___y_3834_, v___y_3846_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3912_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3912_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3912_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
if (lean_obj_tag(v_a_3895_) == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
lean_dec_ref_known(v_a_3895_, 1);
lean_del_object(v___x_3897_);
v___x_3899_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_3900_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_3899_, v___y_3827_, v___y_3842_, v___y_3834_, v___y_3846_);
return v___x_3900_;
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3911_; 
v_a_3901_ = lean_ctor_get(v_a_3895_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_a_3895_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3903_ = v_a_3895_;
v_isShared_3904_ = v_isSharedCheck_3911_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v_a_3895_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3911_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3908_; 
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3906_);
v___x_3908_ = v___x_3897_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
v_a_3913_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3894_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3894_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
v_a_3921_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3891_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3891_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_3936_; 
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3828_);
v___x_3936_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_3834_, v___y_3846_);
return v___x_3936_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3828_);
v_a_3937_ = lean_ctor_get(v___y_3847_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___y_3847_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___y_3847_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___y_3847_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
v___jp_3952_:
{
lean_object* v___x_3981_; double v___x_3982_; double v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3981_ = lean_io_get_num_heartbeats();
v___x_3982_ = lean_float_of_nat(v___y_3955_);
v___x_3983_ = lean_float_of_nat(v___x_3981_);
v___x_3984_ = lean_box_float(v___x_3982_);
v___x_3985_ = lean_box_float(v___x_3983_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3984_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v_a_3980_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
lean_inc_ref(v___y_3973_);
lean_inc(v___y_3969_);
v___x_3988_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_3969_, v___y_3970_, v___y_3973_, v___y_3971_, v___y_3965_, v___y_3974_, v___f_3951_, v___x_3987_, v___y_3964_, v___y_3960_, v___y_3962_, v___y_3976_, v___y_3959_, v___y_3958_, v___y_3966_, v___y_3963_, v___y_3961_, v___y_3979_, v___y_3953_, v___y_3977_, v___y_3972_, v___y_3967_);
v___y_3826_ = v___y_3968_;
v___y_3827_ = v___y_3953_;
v___y_3828_ = v___y_3954_;
v___y_3829_ = v___y_3969_;
v___y_3830_ = v___y_3956_;
v___y_3831_ = v___y_3957_;
v___y_3832_ = v___y_3958_;
v___y_3833_ = v___y_3959_;
v___y_3834_ = v___y_3972_;
v___y_3835_ = v___y_3960_;
v___y_3836_ = v___y_3961_;
v___y_3837_ = v___y_3962_;
v___y_3838_ = v___y_3963_;
v___y_3839_ = v___y_3975_;
v___y_3840_ = v___y_3964_;
v___y_3841_ = v___y_3976_;
v___y_3842_ = v___y_3977_;
v___y_3843_ = v___y_3966_;
v___y_3844_ = v___y_3978_;
v___y_3845_ = v___y_3979_;
v___y_3846_ = v___y_3967_;
v___y_3847_ = v___x_3988_;
goto v___jp_3825_;
}
v___jp_3989_:
{
lean_object* v___x_4018_; double v___x_4019_; double v___x_4020_; double v___x_4021_; double v___x_4022_; double v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4018_ = lean_io_mono_nanos_now();
v___x_4019_ = lean_float_of_nat(v___y_4001_);
v___x_4020_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4021_ = lean_float_div(v___x_4019_, v___x_4020_);
v___x_4022_ = lean_float_of_nat(v___x_4018_);
v___x_4023_ = lean_float_div(v___x_4022_, v___x_4020_);
v___x_4024_ = lean_box_float(v___x_4021_);
v___x_4025_ = lean_box_float(v___x_4023_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4027_, 0, v_a_4017_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
lean_inc_ref(v___y_4010_);
lean_inc(v___y_4006_);
v___x_4028_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_4006_, v___y_4007_, v___y_4010_, v___y_4008_, v___y_4002_, v___y_4011_, v___f_3951_, v___x_4027_, v___y_4000_, v___y_3996_, v___y_3998_, v___y_4013_, v___y_3995_, v___y_3994_, v___y_4003_, v___y_3999_, v___y_3997_, v___y_4016_, v___y_3990_, v___y_4014_, v___y_4009_, v___y_4004_);
v___y_3826_ = v___y_4005_;
v___y_3827_ = v___y_3990_;
v___y_3828_ = v___y_3991_;
v___y_3829_ = v___y_4006_;
v___y_3830_ = v___y_3992_;
v___y_3831_ = v___y_3993_;
v___y_3832_ = v___y_3994_;
v___y_3833_ = v___y_3995_;
v___y_3834_ = v___y_4009_;
v___y_3835_ = v___y_3996_;
v___y_3836_ = v___y_3997_;
v___y_3837_ = v___y_3998_;
v___y_3838_ = v___y_3999_;
v___y_3839_ = v___y_4012_;
v___y_3840_ = v___y_4000_;
v___y_3841_ = v___y_4013_;
v___y_3842_ = v___y_4014_;
v___y_3843_ = v___y_4003_;
v___y_3844_ = v___y_4015_;
v___y_3845_ = v___y_4016_;
v___y_3846_ = v___y_4004_;
v___y_3847_ = v___x_4028_;
goto v___jp_3825_;
}
v___jp_4029_:
{
lean_object* v___x_4056_; lean_object* v_a_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v___x_4056_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4044_);
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref(v___x_4056_);
v___x_4058_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4059_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4048_, v___x_4058_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = lean_io_mono_nanos_now();
v___x_4061_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4037_, v___y_4041_, v___y_4036_, v___y_4040_, v___y_4052_, v___y_4035_, v___y_4034_, v___y_4043_, v___y_4039_, v___y_4038_, v___y_4055_, v___y_4030_, v___y_4053_, v___y_4049_, v___y_4044_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4061_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4061_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
lean_ctor_set_tag(v___x_4064_, 1);
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
v___y_3990_ = v___y_4030_;
v___y_3991_ = v___y_4031_;
v___y_3992_ = v___y_4032_;
v___y_3993_ = v___y_4033_;
v___y_3994_ = v___y_4034_;
v___y_3995_ = v___y_4035_;
v___y_3996_ = v___y_4036_;
v___y_3997_ = v___y_4038_;
v___y_3998_ = v___y_4040_;
v___y_3999_ = v___y_4039_;
v___y_4000_ = v___y_4041_;
v___y_4001_ = v___x_4060_;
v___y_4002_ = v___y_4042_;
v___y_4003_ = v___y_4043_;
v___y_4004_ = v___y_4044_;
v___y_4005_ = v___y_4045_;
v___y_4006_ = v___y_4046_;
v___y_4007_ = v___y_4047_;
v___y_4008_ = v___y_4048_;
v___y_4009_ = v___y_4049_;
v___y_4010_ = v___y_4050_;
v___y_4011_ = v_a_4057_;
v___y_4012_ = v___y_4051_;
v___y_4013_ = v___y_4052_;
v___y_4014_ = v___y_4053_;
v___y_4015_ = v___y_4054_;
v___y_4016_ = v___y_4055_;
v_a_4017_ = v___x_4067_;
goto v___jp_3989_;
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
v_a_4070_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4061_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4061_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
lean_ctor_set_tag(v___x_4072_, 0);
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
v___y_3990_ = v___y_4030_;
v___y_3991_ = v___y_4031_;
v___y_3992_ = v___y_4032_;
v___y_3993_ = v___y_4033_;
v___y_3994_ = v___y_4034_;
v___y_3995_ = v___y_4035_;
v___y_3996_ = v___y_4036_;
v___y_3997_ = v___y_4038_;
v___y_3998_ = v___y_4040_;
v___y_3999_ = v___y_4039_;
v___y_4000_ = v___y_4041_;
v___y_4001_ = v___x_4060_;
v___y_4002_ = v___y_4042_;
v___y_4003_ = v___y_4043_;
v___y_4004_ = v___y_4044_;
v___y_4005_ = v___y_4045_;
v___y_4006_ = v___y_4046_;
v___y_4007_ = v___y_4047_;
v___y_4008_ = v___y_4048_;
v___y_4009_ = v___y_4049_;
v___y_4010_ = v___y_4050_;
v___y_4011_ = v_a_4057_;
v___y_4012_ = v___y_4051_;
v___y_4013_ = v___y_4052_;
v___y_4014_ = v___y_4053_;
v___y_4015_ = v___y_4054_;
v___y_4016_ = v___y_4055_;
v_a_4017_ = v___x_4075_;
goto v___jp_3989_;
}
}
}
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_io_get_num_heartbeats();
v___x_4079_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4037_, v___y_4041_, v___y_4036_, v___y_4040_, v___y_4052_, v___y_4035_, v___y_4034_, v___y_4043_, v___y_4039_, v___y_4038_, v___y_4055_, v___y_4030_, v___y_4053_, v___y_4049_, v___y_4044_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_4079_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set_tag(v___x_4082_, 1);
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
v___y_3953_ = v___y_4030_;
v___y_3954_ = v___y_4031_;
v___y_3955_ = v___x_4078_;
v___y_3956_ = v___y_4032_;
v___y_3957_ = v___y_4033_;
v___y_3958_ = v___y_4034_;
v___y_3959_ = v___y_4035_;
v___y_3960_ = v___y_4036_;
v___y_3961_ = v___y_4038_;
v___y_3962_ = v___y_4040_;
v___y_3963_ = v___y_4039_;
v___y_3964_ = v___y_4041_;
v___y_3965_ = v___y_4042_;
v___y_3966_ = v___y_4043_;
v___y_3967_ = v___y_4044_;
v___y_3968_ = v___y_4045_;
v___y_3969_ = v___y_4046_;
v___y_3970_ = v___y_4047_;
v___y_3971_ = v___y_4048_;
v___y_3972_ = v___y_4049_;
v___y_3973_ = v___y_4050_;
v___y_3974_ = v_a_4057_;
v___y_3975_ = v___y_4051_;
v___y_3976_ = v___y_4052_;
v___y_3977_ = v___y_4053_;
v___y_3978_ = v___y_4054_;
v___y_3979_ = v___y_4055_;
v_a_3980_ = v___x_4085_;
goto v___jp_3952_;
}
}
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
v_a_4088_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4079_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4079_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
lean_ctor_set_tag(v___x_4090_, 0);
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
v___y_3953_ = v___y_4030_;
v___y_3954_ = v___y_4031_;
v___y_3955_ = v___x_4078_;
v___y_3956_ = v___y_4032_;
v___y_3957_ = v___y_4033_;
v___y_3958_ = v___y_4034_;
v___y_3959_ = v___y_4035_;
v___y_3960_ = v___y_4036_;
v___y_3961_ = v___y_4038_;
v___y_3962_ = v___y_4040_;
v___y_3963_ = v___y_4039_;
v___y_3964_ = v___y_4041_;
v___y_3965_ = v___y_4042_;
v___y_3966_ = v___y_4043_;
v___y_3967_ = v___y_4044_;
v___y_3968_ = v___y_4045_;
v___y_3969_ = v___y_4046_;
v___y_3970_ = v___y_4047_;
v___y_3971_ = v___y_4048_;
v___y_3972_ = v___y_4049_;
v___y_3973_ = v___y_4050_;
v___y_3974_ = v_a_4057_;
v___y_3975_ = v___y_4051_;
v___y_3976_ = v___y_4052_;
v___y_3977_ = v___y_4053_;
v___y_3978_ = v___y_4054_;
v___y_3979_ = v___y_4055_;
v_a_3980_ = v___x_4093_;
goto v___jp_3952_;
}
}
}
}
}
v___jp_4096_:
{
lean_object* v_toCold_4123_; lean_object* v_ref_4124_; lean_object* v___x_4125_; 
v_toCold_4123_ = lean_ctor_get(v___y_4115_, 0);
v_ref_4124_ = lean_ctor_get(v___y_4115_, 2);
lean_inc_ref(v___y_4105_);
v___x_4125_ = l_Lean_Cadical_Solver_assume(v___y_4105_, v___y_4104_, v___y_4122_);
lean_dec(v___y_4104_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_options_4126_; uint8_t v_hasTrace_4127_; 
lean_dec_ref_known(v___x_4125_, 1);
v_options_4126_ = lean_ctor_get(v_toCold_4123_, 2);
v_hasTrace_4127_ = lean_ctor_get_uint8(v_options_4126_, sizeof(void*)*1);
if (v_hasTrace_4127_ == 0)
{
lean_object* v___x_4128_; 
v___x_4128_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4105_, v___y_4109_, v___y_4103_, v___y_4108_, v___y_4118_, v___y_4102_, v___y_4101_, v___y_4110_, v___y_4107_, v___y_4106_, v___y_4120_, v___y_4097_, v___y_4119_, v___y_4115_, v___y_4111_);
v___y_3826_ = v___y_4112_;
v___y_3827_ = v___y_4097_;
v___y_3828_ = v___y_4098_;
v___y_3829_ = v___y_4113_;
v___y_3830_ = v___y_4099_;
v___y_3831_ = v___y_4100_;
v___y_3832_ = v___y_4101_;
v___y_3833_ = v___y_4102_;
v___y_3834_ = v___y_4115_;
v___y_3835_ = v___y_4103_;
v___y_3836_ = v___y_4106_;
v___y_3837_ = v___y_4108_;
v___y_3838_ = v___y_4107_;
v___y_3839_ = v___y_4117_;
v___y_3840_ = v___y_4109_;
v___y_3841_ = v___y_4118_;
v___y_3842_ = v___y_4119_;
v___y_3843_ = v___y_4110_;
v___y_3844_ = v___y_4121_;
v___y_3845_ = v___y_4120_;
v___y_3846_ = v___y_4111_;
v___y_3847_ = v___x_4128_;
goto v___jp_3825_;
}
else
{
lean_object* v_inheritedTraceOptions_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v_inheritedTraceOptions_4129_ = lean_ctor_get(v_toCold_4123_, 11);
v___x_4130_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_4113_);
v___x_4131_ = l_Lean_Name_append(v___x_4130_, v___y_4113_);
v___x_4132_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4129_, v_options_4126_, v___x_4131_);
lean_dec(v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4133_ = l_Lean_trace_profiler;
v___x_4134_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4126_, v___x_4133_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; 
v___x_4135_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4105_, v___y_4109_, v___y_4103_, v___y_4108_, v___y_4118_, v___y_4102_, v___y_4101_, v___y_4110_, v___y_4107_, v___y_4106_, v___y_4120_, v___y_4097_, v___y_4119_, v___y_4115_, v___y_4111_);
v___y_3826_ = v___y_4112_;
v___y_3827_ = v___y_4097_;
v___y_3828_ = v___y_4098_;
v___y_3829_ = v___y_4113_;
v___y_3830_ = v___y_4099_;
v___y_3831_ = v___y_4100_;
v___y_3832_ = v___y_4101_;
v___y_3833_ = v___y_4102_;
v___y_3834_ = v___y_4115_;
v___y_3835_ = v___y_4103_;
v___y_3836_ = v___y_4106_;
v___y_3837_ = v___y_4108_;
v___y_3838_ = v___y_4107_;
v___y_3839_ = v___y_4117_;
v___y_3840_ = v___y_4109_;
v___y_3841_ = v___y_4118_;
v___y_3842_ = v___y_4119_;
v___y_3843_ = v___y_4110_;
v___y_3844_ = v___y_4121_;
v___y_3845_ = v___y_4120_;
v___y_3846_ = v___y_4111_;
v___y_3847_ = v___x_4135_;
goto v___jp_3825_;
}
else
{
v___y_4030_ = v___y_4097_;
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___y_4099_;
v___y_4033_ = v___y_4100_;
v___y_4034_ = v___y_4101_;
v___y_4035_ = v___y_4102_;
v___y_4036_ = v___y_4103_;
v___y_4037_ = v___y_4105_;
v___y_4038_ = v___y_4106_;
v___y_4039_ = v___y_4107_;
v___y_4040_ = v___y_4108_;
v___y_4041_ = v___y_4109_;
v___y_4042_ = v___x_4132_;
v___y_4043_ = v___y_4110_;
v___y_4044_ = v___y_4111_;
v___y_4045_ = v___y_4112_;
v___y_4046_ = v___y_4113_;
v___y_4047_ = v___y_4114_;
v___y_4048_ = v_options_4126_;
v___y_4049_ = v___y_4115_;
v___y_4050_ = v___y_4116_;
v___y_4051_ = v___y_4117_;
v___y_4052_ = v___y_4118_;
v___y_4053_ = v___y_4119_;
v___y_4054_ = v___y_4121_;
v___y_4055_ = v___y_4120_;
goto v___jp_4029_;
}
}
else
{
v___y_4030_ = v___y_4097_;
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___y_4099_;
v___y_4033_ = v___y_4100_;
v___y_4034_ = v___y_4101_;
v___y_4035_ = v___y_4102_;
v___y_4036_ = v___y_4103_;
v___y_4037_ = v___y_4105_;
v___y_4038_ = v___y_4106_;
v___y_4039_ = v___y_4107_;
v___y_4040_ = v___y_4108_;
v___y_4041_ = v___y_4109_;
v___y_4042_ = v___x_4132_;
v___y_4043_ = v___y_4110_;
v___y_4044_ = v___y_4111_;
v___y_4045_ = v___y_4112_;
v___y_4046_ = v___y_4113_;
v___y_4047_ = v___y_4114_;
v___y_4048_ = v_options_4126_;
v___y_4049_ = v___y_4115_;
v___y_4050_ = v___y_4116_;
v___y_4051_ = v___y_4117_;
v___y_4052_ = v___y_4118_;
v___y_4053_ = v___y_4119_;
v___y_4054_ = v___y_4121_;
v___y_4055_ = v___y_4120_;
goto v___jp_4029_;
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4105_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec(v___y_4098_);
v_a_4136_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4138_ = v___x_4125_;
v_isShared_4139_ = v_isSharedCheck_4147_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4125_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4147_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
v___x_4140_ = lean_io_error_to_string(v_a_4136_);
v___x_4141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4140_);
v___x_4142_ = l_Lean_MessageData_ofFormat(v___x_4141_);
lean_inc(v_ref_4124_);
v___x_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4143_, 0, v_ref_4124_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v___x_4143_);
v___x_4145_ = v___x_4138_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
v___jp_4148_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v_theoryState_4179_; lean_object* v_satExpr_4180_; lean_object* v_hypQueue_4181_; lean_object* v_usedHyps_4182_; uint8_t v_didChange_4183_; lean_object* v_solverTimeBudgetMs_4184_; lean_object* v_roundBudget_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4228_; 
lean_inc_ref(v___y_4154_);
v___x_4177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4177_, 0, v___y_4154_);
lean_ctor_set(v___x_4177_, 1, v___y_4160_);
lean_ctor_set(v___x_4177_, 2, v___y_4161_);
v___x_4178_ = lean_st_ref_take(v___y_4164_);
v_theoryState_4179_ = lean_ctor_get(v___x_4178_, 3);
v_satExpr_4180_ = lean_ctor_get(v___x_4178_, 0);
v_hypQueue_4181_ = lean_ctor_get(v___x_4178_, 1);
v_usedHyps_4182_ = lean_ctor_get(v___x_4178_, 2);
v_didChange_4183_ = lean_ctor_get_uint8(v___x_4178_, sizeof(void*)*6);
v_solverTimeBudgetMs_4184_ = lean_ctor_get(v___x_4178_, 4);
v_roundBudget_4185_ = lean_ctor_get(v___x_4178_, 5);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4187_ = v___x_4178_;
v_isShared_4188_ = v_isSharedCheck_4228_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_roundBudget_4185_);
lean_inc(v_solverTimeBudgetMs_4184_);
lean_inc(v_theoryState_4179_);
lean_inc(v_usedHyps_4182_);
lean_inc(v_hypQueue_4181_);
lean_inc(v_satExpr_4180_);
lean_dec(v___x_4178_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4228_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v_funState_4189_; lean_object* v_preprocessCaches_4190_; lean_object* v_satSolver_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4226_; 
v_funState_4189_ = lean_ctor_get(v_theoryState_4179_, 0);
v_preprocessCaches_4190_ = lean_ctor_get(v_theoryState_4179_, 2);
v_satSolver_4191_ = lean_ctor_get(v_theoryState_4179_, 3);
v_isSharedCheck_4226_ = !lean_is_exclusive(v_theoryState_4179_);
if (v_isSharedCheck_4226_ == 0)
{
lean_object* v_unused_4227_; 
v_unused_4227_ = lean_ctor_get(v_theoryState_4179_, 1);
lean_dec(v_unused_4227_);
v___x_4193_ = v_theoryState_4179_;
v_isShared_4194_ = v_isSharedCheck_4226_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_satSolver_4191_);
lean_inc(v_preprocessCaches_4190_);
lean_inc(v_funState_4189_);
lean_dec(v_theoryState_4179_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4226_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 1, v___x_4177_);
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_funState_4189_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4225_, 2, v_preprocessCaches_4190_);
lean_ctor_set(v_reuseFailAlloc_4225_, 3, v_satSolver_4191_);
v___x_4196_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4198_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 3, v___x_4196_);
v___x_4198_ = v___x_4187_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_satExpr_4180_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_hypQueue_4181_);
lean_ctor_set(v_reuseFailAlloc_4224_, 2, v_usedHyps_4182_);
lean_ctor_set(v_reuseFailAlloc_4224_, 3, v___x_4196_);
lean_ctor_set(v_reuseFailAlloc_4224_, 4, v_solverTimeBudgetMs_4184_);
lean_ctor_set(v_reuseFailAlloc_4224_, 5, v_roundBudget_4185_);
lean_ctor_set_uint8(v_reuseFailAlloc_4224_, sizeof(void*)*6, v_didChange_4183_);
v___x_4198_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = lean_st_ref_put(v___y_4164_, v___x_4198_);
v___x_4200_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_4152_, v___y_4155_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v___x_4201_; 
lean_dec_ref_known(v___x_4200_, 1);
v___x_4201_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_4164_);
if (lean_obj_tag(v___x_4201_) == 0)
{
uint8_t v_invert_4202_; 
v_invert_4202_ = lean_ctor_get_uint8(v___y_4157_, sizeof(void*)*1);
if (v_invert_4202_ == 0)
{
lean_object* v_a_4203_; lean_object* v_gate_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4201_, 1);
v_gate_4204_ = lean_ctor_get(v___y_4157_, 0);
lean_inc(v_gate_4204_);
lean_dec_ref(v___y_4157_);
v___y_4097_ = v___y_4173_;
v___y_4098_ = v___y_4150_;
v___y_4099_ = v___y_4153_;
v___y_4100_ = v___y_4154_;
v___y_4101_ = v___y_4168_;
v___y_4102_ = v___y_4167_;
v___y_4103_ = v___y_4164_;
v___y_4104_ = v_gate_4204_;
v___y_4105_ = v_a_4203_;
v___y_4106_ = v___y_4171_;
v___y_4107_ = v___y_4170_;
v___y_4108_ = v___y_4165_;
v___y_4109_ = v___y_4163_;
v___y_4110_ = v___y_4169_;
v___y_4111_ = v___y_4176_;
v___y_4112_ = v___y_4149_;
v___y_4113_ = v___y_4151_;
v___y_4114_ = v___y_4156_;
v___y_4115_ = v___y_4175_;
v___y_4116_ = v___y_4158_;
v___y_4117_ = v___y_4159_;
v___y_4118_ = v___y_4166_;
v___y_4119_ = v___y_4174_;
v___y_4120_ = v___y_4172_;
v___y_4121_ = v___y_4162_;
v___y_4122_ = v___y_4156_;
goto v___jp_4096_;
}
else
{
lean_object* v_a_4205_; lean_object* v_gate_4206_; uint8_t v___x_4207_; 
v_a_4205_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4201_, 1);
v_gate_4206_ = lean_ctor_get(v___y_4157_, 0);
lean_inc(v_gate_4206_);
lean_dec_ref(v___y_4157_);
v___x_4207_ = 0;
v___y_4097_ = v___y_4173_;
v___y_4098_ = v___y_4150_;
v___y_4099_ = v___y_4153_;
v___y_4100_ = v___y_4154_;
v___y_4101_ = v___y_4168_;
v___y_4102_ = v___y_4167_;
v___y_4103_ = v___y_4164_;
v___y_4104_ = v_gate_4206_;
v___y_4105_ = v_a_4205_;
v___y_4106_ = v___y_4171_;
v___y_4107_ = v___y_4170_;
v___y_4108_ = v___y_4165_;
v___y_4109_ = v___y_4163_;
v___y_4110_ = v___y_4169_;
v___y_4111_ = v___y_4176_;
v___y_4112_ = v___y_4149_;
v___y_4113_ = v___y_4151_;
v___y_4114_ = v___y_4156_;
v___y_4115_ = v___y_4175_;
v___y_4116_ = v___y_4158_;
v___y_4117_ = v___y_4159_;
v___y_4118_ = v___y_4166_;
v___y_4119_ = v___y_4174_;
v___y_4120_ = v___y_4172_;
v___y_4121_ = v___y_4162_;
v___y_4122_ = v___x_4207_;
goto v___jp_4096_;
}
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4157_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec(v___y_4150_);
v_a_4208_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4201_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4201_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4157_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec(v___y_4150_);
v_a_4216_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4200_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4200_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
}
}
}
}
v___jp_4234_:
{
if (lean_obj_tag(v___y_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v_toCold_4263_; lean_object* v_options_4264_; uint8_t v_hasTrace_4265_; 
v_a_4262_ = lean_ctor_get(v___y_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___y_4261_, 1);
v_toCold_4263_ = lean_ctor_get(v___y_4249_, 0);
v_options_4264_ = lean_ctor_get(v_toCold_4263_, 2);
v_hasTrace_4265_ = lean_ctor_get_uint8(v_options_4264_, sizeof(void*)*1);
if (v_hasTrace_4265_ == 0)
{
lean_object* v_cnf_4266_; 
v_cnf_4266_ = lean_ctor_get(v_a_4262_, 0);
lean_inc_ref(v_cnf_4266_);
v___y_4149_ = v___y_4245_;
v___y_4150_ = v___y_4235_;
v___y_4151_ = v___y_4247_;
v___y_4152_ = v___y_4236_;
v___y_4153_ = v___y_4238_;
v___y_4154_ = v___y_4237_;
v___y_4155_ = v_cnf_4266_;
v___y_4156_ = v___y_4248_;
v___y_4157_ = v___y_4253_;
v___y_4158_ = v___y_4255_;
v___y_4159_ = v___y_4258_;
v___y_4160_ = v___y_4243_;
v___y_4161_ = v_a_4262_;
v___y_4162_ = v___y_4260_;
v___y_4163_ = v___y_4256_;
v___y_4164_ = v___y_4240_;
v___y_4165_ = v___y_4250_;
v___y_4166_ = v___y_4239_;
v___y_4167_ = v___y_4244_;
v___y_4168_ = v___y_4241_;
v___y_4169_ = v___y_4252_;
v___y_4170_ = v___y_4246_;
v___y_4171_ = v___y_4242_;
v___y_4172_ = v___y_4257_;
v___y_4173_ = v___y_4259_;
v___y_4174_ = v___y_4254_;
v___y_4175_ = v___y_4249_;
v___y_4176_ = v___y_4251_;
goto v___jp_4148_;
}
else
{
lean_object* v_cnf_4267_; lean_object* v_inheritedTraceOptions_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; 
v_cnf_4267_ = lean_ctor_get(v_a_4262_, 0);
lean_inc_ref(v_cnf_4267_);
v_inheritedTraceOptions_4268_ = lean_ctor_get(v_toCold_4263_, 11);
v___x_4269_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4270_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4268_, v_options_4264_, v___x_4269_);
if (v___x_4270_ == 0)
{
v___y_4149_ = v___y_4245_;
v___y_4150_ = v___y_4235_;
v___y_4151_ = v___y_4247_;
v___y_4152_ = v___y_4236_;
v___y_4153_ = v___y_4238_;
v___y_4154_ = v___y_4237_;
v___y_4155_ = v_cnf_4267_;
v___y_4156_ = v___y_4248_;
v___y_4157_ = v___y_4253_;
v___y_4158_ = v___y_4255_;
v___y_4159_ = v___y_4258_;
v___y_4160_ = v___y_4243_;
v___y_4161_ = v_a_4262_;
v___y_4162_ = v___y_4260_;
v___y_4163_ = v___y_4256_;
v___y_4164_ = v___y_4240_;
v___y_4165_ = v___y_4250_;
v___y_4166_ = v___y_4239_;
v___y_4167_ = v___y_4244_;
v___y_4168_ = v___y_4241_;
v___y_4169_ = v___y_4252_;
v___y_4170_ = v___y_4246_;
v___y_4171_ = v___y_4242_;
v___y_4172_ = v___y_4257_;
v___y_4173_ = v___y_4259_;
v___y_4174_ = v___y_4254_;
v___y_4175_ = v___y_4249_;
v___y_4176_ = v___y_4251_;
goto v___jp_4148_;
}
else
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4271_ = lean_array_get_size(v_cnf_4267_);
v___x_4272_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_4273_ = l_Nat_reprFast(v___x_4271_);
v___x_4274_ = lean_string_append(v___x_4272_, v___x_4273_);
lean_dec_ref(v___x_4273_);
v___x_4275_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_4276_ = lean_string_append(v___x_4274_, v___x_4275_);
v___x_4277_ = lean_nat_sub(v___x_4271_, v___y_4236_);
v___x_4278_ = l_Nat_reprFast(v___x_4277_);
v___x_4279_ = lean_string_append(v___x_4276_, v___x_4278_);
lean_dec_ref(v___x_4278_);
v___x_4280_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_4281_ = lean_string_append(v___x_4279_, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
v___x_4283_ = l_Lean_MessageData_ofFormat(v___x_4282_);
v___x_4284_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4233_, v___x_4283_, v___y_4259_, v___y_4254_, v___y_4249_, v___y_4251_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_dec_ref_known(v___x_4284_, 1);
v___y_4149_ = v___y_4245_;
v___y_4150_ = v___y_4235_;
v___y_4151_ = v___y_4247_;
v___y_4152_ = v___y_4236_;
v___y_4153_ = v___y_4238_;
v___y_4154_ = v___y_4237_;
v___y_4155_ = v_cnf_4267_;
v___y_4156_ = v___y_4248_;
v___y_4157_ = v___y_4253_;
v___y_4158_ = v___y_4255_;
v___y_4159_ = v___y_4258_;
v___y_4160_ = v___y_4243_;
v___y_4161_ = v_a_4262_;
v___y_4162_ = v___y_4260_;
v___y_4163_ = v___y_4256_;
v___y_4164_ = v___y_4240_;
v___y_4165_ = v___y_4250_;
v___y_4166_ = v___y_4239_;
v___y_4167_ = v___y_4244_;
v___y_4168_ = v___y_4241_;
v___y_4169_ = v___y_4252_;
v___y_4170_ = v___y_4246_;
v___y_4171_ = v___y_4242_;
v___y_4172_ = v___y_4257_;
v___y_4173_ = v___y_4259_;
v___y_4174_ = v___y_4254_;
v___y_4175_ = v___y_4249_;
v___y_4176_ = v___y_4251_;
goto v___jp_4148_;
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec_ref(v_cnf_4267_);
lean_dec(v_a_4262_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec(v___y_4235_);
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4284_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4284_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec(v___y_4235_);
v_a_4293_ = lean_ctor_get(v___y_4261_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___y_4261_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___y_4261_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___y_4261_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
v___jp_4301_:
{
lean_object* v___x_4333_; double v___x_4334_; double v___x_4335_; double v___x_4336_; double v___x_4337_; double v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4333_ = lean_io_mono_nanos_now();
v___x_4334_ = lean_float_of_nat(v___y_4331_);
v___x_4335_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4336_ = lean_float_div(v___x_4334_, v___x_4335_);
v___x_4337_ = lean_float_of_nat(v___x_4333_);
v___x_4338_ = lean_float_div(v___x_4337_, v___x_4335_);
v___x_4339_ = lean_box_float(v___x_4336_);
v___x_4340_ = lean_box_float(v___x_4338_);
v___x_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4339_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v_a_4332_);
lean_ctor_set(v___x_4342_, 1, v___x_4341_);
lean_inc_ref(v___y_4325_);
lean_inc(v___y_4316_);
v___x_4343_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_4316_, v___y_4317_, v___y_4325_, v___y_4304_, v___y_4318_, v___y_4308_, v___f_3950_, v___x_4342_, v___y_4326_, v___y_4310_, v___y_4320_, v___y_4307_, v___y_4313_, v___y_4309_, v___y_4321_, v___y_4315_, v___y_4311_, v___y_4327_, v___y_4329_, v___y_4324_, v___y_4319_, v___y_4322_);
v___y_4235_ = v___y_4302_;
v___y_4236_ = v___y_4303_;
v___y_4237_ = v___y_4305_;
v___y_4238_ = v___y_4306_;
v___y_4239_ = v___y_4307_;
v___y_4240_ = v___y_4310_;
v___y_4241_ = v___y_4309_;
v___y_4242_ = v___y_4311_;
v___y_4243_ = v___y_4312_;
v___y_4244_ = v___y_4313_;
v___y_4245_ = v___y_4314_;
v___y_4246_ = v___y_4315_;
v___y_4247_ = v___y_4316_;
v___y_4248_ = v___y_4317_;
v___y_4249_ = v___y_4319_;
v___y_4250_ = v___y_4320_;
v___y_4251_ = v___y_4322_;
v___y_4252_ = v___y_4321_;
v___y_4253_ = v___y_4323_;
v___y_4254_ = v___y_4324_;
v___y_4255_ = v___y_4325_;
v___y_4256_ = v___y_4326_;
v___y_4257_ = v___y_4327_;
v___y_4258_ = v___y_4328_;
v___y_4259_ = v___y_4329_;
v___y_4260_ = v___y_4330_;
v___y_4261_ = v___x_4343_;
goto v___jp_4234_;
}
v___jp_4344_:
{
lean_object* v___x_4376_; double v___x_4377_; double v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4376_ = lean_io_get_num_heartbeats();
v___x_4377_ = lean_float_of_nat(v___y_4373_);
v___x_4378_ = lean_float_of_nat(v___x_4376_);
v___x_4379_ = lean_box_float(v___x_4377_);
v___x_4380_ = lean_box_float(v___x_4378_);
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4379_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
v___x_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4382_, 0, v_a_4375_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
lean_inc_ref(v___y_4368_);
lean_inc(v___y_4359_);
v___x_4383_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_4359_, v___y_4360_, v___y_4368_, v___y_4347_, v___y_4361_, v___y_4351_, v___f_3950_, v___x_4382_, v___y_4369_, v___y_4353_, v___y_4363_, v___y_4350_, v___y_4356_, v___y_4352_, v___y_4364_, v___y_4358_, v___y_4354_, v___y_4370_, v___y_4372_, v___y_4367_, v___y_4362_, v___y_4365_);
v___y_4235_ = v___y_4345_;
v___y_4236_ = v___y_4346_;
v___y_4237_ = v___y_4348_;
v___y_4238_ = v___y_4349_;
v___y_4239_ = v___y_4350_;
v___y_4240_ = v___y_4353_;
v___y_4241_ = v___y_4352_;
v___y_4242_ = v___y_4354_;
v___y_4243_ = v___y_4355_;
v___y_4244_ = v___y_4356_;
v___y_4245_ = v___y_4357_;
v___y_4246_ = v___y_4358_;
v___y_4247_ = v___y_4359_;
v___y_4248_ = v___y_4360_;
v___y_4249_ = v___y_4362_;
v___y_4250_ = v___y_4363_;
v___y_4251_ = v___y_4365_;
v___y_4252_ = v___y_4364_;
v___y_4253_ = v___y_4366_;
v___y_4254_ = v___y_4367_;
v___y_4255_ = v___y_4368_;
v___y_4256_ = v___y_4369_;
v___y_4257_ = v___y_4370_;
v___y_4258_ = v___y_4371_;
v___y_4259_ = v___y_4372_;
v___y_4260_ = v___y_4374_;
v___y_4261_ = v___x_4383_;
goto v___jp_4234_;
}
v___jp_4384_:
{
lean_object* v___x_4415_; lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4470_; 
v___x_4415_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4406_);
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4418_ = v___x_4415_;
v_isShared_4419_ = v_isSharedCheck_4470_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4415_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4470_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4420_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4421_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4387_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4422_ = lean_io_mono_nanos_now();
v___x_4423_ = l_IO_lazyPure___redArg(v___y_4404_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_del_object(v___x_4418_);
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4423_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
lean_ctor_set_tag(v___x_4426_, 1);
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
v___y_4302_ = v___y_4385_;
v___y_4303_ = v___y_4386_;
v___y_4304_ = v___y_4387_;
v___y_4305_ = v___y_4388_;
v___y_4306_ = v___y_4389_;
v___y_4307_ = v___y_4390_;
v___y_4308_ = v_a_4416_;
v___y_4309_ = v___y_4392_;
v___y_4310_ = v___y_4393_;
v___y_4311_ = v___y_4391_;
v___y_4312_ = v___y_4395_;
v___y_4313_ = v___y_4394_;
v___y_4314_ = v___y_4397_;
v___y_4315_ = v___y_4396_;
v___y_4316_ = v___y_4398_;
v___y_4317_ = v___y_4399_;
v___y_4318_ = v___y_4400_;
v___y_4319_ = v___y_4401_;
v___y_4320_ = v___y_4402_;
v___y_4321_ = v___y_4405_;
v___y_4322_ = v___y_4406_;
v___y_4323_ = v___y_4407_;
v___y_4324_ = v___y_4408_;
v___y_4325_ = v___y_4409_;
v___y_4326_ = v___y_4411_;
v___y_4327_ = v___y_4410_;
v___y_4328_ = v___y_4412_;
v___y_4329_ = v___y_4413_;
v___y_4330_ = v___y_4414_;
v___y_4331_ = v___x_4422_;
v_a_4332_ = v___x_4429_;
goto v___jp_4301_;
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4445_; 
v_a_4432_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4434_ = v___x_4423_;
v_isShared_4435_ = v_isSharedCheck_4445_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4423_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4445_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
v___x_4436_ = lean_io_error_to_string(v_a_4432_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set_tag(v___x_4434_, 3);
lean_ctor_set(v___x_4434_, 0, v___x_4436_);
v___x_4438_ = v___x_4434_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4439_ = l_Lean_MessageData_ofFormat(v___x_4438_);
lean_inc(v___y_4403_);
v___x_4440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___y_4403_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4440_);
v___x_4442_ = v___x_4418_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
v___y_4302_ = v___y_4385_;
v___y_4303_ = v___y_4386_;
v___y_4304_ = v___y_4387_;
v___y_4305_ = v___y_4388_;
v___y_4306_ = v___y_4389_;
v___y_4307_ = v___y_4390_;
v___y_4308_ = v_a_4416_;
v___y_4309_ = v___y_4392_;
v___y_4310_ = v___y_4393_;
v___y_4311_ = v___y_4391_;
v___y_4312_ = v___y_4395_;
v___y_4313_ = v___y_4394_;
v___y_4314_ = v___y_4397_;
v___y_4315_ = v___y_4396_;
v___y_4316_ = v___y_4398_;
v___y_4317_ = v___y_4399_;
v___y_4318_ = v___y_4400_;
v___y_4319_ = v___y_4401_;
v___y_4320_ = v___y_4402_;
v___y_4321_ = v___y_4405_;
v___y_4322_ = v___y_4406_;
v___y_4323_ = v___y_4407_;
v___y_4324_ = v___y_4408_;
v___y_4325_ = v___y_4409_;
v___y_4326_ = v___y_4411_;
v___y_4327_ = v___y_4410_;
v___y_4328_ = v___y_4412_;
v___y_4329_ = v___y_4413_;
v___y_4330_ = v___y_4414_;
v___y_4331_ = v___x_4422_;
v_a_4332_ = v___x_4442_;
goto v___jp_4301_;
}
}
}
}
}
else
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = lean_io_get_num_heartbeats();
v___x_4447_ = l_IO_lazyPure___redArg(v___y_4404_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_del_object(v___x_4418_);
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4447_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4447_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
lean_ctor_set_tag(v___x_4450_, 1);
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
v___y_4345_ = v___y_4385_;
v___y_4346_ = v___y_4386_;
v___y_4347_ = v___y_4387_;
v___y_4348_ = v___y_4388_;
v___y_4349_ = v___y_4389_;
v___y_4350_ = v___y_4390_;
v___y_4351_ = v_a_4416_;
v___y_4352_ = v___y_4392_;
v___y_4353_ = v___y_4393_;
v___y_4354_ = v___y_4391_;
v___y_4355_ = v___y_4395_;
v___y_4356_ = v___y_4394_;
v___y_4357_ = v___y_4397_;
v___y_4358_ = v___y_4396_;
v___y_4359_ = v___y_4398_;
v___y_4360_ = v___y_4399_;
v___y_4361_ = v___y_4400_;
v___y_4362_ = v___y_4401_;
v___y_4363_ = v___y_4402_;
v___y_4364_ = v___y_4405_;
v___y_4365_ = v___y_4406_;
v___y_4366_ = v___y_4407_;
v___y_4367_ = v___y_4408_;
v___y_4368_ = v___y_4409_;
v___y_4369_ = v___y_4411_;
v___y_4370_ = v___y_4410_;
v___y_4371_ = v___y_4412_;
v___y_4372_ = v___y_4413_;
v___y_4373_ = v___x_4446_;
v___y_4374_ = v___y_4414_;
v_a_4375_ = v___x_4453_;
goto v___jp_4344_;
}
}
}
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4469_; 
v_a_4456_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4458_ = v___x_4447_;
v_isShared_4459_ = v_isSharedCheck_4469_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4447_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4469_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4460_ = lean_io_error_to_string(v_a_4456_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set_tag(v___x_4458_, 3);
lean_ctor_set(v___x_4458_, 0, v___x_4460_);
v___x_4462_ = v___x_4458_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
v___x_4463_ = l_Lean_MessageData_ofFormat(v___x_4462_);
lean_inc(v___y_4403_);
v___x_4464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4464_, 0, v___y_4403_);
lean_ctor_set(v___x_4464_, 1, v___x_4463_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4464_);
v___x_4466_ = v___x_4418_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
v___y_4345_ = v___y_4385_;
v___y_4346_ = v___y_4386_;
v___y_4347_ = v___y_4387_;
v___y_4348_ = v___y_4388_;
v___y_4349_ = v___y_4389_;
v___y_4350_ = v___y_4390_;
v___y_4351_ = v_a_4416_;
v___y_4352_ = v___y_4392_;
v___y_4353_ = v___y_4393_;
v___y_4354_ = v___y_4391_;
v___y_4355_ = v___y_4395_;
v___y_4356_ = v___y_4394_;
v___y_4357_ = v___y_4397_;
v___y_4358_ = v___y_4396_;
v___y_4359_ = v___y_4398_;
v___y_4360_ = v___y_4399_;
v___y_4361_ = v___y_4400_;
v___y_4362_ = v___y_4401_;
v___y_4363_ = v___y_4402_;
v___y_4364_ = v___y_4405_;
v___y_4365_ = v___y_4406_;
v___y_4366_ = v___y_4407_;
v___y_4367_ = v___y_4408_;
v___y_4368_ = v___y_4409_;
v___y_4369_ = v___y_4411_;
v___y_4370_ = v___y_4410_;
v___y_4371_ = v___y_4412_;
v___y_4372_ = v___y_4413_;
v___y_4373_ = v___x_4446_;
v___y_4374_ = v___y_4414_;
v_a_4375_ = v___x_4466_;
goto v___jp_4344_;
}
}
}
}
}
}
}
v___jp_4471_:
{
lean_object* v_toCold_4498_; lean_object* v_options_4499_; lean_object* v_cnf_4500_; lean_object* v_ref_4501_; lean_object* v_inheritedTraceOptions_4502_; uint8_t v_hasTrace_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___f_4507_; lean_object* v___x_4508_; 
v_toCold_4498_ = lean_ctor_get(v___y_4496_, 0);
v_options_4499_ = lean_ctor_get(v_toCold_4498_, 2);
v_cnf_4500_ = lean_ctor_get(v___y_4474_, 0);
v_ref_4501_ = lean_ctor_get(v___y_4496_, 2);
v_inheritedTraceOptions_4502_ = lean_ctor_get(v_toCold_4498_, 11);
v_hasTrace_4503_ = lean_ctor_get_uint8(v_options_4499_, sizeof(void*)*1);
v___x_4504_ = lean_array_get_size(v_cnf_4500_);
v___x_4505_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_4506_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v___y_4479_, v___y_4474_);
v___f_4507_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_4507_, 0, v___x_4230_);
lean_closure_set(v___f_4507_, 1, v___x_4505_);
lean_closure_set(v___f_4507_, 2, v___y_4472_);
lean_closure_set(v___f_4507_, 3, v___x_4506_);
v___x_4508_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9));
if (v_hasTrace_4503_ == 0)
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_4507_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
v___y_4235_ = v___y_4475_;
v___y_4236_ = v___x_4504_;
v___y_4237_ = v___y_4479_;
v___y_4238_ = v___y_4478_;
v___y_4239_ = v___y_4487_;
v___y_4240_ = v___y_4485_;
v___y_4241_ = v___y_4489_;
v___y_4242_ = v___y_4492_;
v___y_4243_ = v___y_4482_;
v___y_4244_ = v___y_4488_;
v___y_4245_ = v___y_4473_;
v___y_4246_ = v___y_4491_;
v___y_4247_ = v___x_4508_;
v___y_4248_ = v___y_4480_;
v___y_4249_ = v___y_4496_;
v___y_4250_ = v___y_4486_;
v___y_4251_ = v___y_4497_;
v___y_4252_ = v___y_4490_;
v___y_4253_ = v___y_4476_;
v___y_4254_ = v___y_4495_;
v___y_4255_ = v___y_4477_;
v___y_4256_ = v___y_4484_;
v___y_4257_ = v___y_4493_;
v___y_4258_ = v___y_4481_;
v___y_4259_ = v___y_4494_;
v___y_4260_ = v___y_4483_;
v___y_4261_ = v___x_4509_;
goto v___jp_4234_;
}
else
{
lean_object* v___x_4510_; uint8_t v___x_4511_; 
v___x_4510_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10);
v___x_4511_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4502_, v_options_4499_, v___x_4510_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4512_ = l_Lean_trace_profiler;
v___x_4513_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4499_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; 
v___x_4514_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_4507_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
v___y_4235_ = v___y_4475_;
v___y_4236_ = v___x_4504_;
v___y_4237_ = v___y_4479_;
v___y_4238_ = v___y_4478_;
v___y_4239_ = v___y_4487_;
v___y_4240_ = v___y_4485_;
v___y_4241_ = v___y_4489_;
v___y_4242_ = v___y_4492_;
v___y_4243_ = v___y_4482_;
v___y_4244_ = v___y_4488_;
v___y_4245_ = v___y_4473_;
v___y_4246_ = v___y_4491_;
v___y_4247_ = v___x_4508_;
v___y_4248_ = v___y_4480_;
v___y_4249_ = v___y_4496_;
v___y_4250_ = v___y_4486_;
v___y_4251_ = v___y_4497_;
v___y_4252_ = v___y_4490_;
v___y_4253_ = v___y_4476_;
v___y_4254_ = v___y_4495_;
v___y_4255_ = v___y_4477_;
v___y_4256_ = v___y_4484_;
v___y_4257_ = v___y_4493_;
v___y_4258_ = v___y_4481_;
v___y_4259_ = v___y_4494_;
v___y_4260_ = v___y_4483_;
v___y_4261_ = v___x_4514_;
goto v___jp_4234_;
}
else
{
v___y_4385_ = v___y_4475_;
v___y_4386_ = v___x_4504_;
v___y_4387_ = v_options_4499_;
v___y_4388_ = v___y_4479_;
v___y_4389_ = v___y_4478_;
v___y_4390_ = v___y_4487_;
v___y_4391_ = v___y_4492_;
v___y_4392_ = v___y_4489_;
v___y_4393_ = v___y_4485_;
v___y_4394_ = v___y_4488_;
v___y_4395_ = v___y_4482_;
v___y_4396_ = v___y_4491_;
v___y_4397_ = v___y_4473_;
v___y_4398_ = v___x_4508_;
v___y_4399_ = v___y_4480_;
v___y_4400_ = v___x_4511_;
v___y_4401_ = v___y_4496_;
v___y_4402_ = v___y_4486_;
v___y_4403_ = v_ref_4501_;
v___y_4404_ = v___f_4507_;
v___y_4405_ = v___y_4490_;
v___y_4406_ = v___y_4497_;
v___y_4407_ = v___y_4476_;
v___y_4408_ = v___y_4495_;
v___y_4409_ = v___y_4477_;
v___y_4410_ = v___y_4493_;
v___y_4411_ = v___y_4484_;
v___y_4412_ = v___y_4481_;
v___y_4413_ = v___y_4494_;
v___y_4414_ = v___y_4483_;
goto v___jp_4384_;
}
}
else
{
v___y_4385_ = v___y_4475_;
v___y_4386_ = v___x_4504_;
v___y_4387_ = v_options_4499_;
v___y_4388_ = v___y_4479_;
v___y_4389_ = v___y_4478_;
v___y_4390_ = v___y_4487_;
v___y_4391_ = v___y_4492_;
v___y_4392_ = v___y_4489_;
v___y_4393_ = v___y_4485_;
v___y_4394_ = v___y_4488_;
v___y_4395_ = v___y_4482_;
v___y_4396_ = v___y_4491_;
v___y_4397_ = v___y_4473_;
v___y_4398_ = v___x_4508_;
v___y_4399_ = v___y_4480_;
v___y_4400_ = v___x_4511_;
v___y_4401_ = v___y_4496_;
v___y_4402_ = v___y_4486_;
v___y_4403_ = v_ref_4501_;
v___y_4404_ = v___f_4507_;
v___y_4405_ = v___y_4490_;
v___y_4406_ = v___y_4497_;
v___y_4407_ = v___y_4476_;
v___y_4408_ = v___y_4495_;
v___y_4409_ = v___y_4477_;
v___y_4410_ = v___y_4493_;
v___y_4411_ = v___y_4484_;
v___y_4412_ = v___y_4481_;
v___y_4413_ = v___y_4494_;
v___y_4414_ = v___y_4483_;
goto v___jp_4384_;
}
}
}
v___jp_4515_:
{
lean_object* v_config_4543_; uint8_t v_graphviz_4544_; 
v_config_4543_ = lean_ctor_get(v___y_4517_, 5);
v_graphviz_4544_ = lean_ctor_get_uint8(v_config_4543_, sizeof(void*)*3 + 8);
if (v_graphviz_4544_ == 0)
{
lean_dec_ref(v___y_4524_);
v___y_4472_ = v___y_4516_;
v___y_4473_ = v___y_4517_;
v___y_4474_ = v___y_4518_;
v___y_4475_ = v___y_4519_;
v___y_4476_ = v___y_4520_;
v___y_4477_ = v___y_4523_;
v___y_4478_ = v___y_4522_;
v___y_4479_ = v___y_4521_;
v___y_4480_ = v___y_4525_;
v___y_4481_ = v___y_4526_;
v___y_4482_ = v___y_4527_;
v___y_4483_ = v___y_4528_;
v___y_4484_ = v___y_4529_;
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
v___y_4488_ = v___y_4533_;
v___y_4489_ = v___y_4534_;
v___y_4490_ = v___y_4535_;
v___y_4491_ = v___y_4536_;
v___y_4492_ = v___y_4537_;
v___y_4493_ = v___y_4538_;
v___y_4494_ = v___y_4539_;
v___y_4495_ = v___y_4540_;
v___y_4496_ = v___y_4541_;
v___y_4497_ = v___y_4542_;
goto v___jp_4471_;
}
else
{
lean_object* v_ref_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v_ref_4545_ = lean_ctor_get(v___y_4541_, 2);
v___x_4546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
v___x_4547_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v___y_4524_);
v___x_4548_ = l_IO_FS_writeFile(v___x_4546_, v___x_4547_);
lean_dec_ref(v___x_4547_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_dec_ref_known(v___x_4548_, 1);
v___y_4472_ = v___y_4516_;
v___y_4473_ = v___y_4517_;
v___y_4474_ = v___y_4518_;
v___y_4475_ = v___y_4519_;
v___y_4476_ = v___y_4520_;
v___y_4477_ = v___y_4523_;
v___y_4478_ = v___y_4522_;
v___y_4479_ = v___y_4521_;
v___y_4480_ = v___y_4525_;
v___y_4481_ = v___y_4526_;
v___y_4482_ = v___y_4527_;
v___y_4483_ = v___y_4528_;
v___y_4484_ = v___y_4529_;
v___y_4485_ = v___y_4530_;
v___y_4486_ = v___y_4531_;
v___y_4487_ = v___y_4532_;
v___y_4488_ = v___y_4533_;
v___y_4489_ = v___y_4534_;
v___y_4490_ = v___y_4535_;
v___y_4491_ = v___y_4536_;
v___y_4492_ = v___y_4537_;
v___y_4493_ = v___y_4538_;
v___y_4494_ = v___y_4539_;
v___y_4495_ = v___y_4540_;
v___y_4496_ = v___y_4541_;
v___y_4497_ = v___y_4542_;
goto v___jp_4471_;
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4560_; 
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec_ref(v___y_4516_);
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4551_ = v___x_4548_;
v_isShared_4552_ = v_isSharedCheck_4560_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4548_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4560_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4558_; 
v___x_4553_ = lean_io_error_to_string(v_a_4549_);
v___x_4554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
v___x_4555_ = l_Lean_MessageData_ofFormat(v___x_4554_);
lean_inc(v_ref_4545_);
v___x_4556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4556_, 0, v_ref_4545_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4556_);
v___x_4558_ = v___x_4551_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
v___jp_4561_:
{
if (lean_obj_tag(v___y_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v_result_4586_; lean_object* v_aig_4587_; lean_object* v_toCold_4588_; lean_object* v_options_4589_; lean_object* v_cache_4590_; lean_object* v_ref_4591_; lean_object* v_decls_4592_; lean_object* v_inheritedTraceOptions_4593_; uint8_t v_hasTrace_4594_; lean_object* v___x_4595_; 
v_a_4585_ = lean_ctor_get(v___y_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref_known(v___y_4584_, 1);
v_result_4586_ = lean_ctor_get(v_a_4585_, 0);
lean_inc_ref(v_result_4586_);
v_aig_4587_ = lean_ctor_get(v_result_4586_, 0);
lean_inc_ref(v_aig_4587_);
v_toCold_4588_ = lean_ctor_get(v___y_4575_, 0);
v_options_4589_ = lean_ctor_get(v_toCold_4588_, 2);
v_cache_4590_ = lean_ctor_get(v_a_4585_, 1);
lean_inc_ref(v_cache_4590_);
lean_dec(v_a_4585_);
v_ref_4591_ = lean_ctor_get(v_result_4586_, 1);
lean_inc_ref(v_ref_4591_);
v_decls_4592_ = lean_ctor_get(v_aig_4587_, 0);
v_inheritedTraceOptions_4593_ = lean_ctor_get(v_toCold_4588_, 11);
v_hasTrace_4594_ = lean_ctor_get_uint8(v_options_4589_, sizeof(void*)*1);
v___x_4595_ = lean_array_get_size(v_decls_4592_);
if (v_hasTrace_4594_ == 0)
{
lean_dec(v___y_4564_);
lean_inc_ref(v_result_4586_);
v___y_4516_ = v_result_4586_;
v___y_4517_ = v___y_4562_;
v___y_4518_ = v___y_4572_;
v___y_4519_ = v___y_4563_;
v___y_4520_ = v_ref_4591_;
v___y_4521_ = v_aig_4587_;
v___y_4522_ = v___y_4565_;
v___y_4523_ = v___y_4574_;
v___y_4524_ = v_result_4586_;
v___y_4525_ = v___y_4567_;
v___y_4526_ = v___x_4595_;
v___y_4527_ = v_cache_4590_;
v___y_4528_ = v___y_4582_;
v___y_4529_ = v___y_4576_;
v___y_4530_ = v___y_4569_;
v___y_4531_ = v___y_4578_;
v___y_4532_ = v___y_4579_;
v___y_4533_ = v___y_4577_;
v___y_4534_ = v___y_4568_;
v___y_4535_ = v___y_4581_;
v___y_4536_ = v___y_4580_;
v___y_4537_ = v___y_4570_;
v___y_4538_ = v___y_4571_;
v___y_4539_ = v___y_4573_;
v___y_4540_ = v___y_4583_;
v___y_4541_ = v___y_4575_;
v___y_4542_ = v___y_4566_;
goto v___jp_4515_;
}
else
{
lean_object* v___x_4596_; uint8_t v___x_4597_; 
v___x_4596_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4593_, v_options_4589_, v___x_4596_);
if (v___x_4597_ == 0)
{
lean_dec(v___y_4564_);
lean_inc_ref(v_result_4586_);
v___y_4516_ = v_result_4586_;
v___y_4517_ = v___y_4562_;
v___y_4518_ = v___y_4572_;
v___y_4519_ = v___y_4563_;
v___y_4520_ = v_ref_4591_;
v___y_4521_ = v_aig_4587_;
v___y_4522_ = v___y_4565_;
v___y_4523_ = v___y_4574_;
v___y_4524_ = v_result_4586_;
v___y_4525_ = v___y_4567_;
v___y_4526_ = v___x_4595_;
v___y_4527_ = v_cache_4590_;
v___y_4528_ = v___y_4582_;
v___y_4529_ = v___y_4576_;
v___y_4530_ = v___y_4569_;
v___y_4531_ = v___y_4578_;
v___y_4532_ = v___y_4579_;
v___y_4533_ = v___y_4577_;
v___y_4534_ = v___y_4568_;
v___y_4535_ = v___y_4581_;
v___y_4536_ = v___y_4580_;
v___y_4537_ = v___y_4570_;
v___y_4538_ = v___y_4571_;
v___y_4539_ = v___y_4573_;
v___y_4540_ = v___y_4583_;
v___y_4541_ = v___y_4575_;
v___y_4542_ = v___y_4566_;
goto v___jp_4515_;
}
else
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4598_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_4599_ = l_Nat_reprFast(v___x_4595_);
v___x_4600_ = lean_string_append(v___x_4598_, v___x_4599_);
lean_dec_ref(v___x_4599_);
v___x_4601_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_4602_ = lean_string_append(v___x_4600_, v___x_4601_);
v___x_4603_ = lean_nat_sub(v___x_4595_, v___y_4564_);
lean_dec(v___y_4564_);
v___x_4604_ = l_Nat_reprFast(v___x_4603_);
v___x_4605_ = lean_string_append(v___x_4602_, v___x_4604_);
lean_dec_ref(v___x_4604_);
v___x_4606_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_4607_ = lean_string_append(v___x_4605_, v___x_4606_);
v___x_4608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
v___x_4609_ = l_Lean_MessageData_ofFormat(v___x_4608_);
v___x_4610_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4233_, v___x_4609_, v___y_4573_, v___y_4583_, v___y_4575_, v___y_4566_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_dec_ref_known(v___x_4610_, 1);
lean_inc_ref(v_result_4586_);
v___y_4516_ = v_result_4586_;
v___y_4517_ = v___y_4562_;
v___y_4518_ = v___y_4572_;
v___y_4519_ = v___y_4563_;
v___y_4520_ = v_ref_4591_;
v___y_4521_ = v_aig_4587_;
v___y_4522_ = v___y_4565_;
v___y_4523_ = v___y_4574_;
v___y_4524_ = v_result_4586_;
v___y_4525_ = v___y_4567_;
v___y_4526_ = v___x_4595_;
v___y_4527_ = v_cache_4590_;
v___y_4528_ = v___y_4582_;
v___y_4529_ = v___y_4576_;
v___y_4530_ = v___y_4569_;
v___y_4531_ = v___y_4578_;
v___y_4532_ = v___y_4579_;
v___y_4533_ = v___y_4577_;
v___y_4534_ = v___y_4568_;
v___y_4535_ = v___y_4581_;
v___y_4536_ = v___y_4580_;
v___y_4537_ = v___y_4570_;
v___y_4538_ = v___y_4571_;
v___y_4539_ = v___y_4573_;
v___y_4540_ = v___y_4583_;
v___y_4541_ = v___y_4575_;
v___y_4542_ = v___y_4566_;
goto v___jp_4515_;
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4618_; 
lean_dec_ref(v_ref_4591_);
lean_dec_ref(v_cache_4590_);
lean_dec_ref(v_aig_4587_);
lean_dec_ref(v_result_4586_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4565_);
lean_dec(v___y_4563_);
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4618_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
}
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec(v___y_4563_);
v_a_4619_ = lean_ctor_get(v___y_4584_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___y_4584_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___y_4584_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___y_4584_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
v___jp_4627_:
{
lean_object* v___x_4655_; double v___x_4656_; double v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4655_ = lean_io_get_num_heartbeats();
v___x_4656_ = lean_float_of_nat(v___y_4642_);
v___x_4657_ = lean_float_of_nat(v___x_4655_);
v___x_4658_ = lean_box_float(v___x_4656_);
v___x_4659_ = lean_box_float(v___x_4657_);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4658_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
v___x_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4661_, 0, v_a_4654_);
lean_ctor_set(v___x_4661_, 1, v___x_4660_);
lean_inc_ref(v___y_4644_);
v___x_4662_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4233_, v___y_4638_, v___y_4644_, v___y_4652_, v___y_4634_, v___y_4648_, v___f_4229_, v___x_4661_, v___y_4636_, v___y_4640_, v___y_4647_, v___y_4646_, v___y_4635_, v___y_4639_, v___y_4649_, v___y_4650_, v___y_4632_, v___y_4641_, v___y_4643_, v___y_4653_, v___y_4645_, v___y_4631_);
v___y_4562_ = v___y_4637_;
v___y_4563_ = v___y_4628_;
v___y_4564_ = v___y_4629_;
v___y_4565_ = v___y_4630_;
v___y_4566_ = v___y_4631_;
v___y_4567_ = v___y_4638_;
v___y_4568_ = v___y_4639_;
v___y_4569_ = v___y_4640_;
v___y_4570_ = v___y_4632_;
v___y_4571_ = v___y_4641_;
v___y_4572_ = v___y_4633_;
v___y_4573_ = v___y_4643_;
v___y_4574_ = v___y_4644_;
v___y_4575_ = v___y_4645_;
v___y_4576_ = v___y_4636_;
v___y_4577_ = v___y_4635_;
v___y_4578_ = v___y_4647_;
v___y_4579_ = v___y_4646_;
v___y_4580_ = v___y_4650_;
v___y_4581_ = v___y_4649_;
v___y_4582_ = v___y_4651_;
v___y_4583_ = v___y_4653_;
v___y_4584_ = v___x_4662_;
goto v___jp_4561_;
}
v___jp_4663_:
{
lean_object* v___x_4691_; double v___x_4692_; double v___x_4693_; double v___x_4694_; double v___x_4695_; double v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4691_ = lean_io_mono_nanos_now();
v___x_4692_ = lean_float_of_nat(v___y_4678_);
v___x_4693_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4694_ = lean_float_div(v___x_4692_, v___x_4693_);
v___x_4695_ = lean_float_of_nat(v___x_4691_);
v___x_4696_ = lean_float_div(v___x_4695_, v___x_4693_);
v___x_4697_ = lean_box_float(v___x_4694_);
v___x_4698_ = lean_box_float(v___x_4696_);
v___x_4699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4697_);
lean_ctor_set(v___x_4699_, 1, v___x_4698_);
v___x_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4700_, 0, v_a_4690_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
lean_inc_ref(v___y_4680_);
v___x_4701_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4233_, v___y_4674_, v___y_4680_, v___y_4688_, v___y_4670_, v___y_4684_, v___f_4229_, v___x_4700_, v___y_4672_, v___y_4676_, v___y_4683_, v___y_4682_, v___y_4671_, v___y_4675_, v___y_4685_, v___y_4686_, v___y_4668_, v___y_4677_, v___y_4679_, v___y_4689_, v___y_4681_, v___y_4667_);
v___y_4562_ = v___y_4673_;
v___y_4563_ = v___y_4664_;
v___y_4564_ = v___y_4665_;
v___y_4565_ = v___y_4666_;
v___y_4566_ = v___y_4667_;
v___y_4567_ = v___y_4674_;
v___y_4568_ = v___y_4675_;
v___y_4569_ = v___y_4676_;
v___y_4570_ = v___y_4668_;
v___y_4571_ = v___y_4677_;
v___y_4572_ = v___y_4669_;
v___y_4573_ = v___y_4679_;
v___y_4574_ = v___y_4680_;
v___y_4575_ = v___y_4681_;
v___y_4576_ = v___y_4672_;
v___y_4577_ = v___y_4671_;
v___y_4578_ = v___y_4683_;
v___y_4579_ = v___y_4682_;
v___y_4580_ = v___y_4686_;
v___y_4581_ = v___y_4685_;
v___y_4582_ = v___y_4687_;
v___y_4583_ = v___y_4689_;
v___y_4584_ = v___x_4701_;
goto v___jp_4561_;
}
v___jp_4702_:
{
lean_object* v___x_4729_; lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4784_; 
v___x_4729_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4706_);
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4732_ = v___x_4729_;
v_isShared_4733_ = v_isSharedCheck_4784_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4784_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4734_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4735_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4728_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_io_mono_nanos_now();
v___x_4737_ = l_IO_lazyPure___redArg(v___y_4707_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_del_object(v___x_4732_);
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4737_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4737_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
lean_ctor_set_tag(v___x_4740_, 1);
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
v___y_4664_ = v___y_4703_;
v___y_4665_ = v___y_4704_;
v___y_4666_ = v___y_4705_;
v___y_4667_ = v___y_4706_;
v___y_4668_ = v___y_4708_;
v___y_4669_ = v___y_4709_;
v___y_4670_ = v___y_4710_;
v___y_4671_ = v___y_4711_;
v___y_4672_ = v___y_4712_;
v___y_4673_ = v___y_4713_;
v___y_4674_ = v___y_4714_;
v___y_4675_ = v___y_4716_;
v___y_4676_ = v___y_4717_;
v___y_4677_ = v___y_4718_;
v___y_4678_ = v___x_4736_;
v___y_4679_ = v___y_4719_;
v___y_4680_ = v___y_4720_;
v___y_4681_ = v___y_4721_;
v___y_4682_ = v___y_4722_;
v___y_4683_ = v___y_4723_;
v___y_4684_ = v_a_4730_;
v___y_4685_ = v___y_4725_;
v___y_4686_ = v___y_4724_;
v___y_4687_ = v___y_4726_;
v___y_4688_ = v___y_4728_;
v___y_4689_ = v___y_4727_;
v_a_4690_ = v___x_4743_;
goto v___jp_4663_;
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4759_; 
v_a_4746_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4748_ = v___x_4737_;
v_isShared_4749_ = v_isSharedCheck_4759_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4737_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4759_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4750_; lean_object* v___x_4752_; 
v___x_4750_ = lean_io_error_to_string(v_a_4746_);
if (v_isShared_4749_ == 0)
{
lean_ctor_set_tag(v___x_4748_, 3);
lean_ctor_set(v___x_4748_, 0, v___x_4750_);
v___x_4752_ = v___x_4748_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4750_);
v___x_4752_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4756_; 
v___x_4753_ = l_Lean_MessageData_ofFormat(v___x_4752_);
lean_inc(v___y_4715_);
v___x_4754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4754_, 0, v___y_4715_);
lean_ctor_set(v___x_4754_, 1, v___x_4753_);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v___x_4754_);
v___x_4756_ = v___x_4732_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4754_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
v___y_4664_ = v___y_4703_;
v___y_4665_ = v___y_4704_;
v___y_4666_ = v___y_4705_;
v___y_4667_ = v___y_4706_;
v___y_4668_ = v___y_4708_;
v___y_4669_ = v___y_4709_;
v___y_4670_ = v___y_4710_;
v___y_4671_ = v___y_4711_;
v___y_4672_ = v___y_4712_;
v___y_4673_ = v___y_4713_;
v___y_4674_ = v___y_4714_;
v___y_4675_ = v___y_4716_;
v___y_4676_ = v___y_4717_;
v___y_4677_ = v___y_4718_;
v___y_4678_ = v___x_4736_;
v___y_4679_ = v___y_4719_;
v___y_4680_ = v___y_4720_;
v___y_4681_ = v___y_4721_;
v___y_4682_ = v___y_4722_;
v___y_4683_ = v___y_4723_;
v___y_4684_ = v_a_4730_;
v___y_4685_ = v___y_4725_;
v___y_4686_ = v___y_4724_;
v___y_4687_ = v___y_4726_;
v___y_4688_ = v___y_4728_;
v___y_4689_ = v___y_4727_;
v_a_4690_ = v___x_4756_;
goto v___jp_4663_;
}
}
}
}
}
else
{
lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4760_ = lean_io_get_num_heartbeats();
v___x_4761_ = l_IO_lazyPure___redArg(v___y_4707_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_del_object(v___x_4732_);
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4761_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4761_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
lean_ctor_set_tag(v___x_4764_, 1);
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
v___y_4628_ = v___y_4703_;
v___y_4629_ = v___y_4704_;
v___y_4630_ = v___y_4705_;
v___y_4631_ = v___y_4706_;
v___y_4632_ = v___y_4708_;
v___y_4633_ = v___y_4709_;
v___y_4634_ = v___y_4710_;
v___y_4635_ = v___y_4711_;
v___y_4636_ = v___y_4712_;
v___y_4637_ = v___y_4713_;
v___y_4638_ = v___y_4714_;
v___y_4639_ = v___y_4716_;
v___y_4640_ = v___y_4717_;
v___y_4641_ = v___y_4718_;
v___y_4642_ = v___x_4760_;
v___y_4643_ = v___y_4719_;
v___y_4644_ = v___y_4720_;
v___y_4645_ = v___y_4721_;
v___y_4646_ = v___y_4722_;
v___y_4647_ = v___y_4723_;
v___y_4648_ = v_a_4730_;
v___y_4649_ = v___y_4725_;
v___y_4650_ = v___y_4724_;
v___y_4651_ = v___y_4726_;
v___y_4652_ = v___y_4728_;
v___y_4653_ = v___y_4727_;
v_a_4654_ = v___x_4767_;
goto v___jp_4627_;
}
}
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4783_; 
v_a_4770_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4772_ = v___x_4761_;
v_isShared_4773_ = v_isSharedCheck_4783_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4761_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4783_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4774_; lean_object* v___x_4776_; 
v___x_4774_ = lean_io_error_to_string(v_a_4770_);
if (v_isShared_4773_ == 0)
{
lean_ctor_set_tag(v___x_4772_, 3);
lean_ctor_set(v___x_4772_, 0, v___x_4774_);
v___x_4776_ = v___x_4772_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v___x_4774_);
v___x_4776_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4780_; 
v___x_4777_ = l_Lean_MessageData_ofFormat(v___x_4776_);
lean_inc(v___y_4715_);
v___x_4778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___y_4715_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v___x_4778_);
v___x_4780_ = v___x_4732_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
v___y_4628_ = v___y_4703_;
v___y_4629_ = v___y_4704_;
v___y_4630_ = v___y_4705_;
v___y_4631_ = v___y_4706_;
v___y_4632_ = v___y_4708_;
v___y_4633_ = v___y_4709_;
v___y_4634_ = v___y_4710_;
v___y_4635_ = v___y_4711_;
v___y_4636_ = v___y_4712_;
v___y_4637_ = v___y_4713_;
v___y_4638_ = v___y_4714_;
v___y_4639_ = v___y_4716_;
v___y_4640_ = v___y_4717_;
v___y_4641_ = v___y_4718_;
v___y_4642_ = v___x_4760_;
v___y_4643_ = v___y_4719_;
v___y_4644_ = v___y_4720_;
v___y_4645_ = v___y_4721_;
v___y_4646_ = v___y_4722_;
v___y_4647_ = v___y_4723_;
v___y_4648_ = v_a_4730_;
v___y_4649_ = v___y_4725_;
v___y_4650_ = v___y_4724_;
v___y_4651_ = v___y_4726_;
v___y_4652_ = v___y_4728_;
v___y_4653_ = v___y_4727_;
v_a_4654_ = v___x_4780_;
goto v___jp_4627_;
}
}
}
}
}
}
}
v___jp_4785_:
{
lean_object* v___x_4801_; lean_object* v_satExpr_4802_; lean_object* v_bvExpr_4803_; lean_object* v___x_4804_; lean_object* v_theoryState_4805_; lean_object* v_bitvecState_4806_; lean_object* v___x_4807_; lean_object* v_theoryState_4808_; lean_object* v_satExpr_4809_; lean_object* v_hypQueue_4810_; lean_object* v_usedHyps_4811_; uint8_t v_didChange_4812_; lean_object* v_solverTimeBudgetMs_4813_; lean_object* v_roundBudget_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4855_; 
v___x_4801_ = lean_st_ref_get(v___y_4788_);
v_satExpr_4802_ = lean_ctor_get(v___x_4801_, 0);
lean_inc_ref(v_satExpr_4802_);
lean_dec(v___x_4801_);
v_bvExpr_4803_ = lean_ctor_get(v_satExpr_4802_, 0);
lean_inc_ref(v_bvExpr_4803_);
lean_dec_ref(v_satExpr_4802_);
v___x_4804_ = lean_st_ref_get(v___y_4788_);
v_theoryState_4805_ = lean_ctor_get(v___x_4804_, 3);
lean_inc_ref(v_theoryState_4805_);
lean_dec(v___x_4804_);
v_bitvecState_4806_ = lean_ctor_get(v_theoryState_4805_, 1);
lean_inc_ref(v_bitvecState_4806_);
lean_dec_ref(v_theoryState_4805_);
v___x_4807_ = lean_st_ref_take(v___y_4788_);
v_theoryState_4808_ = lean_ctor_get(v___x_4807_, 3);
v_satExpr_4809_ = lean_ctor_get(v___x_4807_, 0);
v_hypQueue_4810_ = lean_ctor_get(v___x_4807_, 1);
v_usedHyps_4811_ = lean_ctor_get(v___x_4807_, 2);
v_didChange_4812_ = lean_ctor_get_uint8(v___x_4807_, sizeof(void*)*6);
v_solverTimeBudgetMs_4813_ = lean_ctor_get(v___x_4807_, 4);
v_roundBudget_4814_ = lean_ctor_get(v___x_4807_, 5);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4816_ = v___x_4807_;
v_isShared_4817_ = v_isSharedCheck_4855_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_roundBudget_4814_);
lean_inc(v_solverTimeBudgetMs_4813_);
lean_inc(v_theoryState_4808_);
lean_inc(v_usedHyps_4811_);
lean_inc(v_hypQueue_4810_);
lean_inc(v_satExpr_4809_);
lean_dec(v___x_4807_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4855_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v_funState_4818_; lean_object* v_preprocessCaches_4819_; lean_object* v_satSolver_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4853_; 
v_funState_4818_ = lean_ctor_get(v_theoryState_4808_, 0);
v_preprocessCaches_4819_ = lean_ctor_get(v_theoryState_4808_, 2);
v_satSolver_4820_ = lean_ctor_get(v_theoryState_4808_, 3);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_theoryState_4808_);
if (v_isSharedCheck_4853_ == 0)
{
lean_object* v_unused_4854_; 
v_unused_4854_ = lean_ctor_get(v_theoryState_4808_, 1);
lean_dec(v_unused_4854_);
v___x_4822_ = v_theoryState_4808_;
v_isShared_4823_ = v_isSharedCheck_4853_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_satSolver_4820_);
lean_inc(v_preprocessCaches_4819_);
lean_inc(v_funState_4818_);
lean_dec(v_theoryState_4808_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4853_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4824_ = lean_unsigned_to_nat(0u);
v___x_4825_ = lean_unsigned_to_nat(16u);
v___x_4826_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 1, v___x_4826_);
v___x_4828_ = v___x_4822_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_funState_4818_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_4852_, 2, v_preprocessCaches_4819_);
lean_ctor_set(v_reuseFailAlloc_4852_, 3, v_satSolver_4820_);
v___x_4828_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4830_; 
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 3, v___x_4828_);
v___x_4830_ = v___x_4816_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_satExpr_4809_);
lean_ctor_set(v_reuseFailAlloc_4851_, 1, v_hypQueue_4810_);
lean_ctor_set(v_reuseFailAlloc_4851_, 2, v_usedHyps_4811_);
lean_ctor_set(v_reuseFailAlloc_4851_, 3, v___x_4828_);
lean_ctor_set(v_reuseFailAlloc_4851_, 4, v_solverTimeBudgetMs_4813_);
lean_ctor_set(v_reuseFailAlloc_4851_, 5, v_roundBudget_4814_);
lean_ctor_set_uint8(v_reuseFailAlloc_4851_, sizeof(void*)*6, v_didChange_4812_);
v___x_4830_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4831_; lean_object* v_aig_4832_; lean_object* v_toCold_4833_; lean_object* v_options_4834_; lean_object* v_blastCache_4835_; lean_object* v_cnfCache_4836_; lean_object* v_decls_4837_; lean_object* v_ref_4838_; lean_object* v_inheritedTraceOptions_4839_; uint8_t v_hasTrace_4840_; lean_object* v___f_4841_; lean_object* v___x_4842_; uint8_t v___x_4843_; lean_object* v___x_4844_; 
v___x_4831_ = lean_st_ref_put(v___y_4788_, v___x_4830_);
v_aig_4832_ = lean_ctor_get(v_bitvecState_4806_, 0);
lean_inc_ref(v_aig_4832_);
v_toCold_4833_ = lean_ctor_get(v___y_4799_, 0);
v_options_4834_ = lean_ctor_get(v_toCold_4833_, 2);
v_blastCache_4835_ = lean_ctor_get(v_bitvecState_4806_, 1);
lean_inc_ref(v_blastCache_4835_);
v_cnfCache_4836_ = lean_ctor_get(v_bitvecState_4806_, 2);
lean_inc_ref(v_cnfCache_4836_);
lean_dec_ref(v_bitvecState_4806_);
v_decls_4837_ = lean_ctor_get(v_aig_4832_, 0);
lean_inc_ref(v_decls_4837_);
v_ref_4838_ = lean_ctor_get(v___y_4799_, 2);
v_inheritedTraceOptions_4839_ = lean_ctor_get(v_toCold_4833_, 11);
v_hasTrace_4840_ = lean_ctor_get_uint8(v_options_4834_, sizeof(void*)*1);
v___f_4841_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_4841_, 0, v_aig_4832_);
lean_closure_set(v___f_4841_, 1, v_bvExpr_4803_);
lean_closure_set(v___f_4841_, 2, v_blastCache_4835_);
v___x_4842_ = lean_array_get_size(v_decls_4837_);
lean_dec_ref(v_decls_4837_);
v___x_4843_ = 1;
v___x_4844_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
if (v_hasTrace_4840_ == 0)
{
lean_object* v___x_4845_; 
v___x_4845_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_4841_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
v___y_4562_ = v_ctx_4786_;
v___y_4563_ = v___x_4825_;
v___y_4564_ = v___x_4842_;
v___y_4565_ = v___x_4824_;
v___y_4566_ = v___y_4800_;
v___y_4567_ = v___x_4843_;
v___y_4568_ = v___y_4792_;
v___y_4569_ = v___y_4788_;
v___y_4570_ = v___y_4795_;
v___y_4571_ = v___y_4796_;
v___y_4572_ = v_cnfCache_4836_;
v___y_4573_ = v___y_4797_;
v___y_4574_ = v___x_4844_;
v___y_4575_ = v___y_4799_;
v___y_4576_ = v___y_4787_;
v___y_4577_ = v___y_4791_;
v___y_4578_ = v___y_4789_;
v___y_4579_ = v___y_4790_;
v___y_4580_ = v___y_4794_;
v___y_4581_ = v___y_4793_;
v___y_4582_ = v___x_4826_;
v___y_4583_ = v___y_4798_;
v___y_4584_ = v___x_4845_;
goto v___jp_4561_;
}
else
{
lean_object* v___x_4846_; uint8_t v___x_4847_; 
v___x_4846_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4847_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4839_, v_options_4834_, v___x_4846_);
if (v___x_4847_ == 0)
{
lean_object* v___x_4848_; uint8_t v___x_4849_; 
v___x_4848_ = l_Lean_trace_profiler;
v___x_4849_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4834_, v___x_4848_);
if (v___x_4849_ == 0)
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_4841_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
v___y_4562_ = v_ctx_4786_;
v___y_4563_ = v___x_4825_;
v___y_4564_ = v___x_4842_;
v___y_4565_ = v___x_4824_;
v___y_4566_ = v___y_4800_;
v___y_4567_ = v___x_4843_;
v___y_4568_ = v___y_4792_;
v___y_4569_ = v___y_4788_;
v___y_4570_ = v___y_4795_;
v___y_4571_ = v___y_4796_;
v___y_4572_ = v_cnfCache_4836_;
v___y_4573_ = v___y_4797_;
v___y_4574_ = v___x_4844_;
v___y_4575_ = v___y_4799_;
v___y_4576_ = v___y_4787_;
v___y_4577_ = v___y_4791_;
v___y_4578_ = v___y_4789_;
v___y_4579_ = v___y_4790_;
v___y_4580_ = v___y_4794_;
v___y_4581_ = v___y_4793_;
v___y_4582_ = v___x_4826_;
v___y_4583_ = v___y_4798_;
v___y_4584_ = v___x_4850_;
goto v___jp_4561_;
}
else
{
v___y_4703_ = v___x_4825_;
v___y_4704_ = v___x_4842_;
v___y_4705_ = v___x_4824_;
v___y_4706_ = v___y_4800_;
v___y_4707_ = v___f_4841_;
v___y_4708_ = v___y_4795_;
v___y_4709_ = v_cnfCache_4836_;
v___y_4710_ = v___x_4847_;
v___y_4711_ = v___y_4791_;
v___y_4712_ = v___y_4787_;
v___y_4713_ = v_ctx_4786_;
v___y_4714_ = v___x_4843_;
v___y_4715_ = v_ref_4838_;
v___y_4716_ = v___y_4792_;
v___y_4717_ = v___y_4788_;
v___y_4718_ = v___y_4796_;
v___y_4719_ = v___y_4797_;
v___y_4720_ = v___x_4844_;
v___y_4721_ = v___y_4799_;
v___y_4722_ = v___y_4790_;
v___y_4723_ = v___y_4789_;
v___y_4724_ = v___y_4794_;
v___y_4725_ = v___y_4793_;
v___y_4726_ = v___x_4826_;
v___y_4727_ = v___y_4798_;
v___y_4728_ = v_options_4834_;
goto v___jp_4702_;
}
}
else
{
v___y_4703_ = v___x_4825_;
v___y_4704_ = v___x_4842_;
v___y_4705_ = v___x_4824_;
v___y_4706_ = v___y_4800_;
v___y_4707_ = v___f_4841_;
v___y_4708_ = v___y_4795_;
v___y_4709_ = v_cnfCache_4836_;
v___y_4710_ = v___x_4847_;
v___y_4711_ = v___y_4791_;
v___y_4712_ = v___y_4787_;
v___y_4713_ = v_ctx_4786_;
v___y_4714_ = v___x_4843_;
v___y_4715_ = v_ref_4838_;
v___y_4716_ = v___y_4792_;
v___y_4717_ = v___y_4788_;
v___y_4718_ = v___y_4796_;
v___y_4719_ = v___y_4797_;
v___y_4720_ = v___x_4844_;
v___y_4721_ = v___y_4799_;
v___y_4722_ = v___y_4790_;
v___y_4723_ = v___y_4789_;
v___y_4724_ = v___y_4794_;
v___y_4725_ = v___y_4793_;
v___y_4726_ = v___x_4826_;
v___y_4727_ = v___y_4798_;
v___y_4728_ = v_options_4834_;
goto v___jp_4702_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___boxed(lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
lean_dec(v_a_5409_);
lean_dec_ref(v_a_5408_);
lean_dec(v_a_5407_);
lean_dec_ref(v_a_5406_);
lean_dec(v_a_5405_);
lean_dec_ref(v_a_5404_);
lean_dec(v_a_5403_);
lean_dec_ref(v_a_5402_);
lean_dec(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec_ref(v_a_5399_);
lean_dec(v_a_5398_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2(lean_object* v_cls_5412_, lean_object* v_msg_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_){
_start:
{
lean_object* v___x_5429_; 
v___x_5429_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_5412_, v_msg_5413_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_);
return v___x_5429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___boxed(lean_object** _args){
lean_object* v_cls_5430_ = _args[0];
lean_object* v_msg_5431_ = _args[1];
lean_object* v___y_5432_ = _args[2];
lean_object* v___y_5433_ = _args[3];
lean_object* v___y_5434_ = _args[4];
lean_object* v___y_5435_ = _args[5];
lean_object* v___y_5436_ = _args[6];
lean_object* v___y_5437_ = _args[7];
lean_object* v___y_5438_ = _args[8];
lean_object* v___y_5439_ = _args[9];
lean_object* v___y_5440_ = _args[10];
lean_object* v___y_5441_ = _args[11];
lean_object* v___y_5442_ = _args[12];
lean_object* v___y_5443_ = _args[13];
lean_object* v___y_5444_ = _args[14];
lean_object* v___y_5445_ = _args[15];
lean_object* v___y_5446_ = _args[16];
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2(v_cls_5430_, v_msg_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec(v___y_5443_);
lean_dec_ref(v___y_5442_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
lean_dec(v___y_5439_);
lean_dec_ref(v___y_5438_);
lean_dec(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec(v___y_5434_);
lean_dec(v___y_5433_);
lean_dec_ref(v___y_5432_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3(lean_object* v_00_u03b1_5448_, lean_object* v_msg_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_){
_start:
{
lean_object* v___x_5465_; 
v___x_5465_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v_msg_5449_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_);
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03b1_5466_ = _args[0];
lean_object* v_msg_5467_ = _args[1];
lean_object* v___y_5468_ = _args[2];
lean_object* v___y_5469_ = _args[3];
lean_object* v___y_5470_ = _args[4];
lean_object* v___y_5471_ = _args[5];
lean_object* v___y_5472_ = _args[6];
lean_object* v___y_5473_ = _args[7];
lean_object* v___y_5474_ = _args[8];
lean_object* v___y_5475_ = _args[9];
lean_object* v___y_5476_ = _args[10];
lean_object* v___y_5477_ = _args[11];
lean_object* v___y_5478_ = _args[12];
lean_object* v___y_5479_ = _args[13];
lean_object* v___y_5480_ = _args[14];
lean_object* v___y_5481_ = _args[15];
lean_object* v___y_5482_ = _args[16];
_start:
{
lean_object* v_res_5483_; 
v_res_5483_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3(v_00_u03b1_5466_, v_msg_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec_ref(v___y_5471_);
lean_dec(v___y_5470_);
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
return v_res_5483_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9(lean_object* v_00_u03b1_5484_, lean_object* v_x_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_){
_start:
{
lean_object* v___x_5501_; 
v___x_5501_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_x_5485_);
return v___x_5501_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_00_u03b1_5502_ = _args[0];
lean_object* v_x_5503_ = _args[1];
lean_object* v___y_5504_ = _args[2];
lean_object* v___y_5505_ = _args[3];
lean_object* v___y_5506_ = _args[4];
lean_object* v___y_5507_ = _args[5];
lean_object* v___y_5508_ = _args[6];
lean_object* v___y_5509_ = _args[7];
lean_object* v___y_5510_ = _args[8];
lean_object* v___y_5511_ = _args[9];
lean_object* v___y_5512_ = _args[10];
lean_object* v___y_5513_ = _args[11];
lean_object* v___y_5514_ = _args[12];
lean_object* v___y_5515_ = _args[13];
lean_object* v___y_5516_ = _args[14];
lean_object* v___y_5517_ = _args[15];
lean_object* v___y_5518_ = _args[16];
_start:
{
lean_object* v_res_5519_; 
v_res_5519_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9(v_00_u03b1_5502_, v_x_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
lean_dec(v___y_5515_);
lean_dec_ref(v___y_5514_);
lean_dec(v___y_5513_);
lean_dec_ref(v___y_5512_);
lean_dec(v___y_5511_);
lean_dec_ref(v___y_5510_);
lean_dec(v___y_5509_);
lean_dec(v___y_5508_);
lean_dec_ref(v___y_5507_);
lean_dec(v___y_5506_);
lean_dec(v___y_5505_);
lean_dec_ref(v___y_5504_);
return v_res_5519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8(lean_object* v_oldTraces_5520_, lean_object* v_data_5521_, lean_object* v_ref_5522_, lean_object* v_msg_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_){
_start:
{
lean_object* v___x_5539_; 
v___x_5539_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_5520_, v_data_5521_, v_ref_5522_, v_msg_5523_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_);
return v___x_5539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_5540_ = _args[0];
lean_object* v_data_5541_ = _args[1];
lean_object* v_ref_5542_ = _args[2];
lean_object* v_msg_5543_ = _args[3];
lean_object* v___y_5544_ = _args[4];
lean_object* v___y_5545_ = _args[5];
lean_object* v___y_5546_ = _args[6];
lean_object* v___y_5547_ = _args[7];
lean_object* v___y_5548_ = _args[8];
lean_object* v___y_5549_ = _args[9];
lean_object* v___y_5550_ = _args[10];
lean_object* v___y_5551_ = _args[11];
lean_object* v___y_5552_ = _args[12];
lean_object* v___y_5553_ = _args[13];
lean_object* v___y_5554_ = _args[14];
lean_object* v___y_5555_ = _args[15];
lean_object* v___y_5556_ = _args[16];
lean_object* v___y_5557_ = _args[17];
lean_object* v___y_5558_ = _args[18];
_start:
{
lean_object* v_res_5559_; 
v_res_5559_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8(v_oldTraces_5540_, v_data_5541_, v_ref_5542_, v_msg_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5555_);
lean_dec_ref(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec_ref(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec_ref(v___y_5547_);
lean_dec(v___y_5546_);
lean_dec(v___y_5545_);
lean_dec_ref(v___y_5544_);
return v_res_5559_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16(lean_object* v_acc_5560_, lean_object* v_decls_5561_, lean_object* v_hinv_5562_, lean_object* v_idx_5563_, lean_object* v_hidx_5564_, lean_object* v_a_5565_){
_start:
{
lean_object* v___x_5566_; 
v___x_5566_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v_acc_5560_, v_decls_5561_, v_idx_5563_, v_a_5565_);
return v___x_5566_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___boxed(lean_object* v_acc_5567_, lean_object* v_decls_5568_, lean_object* v_hinv_5569_, lean_object* v_idx_5570_, lean_object* v_hidx_5571_, lean_object* v_a_5572_){
_start:
{
lean_object* v_res_5573_; 
v_res_5573_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16(v_acc_5567_, v_decls_5568_, v_hinv_5569_, v_idx_5570_, v_hidx_5571_, v_a_5572_);
lean_dec_ref(v_decls_5568_);
return v_res_5573_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18(lean_object* v___x_5574_, lean_object* v_00_u03b2_5575_, lean_object* v_m_5576_, lean_object* v_a_5577_){
_start:
{
uint8_t v___x_5578_; 
v___x_5578_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_5574_, v_m_5576_, v_a_5577_);
return v___x_5578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___boxed(lean_object* v___x_5579_, lean_object* v_00_u03b2_5580_, lean_object* v_m_5581_, lean_object* v_a_5582_){
_start:
{
uint8_t v_res_5583_; lean_object* v_r_5584_; 
v_res_5583_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18(v___x_5579_, v_00_u03b2_5580_, v_m_5581_, v_a_5582_);
lean_dec(v_a_5582_);
lean_dec_ref(v_m_5581_);
lean_dec(v___x_5579_);
v_r_5584_ = lean_box(v_res_5583_);
return v_r_5584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19(lean_object* v___x_5585_, lean_object* v_00_u03b2_5586_, lean_object* v_m_5587_, lean_object* v_a_5588_, lean_object* v_b_5589_){
_start:
{
lean_object* v___x_5590_; 
v___x_5590_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_5585_, v_m_5587_, v_a_5588_, v_b_5589_);
return v___x_5590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___boxed(lean_object* v___x_5591_, lean_object* v_00_u03b2_5592_, lean_object* v_m_5593_, lean_object* v_a_5594_, lean_object* v_b_5595_){
_start:
{
lean_object* v_res_5596_; 
v_res_5596_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19(v___x_5591_, v_00_u03b2_5592_, v_m_5593_, v_a_5594_, v_b_5595_);
lean_dec(v___x_5591_);
return v_res_5596_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23(lean_object* v___x_5597_, lean_object* v_00_u03b2_5598_, lean_object* v_a_5599_, lean_object* v_x_5600_){
_start:
{
uint8_t v___x_5601_; 
v___x_5601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_5599_, v_x_5600_);
return v___x_5601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___boxed(lean_object* v___x_5602_, lean_object* v_00_u03b2_5603_, lean_object* v_a_5604_, lean_object* v_x_5605_){
_start:
{
uint8_t v_res_5606_; lean_object* v_r_5607_; 
v_res_5606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23(v___x_5602_, v_00_u03b2_5603_, v_a_5604_, v_x_5605_);
lean_dec(v_x_5605_);
lean_dec(v_a_5604_);
lean_dec(v___x_5602_);
v_r_5607_ = lean_box(v_res_5606_);
return v_r_5607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25(lean_object* v___x_5608_, lean_object* v_00_u03b2_5609_, lean_object* v_data_5610_){
_start:
{
lean_object* v___x_5611_; 
v___x_5611_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_5608_, v_data_5610_);
return v___x_5611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___boxed(lean_object* v___x_5612_, lean_object* v_00_u03b2_5613_, lean_object* v_data_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25(v___x_5612_, v_00_u03b2_5613_, v_data_5614_);
lean_dec(v___x_5612_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28(lean_object* v___x_5616_, lean_object* v_00_u03b2_5617_, lean_object* v_i_5618_, lean_object* v_source_5619_, lean_object* v_target_5620_){
_start:
{
lean_object* v___x_5621_; 
v___x_5621_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(v_i_5618_, v_source_5619_, v_target_5620_);
return v___x_5621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___boxed(lean_object* v___x_5622_, lean_object* v_00_u03b2_5623_, lean_object* v_i_5624_, lean_object* v_source_5625_, lean_object* v_target_5626_){
_start:
{
lean_object* v_res_5627_; 
v_res_5627_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28(v___x_5622_, v_00_u03b2_5623_, v_i_5624_, v_source_5625_, v_target_5626_);
lean_dec(v___x_5622_);
return v_res_5627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29(lean_object* v_00_u03b2_5628_, lean_object* v_x_5629_, lean_object* v_x_5630_){
_start:
{
lean_object* v___x_5631_; 
v___x_5631_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(v_x_5629_, v_x_5630_);
return v___x_5631_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0 = _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_External(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec(builtin);
}
#ifdef __cplusplus
}
#endif
