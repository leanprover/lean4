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
lean_object* l_IO_TaskState_ctorIdx(uint8_t);
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
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___closed__0;
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
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___closed__0(void){
_start:
{
uint8_t v___x_592_; lean_object* v___x_593_; 
v___x_592_ = 2;
v___x_593_ = l_IO_TaskState_ctorIdx(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(lean_object* v_val_594_, lean_object* v_solver_595_, lean_object* v_a_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___y_613_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_633_ = lean_unsigned_to_nat(64u);
v___x_634_ = lean_io_get_task_state(v_val_594_);
v___x_635_ = l_IO_TaskState_ctorIdx(v___x_634_);
v___x_636_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___closed__0);
v___x_637_ = lean_nat_dec_eq(v___x_635_, v___x_636_);
lean_dec(v___x_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v_solverTimeBudgetMs_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_638_ = lean_st_ref_get(v___y_598_);
v_solverTimeBudgetMs_639_ = lean_ctor_get(v___x_638_, 4);
lean_inc(v_solverTimeBudgetMs_639_);
lean_dec(v___x_638_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_nat_dec_eq(v_solverTimeBudgetMs_639_, v___x_640_);
lean_dec(v_solverTimeBudgetMs_639_);
if (v___x_641_ == 0)
{
lean_object* v_toCold_642_; lean_object* v_cancelTk_x3f_643_; 
v_toCold_642_ = lean_ctor_get(v___y_609_, 0);
v_cancelTk_x3f_643_ = lean_ctor_get(v_toCold_642_, 10);
if (lean_obj_tag(v_cancelTk_x3f_643_) == 1)
{
lean_object* v_val_644_; uint8_t v___x_645_; 
v_val_644_ = lean_ctor_get(v_cancelTk_x3f_643_, 0);
v___x_645_ = l_IO_CancelToken_isSet(v_val_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_596_, v___x_633_, v___x_646_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
v___y_613_ = v___x_647_;
goto v___jp_612_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = l_Lean_Cadical_Solver_terminate(v_solver_595_);
v___x_649_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_596_, v___x_633_, v_a_650_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
v___y_613_ = v___x_651_;
goto v___jp_612_;
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_596_);
v_a_652_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_649_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_649_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_596_, v___x_633_, v___x_660_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
v___y_613_ = v___x_661_;
goto v___jp_612_;
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = l_Lean_Cadical_Solver_terminate(v_solver_595_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v_a_596_);
return v___x_663_;
}
}
else
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v_a_596_);
return v___x_664_;
}
v___jp_612_:
{
if (lean_obj_tag(v___y_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_624_; 
v_a_614_ = lean_ctor_get(v___y_613_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___y_613_);
if (v_isSharedCheck_624_ == 0)
{
v___x_616_ = v___y_613_;
v_isShared_617_ = v_isSharedCheck_624_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___y_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_624_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
if (lean_obj_tag(v_a_614_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; 
v_a_618_ = lean_ctor_get(v_a_614_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v_a_614_, 1);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v_a_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_618_);
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
lean_object* v_a_622_; 
lean_del_object(v___x_616_);
v_a_622_ = lean_ctor_get(v_a_614_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v_a_614_, 1);
v_a_596_ = v_a_622_;
goto _start;
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_a_625_ = lean_ctor_get(v___y_613_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___y_613_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___y_613_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___y_613_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_val_665_ = _args[0];
lean_object* v_solver_666_ = _args[1];
lean_object* v_a_667_ = _args[2];
lean_object* v___y_668_ = _args[3];
lean_object* v___y_669_ = _args[4];
lean_object* v___y_670_ = _args[5];
lean_object* v___y_671_ = _args[6];
lean_object* v___y_672_ = _args[7];
lean_object* v___y_673_ = _args[8];
lean_object* v___y_674_ = _args[9];
lean_object* v___y_675_ = _args[10];
lean_object* v___y_676_ = _args[11];
lean_object* v___y_677_ = _args[12];
lean_object* v___y_678_ = _args[13];
lean_object* v___y_679_ = _args[14];
lean_object* v___y_680_ = _args[15];
lean_object* v___y_681_ = _args[16];
lean_object* v___y_682_ = _args[17];
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v_val_665_, v_solver_666_, v_a_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec_ref(v_solver_666_);
lean_dec_ref(v_val_665_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(lean_object* v_solver_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_inc_ref(v_solver_684_);
v___x_700_ = lean_alloc_closure((void*)(l_Lean_Cadical_Solver_solve___boxed), 2, 1);
lean_closure_set(v___x_700_, 0, v_solver_684_);
v___x_701_ = lean_unsigned_to_nat(9u);
v___x_702_ = lean_io_as_task(v___x_700_, v___x_701_);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v___x_702_, v_solver_684_, v___x_703_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec_ref(v_solver_684_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_704_, 0);
lean_dec(v_unused_713_);
v___x_706_ = v___x_704_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_dec(v___x_704_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = lean_task_get_own(v___x_702_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v___x_702_);
v_a_714_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_704_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_704_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver___boxed(lean_object* v_solver_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v_solver_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1(lean_object* v_val_739_, lean_object* v_solver_740_, lean_object* v_inst_741_, lean_object* v_a_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v_val_739_, v_solver_740_, v_a_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___boxed(lean_object** _args){
lean_object* v_val_759_ = _args[0];
lean_object* v_solver_760_ = _args[1];
lean_object* v_inst_761_ = _args[2];
lean_object* v_a_762_ = _args[3];
lean_object* v___y_763_ = _args[4];
lean_object* v___y_764_ = _args[5];
lean_object* v___y_765_ = _args[6];
lean_object* v___y_766_ = _args[7];
lean_object* v___y_767_ = _args[8];
lean_object* v___y_768_ = _args[9];
lean_object* v___y_769_ = _args[10];
lean_object* v___y_770_ = _args[11];
lean_object* v___y_771_ = _args[12];
lean_object* v___y_772_ = _args[13];
lean_object* v___y_773_ = _args[14];
lean_object* v___y_774_ = _args[15];
lean_object* v___y_775_ = _args[16];
lean_object* v___y_776_ = _args[17];
lean_object* v___y_777_ = _args[18];
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1(v_val_759_, v_solver_760_, v_inst_761_, v_a_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_solver_760_);
lean_dec_ref(v_val_759_);
return v_res_778_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_box(0);
v___x_784_ = lean_unsigned_to_nat(16u);
v___x_785_ = lean_mk_array(v___x_784_, v___x_783_);
return v___x_785_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
return v___x_788_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2);
v___x_790_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__0));
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
return v___x_791_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0(void){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3);
return v___x_792_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_793_ = lean_unsigned_to_nat(32u);
v___x_794_ = lean_mk_empty_array_with_capacity(v___x_793_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_796_ = ((size_t)5ULL);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_unsigned_to_nat(32u);
v___x_799_ = lean_mk_empty_array_with_capacity(v___x_798_);
v___x_800_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0);
v___x_801_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___x_799_);
lean_ctor_set(v___x_801_, 2, v___x_797_);
lean_ctor_set(v___x_801_, 3, v___x_797_);
lean_ctor_set_usize(v___x_801_, 4, v___x_796_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v_traceState_805_; lean_object* v_traces_806_; lean_object* v___x_807_; lean_object* v_traceState_808_; lean_object* v_env_809_; lean_object* v_nextMacroScope_810_; lean_object* v_ngen_811_; lean_object* v_auxDeclNGen_812_; lean_object* v_cache_813_; lean_object* v_recordedDeps_814_; lean_object* v_messages_815_; lean_object* v_infoState_816_; lean_object* v_snapshotTasks_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_836_; 
v___x_804_ = lean_st_ref_get(v___y_802_);
v_traceState_805_ = lean_ctor_get(v___x_804_, 4);
lean_inc_ref(v_traceState_805_);
lean_dec(v___x_804_);
v_traces_806_ = lean_ctor_get(v_traceState_805_, 0);
lean_inc_ref(v_traces_806_);
lean_dec_ref(v_traceState_805_);
v___x_807_ = lean_st_ref_take(v___y_802_);
v_traceState_808_ = lean_ctor_get(v___x_807_, 4);
v_env_809_ = lean_ctor_get(v___x_807_, 0);
v_nextMacroScope_810_ = lean_ctor_get(v___x_807_, 1);
v_ngen_811_ = lean_ctor_get(v___x_807_, 2);
v_auxDeclNGen_812_ = lean_ctor_get(v___x_807_, 3);
v_cache_813_ = lean_ctor_get(v___x_807_, 5);
v_recordedDeps_814_ = lean_ctor_get(v___x_807_, 6);
v_messages_815_ = lean_ctor_get(v___x_807_, 7);
v_infoState_816_ = lean_ctor_get(v___x_807_, 8);
v_snapshotTasks_817_ = lean_ctor_get(v___x_807_, 9);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_836_ == 0)
{
v___x_819_ = v___x_807_;
v_isShared_820_ = v_isSharedCheck_836_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_snapshotTasks_817_);
lean_inc(v_infoState_816_);
lean_inc(v_messages_815_);
lean_inc(v_recordedDeps_814_);
lean_inc(v_cache_813_);
lean_inc(v_traceState_808_);
lean_inc(v_auxDeclNGen_812_);
lean_inc(v_ngen_811_);
lean_inc(v_nextMacroScope_810_);
lean_inc(v_env_809_);
lean_dec(v___x_807_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_836_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
uint64_t v_tid_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_834_; 
v_tid_821_ = lean_ctor_get_uint64(v_traceState_808_, sizeof(void*)*1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_traceState_808_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v_traceState_808_, 0);
lean_dec(v_unused_835_);
v___x_823_ = v_traceState_808_;
v_isShared_824_ = v_isSharedCheck_834_;
goto v_resetjp_822_;
}
else
{
lean_dec(v_traceState_808_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_834_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_825_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_825_);
lean_ctor_set_uint64(v_reuseFailAlloc_833_, sizeof(void*)*1, v_tid_821_);
v___x_827_ = v_reuseFailAlloc_833_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_829_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v___x_827_);
v___x_829_ = v___x_819_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_env_809_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_nextMacroScope_810_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_ngen_811_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_auxDeclNGen_812_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_832_, 5, v_cache_813_);
lean_ctor_set(v_reuseFailAlloc_832_, 6, v_recordedDeps_814_);
lean_ctor_set(v_reuseFailAlloc_832_, 7, v_messages_815_);
lean_ctor_set(v_reuseFailAlloc_832_, 8, v_infoState_816_);
lean_ctor_set(v_reuseFailAlloc_832_, 9, v_snapshotTasks_817_);
v___x_829_ = v_reuseFailAlloc_832_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_st_ref_put(v___y_802_, v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v_traces_806_);
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___boxed(lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_837_);
lean_dec(v___y_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4(lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___boxed(lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4(v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_871_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(lean_object* v_opts_872_, lean_object* v_opt_873_){
_start:
{
lean_object* v_name_874_; lean_object* v_defValue_875_; lean_object* v_map_876_; lean_object* v___x_877_; 
v_name_874_ = lean_ctor_get(v_opt_873_, 0);
v_defValue_875_ = lean_ctor_get(v_opt_873_, 1);
v_map_876_ = lean_ctor_get(v_opts_872_, 0);
v___x_877_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_876_, v_name_874_);
if (lean_obj_tag(v___x_877_) == 0)
{
uint8_t v___x_878_; 
v___x_878_ = lean_unbox(v_defValue_875_);
return v___x_878_;
}
else
{
lean_object* v_val_879_; 
v_val_879_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v___x_877_, 1);
if (lean_obj_tag(v_val_879_) == 1)
{
uint8_t v_v_880_; 
v_v_880_ = lean_ctor_get_uint8(v_val_879_, 0);
lean_dec_ref_known(v_val_879_, 0);
return v_v_880_;
}
else
{
uint8_t v___x_881_; 
lean_dec(v_val_879_);
v___x_881_ = lean_unbox(v_defValue_875_);
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5___boxed(lean_object* v_opts_882_, lean_object* v_opt_883_){
_start:
{
uint8_t v_res_884_; lean_object* v_r_885_; 
v_res_884_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_882_, v_opt_883_);
lean_dec_ref(v_opt_883_);
lean_dec_ref(v_opts_882_);
v_r_885_ = lean_box(v_res_884_);
return v_r_885_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__1));
v___x_890_ = l_Lean_MessageData_ofFormat(v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0(lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___boxed(lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0(v_x_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec_ref(v_x_909_);
return v_res_925_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__0));
v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1(lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___boxed(lean_object* v_x_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1(v_x_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec_ref(v_x_947_);
return v_res_963_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__1));
v___x_968_ = l_Lean_MessageData_ofFormat(v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2(lean_object* v_x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___boxed(lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2(v_x_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_x_987_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3(lean_object* v___x_1004_, lean_object* v___x_1005_, lean_object* v_result_1006_, lean_object* v___x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1004_, v___x_1005_, v_result_1006_, v___x_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed(lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_result_1012_, lean_object* v___x_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3(v___x_1010_, v___x_1011_, v_result_1012_, v___x_1013_, v_x_1014_);
lean_dec_ref(v___x_1011_);
lean_dec_ref(v___x_1010_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(lean_object* v___f_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_ref_1029_; lean_object* v___x_1030_; 
v_ref_1029_ = lean_ctor_get(v___y_1026_, 2);
v___x_1030_ = l_IO_lazyPure___redArg(v___f_1016_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1050_; 
v_a_1039_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1041_ = v___x_1030_;
v_isShared_1042_ = v_isSharedCheck_1050_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1030_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1050_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1043_ = lean_io_error_to_string(v_a_1039_);
v___x_1044_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
v___x_1045_ = l_Lean_MessageData_ofFormat(v___x_1044_);
lean_inc(v_ref_1029_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_ref_1029_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1046_);
v___x_1048_ = v___x_1041_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4___boxed(lean_object* v___f_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5(lean_object* v_aig_1065_, lean_object* v_bvExpr_1066_, lean_object* v_blastCache_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_1065_, v_bvExpr_1066_, v_blastCache_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(lean_object* v___f_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_ref_1083_; lean_object* v___x_1084_; 
v_ref_1083_ = lean_ctor_get(v___y_1080_, 2);
v___x_1084_ = l_IO_lazyPure___redArg(v___f_1070_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1104_; 
v_a_1093_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1095_ = v___x_1084_;
v_isShared_1096_ = v_isSharedCheck_1104_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1084_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1104_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1097_ = lean_io_error_to_string(v_a_1093_);
v___x_1098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
v___x_1099_ = l_Lean_MessageData_ofFormat(v___x_1098_);
lean_inc(v_ref_1083_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v_ref_1083_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1100_);
v___x_1102_ = v___x_1095_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6___boxed(lean_object* v___f_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1118_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__0));
v___x_1121_ = l_Lean_stringToMessageData(v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7(lean_object* v_x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___boxed(lean_object* v_x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7(v_x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_x_1140_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(lean_object* v_x_1157_){
_start:
{
if (lean_obj_tag(v_x_1157_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v_x_1157_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x_1157_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v_x_1157_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v_x_1157_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 1);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v_x_1157_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_x_1157_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v_x_1157_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v_x_1157_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 0);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg___boxed(lean_object* v_x_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_x_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(lean_object* v_e_1178_){
_start:
{
if (lean_obj_tag(v_e_1178_) == 0)
{
uint8_t v___x_1179_; 
v___x_1179_ = 2;
return v___x_1179_;
}
else
{
uint8_t v___x_1180_; 
v___x_1180_ = 0;
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10___boxed(lean_object* v_e_1181_){
_start:
{
uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_res_1182_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(v_e_1181_);
lean_dec_ref(v_e_1181_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(lean_object* v_msgData_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v___x_1192_; lean_object* v_toCold_1193_; lean_object* v_mctx_1194_; lean_object* v_lctx_1195_; lean_object* v_options_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1190_ = lean_st_ref_get(v___y_1188_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_st_ref_get(v___y_1186_);
v_toCold_1193_ = lean_ctor_get(v___y_1187_, 0);
v_mctx_1194_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_mctx_1194_);
lean_dec(v___x_1192_);
v_lctx_1195_ = lean_ctor_get(v___y_1185_, 2);
v_options_1196_ = lean_ctor_get(v_toCold_1193_, 2);
lean_inc_ref(v_options_1196_);
lean_inc_ref(v_lctx_1195_);
v___x_1197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1197_, 0, v_env_1191_);
lean_ctor_set(v___x_1197_, 1, v_mctx_1194_);
lean_ctor_set(v___x_1197_, 2, v_lctx_1195_);
lean_ctor_set(v___x_1197_, 3, v_options_1196_);
v___x_1198_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_msgData_1184_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3___boxed(lean_object* v_msgData_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msgData_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(size_t v_sz_1207_, size_t v_i_1208_, lean_object* v_bs_1209_){
_start:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_usize_dec_lt(v_i_1208_, v_sz_1207_);
if (v___x_1210_ == 0)
{
return v_bs_1209_;
}
else
{
lean_object* v_v_1211_; lean_object* v_msg_1212_; lean_object* v___x_1213_; lean_object* v_bs_x27_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v_v_1211_ = lean_array_uget_borrowed(v_bs_1209_, v_i_1208_);
v_msg_1212_ = lean_ctor_get(v_v_1211_, 1);
lean_inc_ref(v_msg_1212_);
v___x_1213_ = lean_unsigned_to_nat(0u);
v_bs_x27_1214_ = lean_array_uset(v_bs_1209_, v_i_1208_, v___x_1213_);
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1208_, v___x_1215_);
v___x_1217_ = lean_array_uset(v_bs_x27_1214_, v_i_1208_, v_msg_1212_);
v_i_1208_ = v___x_1216_;
v_bs_1209_ = v___x_1217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_1219_, lean_object* v_i_1220_, lean_object* v_bs_1221_){
_start:
{
size_t v_sz_boxed_1222_; size_t v_i_boxed_1223_; lean_object* v_res_1224_; 
v_sz_boxed_1222_ = lean_unbox_usize(v_sz_1219_);
lean_dec(v_sz_1219_);
v_i_boxed_1223_ = lean_unbox_usize(v_i_1220_);
lean_dec(v_i_1220_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(v_sz_boxed_1222_, v_i_boxed_1223_, v_bs_1221_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(lean_object* v_oldTraces_1225_, lean_object* v_data_1226_, lean_object* v_ref_1227_, lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_toCold_1234_; lean_object* v_currRecDepth_1235_; lean_object* v_ref_1236_; uint16_t v_optionFlags_1237_; uint8_t v_suppressElabErrors_1238_; uint8_t v_isRecordingDeps_1239_; lean_object* v_ref_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_traceState_1243_; lean_object* v_traces_1244_; lean_object* v___x_1245_; size_t v_sz_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v_msg_1249_; lean_object* v___x_1250_; lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1289_; 
v_toCold_1234_ = lean_ctor_get(v___y_1231_, 0);
v_currRecDepth_1235_ = lean_ctor_get(v___y_1231_, 1);
v_ref_1236_ = lean_ctor_get(v___y_1231_, 2);
v_optionFlags_1237_ = lean_ctor_get_uint16(v___y_1231_, sizeof(void*)*3);
v_suppressElabErrors_1238_ = lean_ctor_get_uint8(v___y_1231_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1239_ = lean_ctor_get_uint8(v___y_1231_, sizeof(void*)*3 + 3);
v_ref_1240_ = l_Lean_replaceRef(v_ref_1227_, v_ref_1236_);
lean_inc(v_currRecDepth_1235_);
lean_inc_ref(v_toCold_1234_);
v___x_1241_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1241_, 0, v_toCold_1234_);
lean_ctor_set(v___x_1241_, 1, v_currRecDepth_1235_);
lean_ctor_set(v___x_1241_, 2, v_ref_1240_);
lean_ctor_set_uint16(v___x_1241_, sizeof(void*)*3, v_optionFlags_1237_);
lean_ctor_set_uint8(v___x_1241_, sizeof(void*)*3 + 2, v_suppressElabErrors_1238_);
lean_ctor_set_uint8(v___x_1241_, sizeof(void*)*3 + 3, v_isRecordingDeps_1239_);
v___x_1242_ = lean_st_ref_get(v___y_1232_);
v_traceState_1243_ = lean_ctor_get(v___x_1242_, 4);
lean_inc_ref(v_traceState_1243_);
lean_dec(v___x_1242_);
v_traces_1244_ = lean_ctor_get(v_traceState_1243_, 0);
lean_inc_ref(v_traces_1244_);
lean_dec_ref(v_traceState_1243_);
v___x_1245_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1244_);
lean_dec_ref(v_traces_1244_);
v_sz_1246_ = lean_array_size(v___x_1245_);
v___x_1247_ = ((size_t)0ULL);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(v_sz_1246_, v___x_1247_, v___x_1245_);
v_msg_1249_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1249_, 0, v_data_1226_);
lean_ctor_set(v_msg_1249_, 1, v_msg_1228_);
lean_ctor_set(v_msg_1249_, 2, v___x_1248_);
v___x_1250_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1249_, v___y_1229_, v___y_1230_, v___x_1241_, v___y_1232_);
lean_dec_ref_known(v___x_1241_, 3);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1289_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1289_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v_traceState_1256_; lean_object* v_env_1257_; lean_object* v_nextMacroScope_1258_; lean_object* v_ngen_1259_; lean_object* v_auxDeclNGen_1260_; lean_object* v_cache_1261_; lean_object* v_recordedDeps_1262_; lean_object* v_messages_1263_; lean_object* v_infoState_1264_; lean_object* v_snapshotTasks_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1288_; 
v___x_1255_ = lean_st_ref_take(v___y_1232_);
v_traceState_1256_ = lean_ctor_get(v___x_1255_, 4);
v_env_1257_ = lean_ctor_get(v___x_1255_, 0);
v_nextMacroScope_1258_ = lean_ctor_get(v___x_1255_, 1);
v_ngen_1259_ = lean_ctor_get(v___x_1255_, 2);
v_auxDeclNGen_1260_ = lean_ctor_get(v___x_1255_, 3);
v_cache_1261_ = lean_ctor_get(v___x_1255_, 5);
v_recordedDeps_1262_ = lean_ctor_get(v___x_1255_, 6);
v_messages_1263_ = lean_ctor_get(v___x_1255_, 7);
v_infoState_1264_ = lean_ctor_get(v___x_1255_, 8);
v_snapshotTasks_1265_ = lean_ctor_get(v___x_1255_, 9);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1267_ = v___x_1255_;
v_isShared_1268_ = v_isSharedCheck_1288_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snapshotTasks_1265_);
lean_inc(v_infoState_1264_);
lean_inc(v_messages_1263_);
lean_inc(v_recordedDeps_1262_);
lean_inc(v_cache_1261_);
lean_inc(v_traceState_1256_);
lean_inc(v_auxDeclNGen_1260_);
lean_inc(v_ngen_1259_);
lean_inc(v_nextMacroScope_1258_);
lean_inc(v_env_1257_);
lean_dec(v___x_1255_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1288_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
uint64_t v_tid_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1286_; 
v_tid_1269_ = lean_ctor_get_uint64(v_traceState_1256_, sizeof(void*)*1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_traceState_1256_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v_traceState_1256_, 0);
lean_dec(v_unused_1287_);
v___x_1271_ = v_traceState_1256_;
v_isShared_1272_ = v_isSharedCheck_1286_;
goto v_resetjp_1270_;
}
else
{
lean_dec(v_traceState_1256_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1286_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_ref_1227_);
lean_ctor_set(v___x_1274_, 1, v_a_1251_);
v___x_1275_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1225_, v___x_1274_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1275_);
v___x_1277_ = v___x_1271_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1275_);
lean_ctor_set_uint64(v_reuseFailAlloc_1285_, sizeof(void*)*1, v_tid_1269_);
v___x_1277_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1279_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 4, v___x_1277_);
v___x_1279_ = v___x_1267_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_env_1257_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_nextMacroScope_1258_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_ngen_1259_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_auxDeclNGen_1260_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1284_, 5, v_cache_1261_);
lean_ctor_set(v_reuseFailAlloc_1284_, 6, v_recordedDeps_1262_);
lean_ctor_set(v_reuseFailAlloc_1284_, 7, v_messages_1263_);
lean_ctor_set(v_reuseFailAlloc_1284_, 8, v_infoState_1264_);
lean_ctor_set(v_reuseFailAlloc_1284_, 9, v_snapshotTasks_1265_);
v___x_1279_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = lean_st_ref_put(v___y_1232_, v___x_1279_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1273_);
v___x_1282_ = v___x_1253_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1273_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg___boxed(lean_object* v_oldTraces_1290_, lean_object* v_data_1291_, lean_object* v_ref_1292_, lean_object* v_msg_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1290_, v_data_1291_, v_ref_1292_, v_msg_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(lean_object* v_opts_1300_, lean_object* v_opt_1301_){
_start:
{
lean_object* v_name_1302_; lean_object* v_defValue_1303_; lean_object* v_map_1304_; lean_object* v___x_1305_; 
v_name_1302_ = lean_ctor_get(v_opt_1301_, 0);
v_defValue_1303_ = lean_ctor_get(v_opt_1301_, 1);
v_map_1304_ = lean_ctor_get(v_opts_1300_, 0);
v___x_1305_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1304_, v_name_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_inc(v_defValue_1303_);
return v_defValue_1303_;
}
else
{
lean_object* v_val_1306_; 
v_val_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v___x_1305_, 1);
if (lean_obj_tag(v_val_1306_) == 3)
{
lean_object* v_v_1307_; 
v_v_1307_ = lean_ctor_get(v_val_1306_, 0);
lean_inc(v_v_1307_);
lean_dec_ref_known(v_val_1306_, 1);
return v_v_1307_;
}
else
{
lean_dec(v_val_1306_);
lean_inc(v_defValue_1303_);
return v_defValue_1303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11___boxed(lean_object* v_opts_1308_, lean_object* v_opt_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1308_, v_opt_1309_);
lean_dec_ref(v_opt_1309_);
lean_dec_ref(v_opts_1308_);
return v_res_1310_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1311_; double v___x_1312_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_float_of_nat(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__1));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1316_; double v___x_1317_; 
v___x_1316_ = lean_unsigned_to_nat(1000u);
v___x_1317_ = lean_float_of_nat(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(lean_object* v_cls_1318_, uint8_t v_collapsed_1319_, lean_object* v_tag_1320_, lean_object* v_opts_1321_, uint8_t v_clsEnabled_1322_, lean_object* v_oldTraces_1323_, lean_object* v_msg_1324_, lean_object* v_resStartStop_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v_data_1346_; lean_object* v_fst_1357_; lean_object* v_snd_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; lean_object* v___y_1362_; lean_object* v_a_1363_; uint8_t v___y_1378_; double v___y_1410_; 
v_fst_1341_ = lean_ctor_get(v_resStartStop_1325_, 0);
lean_inc(v_fst_1341_);
v_snd_1342_ = lean_ctor_get(v_resStartStop_1325_, 1);
lean_inc(v_snd_1342_);
lean_dec_ref(v_resStartStop_1325_);
v_fst_1357_ = lean_ctor_get(v_snd_1342_, 0);
lean_inc(v_fst_1357_);
v_snd_1358_ = lean_ctor_get(v_snd_1342_, 1);
lean_inc(v_snd_1358_);
lean_dec(v_snd_1342_);
v___x_1359_ = l_Lean_trace_profiler;
v___x_1360_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1321_, v___x_1359_);
if (v___x_1360_ == 0)
{
v___y_1378_ = v___x_1360_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1416_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1321_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; double v___x_1419_; double v___x_1420_; double v___x_1421_; 
v___x_1417_ = l_Lean_trace_profiler_threshold;
v___x_1418_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1321_, v___x_1417_);
v___x_1419_ = lean_float_of_nat(v___x_1418_);
v___x_1420_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_1421_ = lean_float_div(v___x_1419_, v___x_1420_);
v___y_1410_ = v___x_1421_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; double v___x_1424_; 
v___x_1422_ = l_Lean_trace_profiler_threshold;
v___x_1423_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1321_, v___x_1422_);
v___x_1424_ = lean_float_of_nat(v___x_1423_);
v___y_1410_ = v___x_1424_;
goto v___jp_1409_;
}
}
v___jp_1343_:
{
lean_object* v___x_1347_; 
lean_inc(v___y_1344_);
v___x_1347_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1323_, v_data_1346_, v___y_1344_, v___y_1345_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; 
lean_dec_ref_known(v___x_1347_, 1);
v___x_1348_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1341_);
return v___x_1348_;
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_fst_1341_);
v_a_1349_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1347_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1347_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
v___jp_1361_:
{
uint8_t v_result_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; double v___x_1367_; lean_object* v_data_1368_; 
v_result_1364_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(v_fst_1341_);
v___x_1365_ = lean_box(v_result_1364_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
v___x_1367_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_1320_);
lean_inc_ref(v___x_1366_);
lean_inc(v_cls_1318_);
v_data_1368_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1368_, 0, v_cls_1318_);
lean_ctor_set(v_data_1368_, 1, v___x_1366_);
lean_ctor_set(v_data_1368_, 2, v_tag_1320_);
lean_ctor_set_float(v_data_1368_, sizeof(void*)*3, v___x_1367_);
lean_ctor_set_float(v_data_1368_, sizeof(void*)*3 + 8, v___x_1367_);
lean_ctor_set_uint8(v_data_1368_, sizeof(void*)*3 + 16, v_collapsed_1319_);
if (v___x_1360_ == 0)
{
lean_dec_ref_known(v___x_1366_, 1);
lean_dec(v_snd_1358_);
lean_dec(v_fst_1357_);
lean_dec_ref(v_tag_1320_);
lean_dec(v_cls_1318_);
v___y_1344_ = v___y_1362_;
v___y_1345_ = v_a_1363_;
v_data_1346_ = v_data_1368_;
goto v___jp_1343_;
}
else
{
lean_object* v_data_1369_; double v___x_1370_; double v___x_1371_; 
lean_dec_ref_known(v_data_1368_, 3);
v_data_1369_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1369_, 0, v_cls_1318_);
lean_ctor_set(v_data_1369_, 1, v___x_1366_);
lean_ctor_set(v_data_1369_, 2, v_tag_1320_);
v___x_1370_ = lean_unbox_float(v_fst_1357_);
lean_dec(v_fst_1357_);
lean_ctor_set_float(v_data_1369_, sizeof(void*)*3, v___x_1370_);
v___x_1371_ = lean_unbox_float(v_snd_1358_);
lean_dec(v_snd_1358_);
lean_ctor_set_float(v_data_1369_, sizeof(void*)*3 + 8, v___x_1371_);
lean_ctor_set_uint8(v_data_1369_, sizeof(void*)*3 + 16, v_collapsed_1319_);
v___y_1344_ = v___y_1362_;
v___y_1345_ = v_a_1363_;
v_data_1346_ = v_data_1369_;
goto v___jp_1343_;
}
}
v___jp_1372_:
{
lean_object* v_ref_1373_; lean_object* v___x_1374_; 
v_ref_1373_ = lean_ctor_get(v___y_1338_, 2);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
lean_inc(v_fst_1341_);
v___x_1374_ = lean_apply_16(v_msg_1324_, v_fst_1341_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___y_1362_ = v_ref_1373_;
v_a_1363_ = v_a_1375_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1376_; 
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_1362_ = v_ref_1373_;
v_a_1363_ = v___x_1376_;
goto v___jp_1361_;
}
}
v___jp_1377_:
{
if (v_clsEnabled_1322_ == 0)
{
if (v___y_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v_traceState_1380_; lean_object* v_env_1381_; lean_object* v_nextMacroScope_1382_; lean_object* v_ngen_1383_; lean_object* v_auxDeclNGen_1384_; lean_object* v_cache_1385_; lean_object* v_recordedDeps_1386_; lean_object* v_messages_1387_; lean_object* v_infoState_1388_; lean_object* v_snapshotTasks_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1408_; 
lean_dec(v_snd_1358_);
lean_dec(v_fst_1357_);
lean_dec_ref(v_msg_1324_);
lean_dec_ref(v_tag_1320_);
lean_dec(v_cls_1318_);
v___x_1379_ = lean_st_ref_take(v___y_1339_);
v_traceState_1380_ = lean_ctor_get(v___x_1379_, 4);
v_env_1381_ = lean_ctor_get(v___x_1379_, 0);
v_nextMacroScope_1382_ = lean_ctor_get(v___x_1379_, 1);
v_ngen_1383_ = lean_ctor_get(v___x_1379_, 2);
v_auxDeclNGen_1384_ = lean_ctor_get(v___x_1379_, 3);
v_cache_1385_ = lean_ctor_get(v___x_1379_, 5);
v_recordedDeps_1386_ = lean_ctor_get(v___x_1379_, 6);
v_messages_1387_ = lean_ctor_get(v___x_1379_, 7);
v_infoState_1388_ = lean_ctor_get(v___x_1379_, 8);
v_snapshotTasks_1389_ = lean_ctor_get(v___x_1379_, 9);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1391_ = v___x_1379_;
v_isShared_1392_ = v_isSharedCheck_1408_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_snapshotTasks_1389_);
lean_inc(v_infoState_1388_);
lean_inc(v_messages_1387_);
lean_inc(v_recordedDeps_1386_);
lean_inc(v_cache_1385_);
lean_inc(v_traceState_1380_);
lean_inc(v_auxDeclNGen_1384_);
lean_inc(v_ngen_1383_);
lean_inc(v_nextMacroScope_1382_);
lean_inc(v_env_1381_);
lean_dec(v___x_1379_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1408_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
uint64_t v_tid_1393_; lean_object* v_traces_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1407_; 
v_tid_1393_ = lean_ctor_get_uint64(v_traceState_1380_, sizeof(void*)*1);
v_traces_1394_ = lean_ctor_get(v_traceState_1380_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_traceState_1380_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1396_ = v_traceState_1380_;
v_isShared_1397_ = v_isSharedCheck_1407_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_traces_1394_);
lean_dec(v_traceState_1380_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1407_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1398_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1323_, v_traces_1394_);
lean_dec_ref(v_traces_1394_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1398_);
v___x_1400_ = v___x_1396_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1398_);
lean_ctor_set_uint64(v_reuseFailAlloc_1406_, sizeof(void*)*1, v_tid_1393_);
v___x_1400_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v___x_1400_);
v___x_1402_ = v___x_1391_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_env_1381_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_nextMacroScope_1382_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_ngen_1383_);
lean_ctor_set(v_reuseFailAlloc_1405_, 3, v_auxDeclNGen_1384_);
lean_ctor_set(v_reuseFailAlloc_1405_, 4, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1405_, 5, v_cache_1385_);
lean_ctor_set(v_reuseFailAlloc_1405_, 6, v_recordedDeps_1386_);
lean_ctor_set(v_reuseFailAlloc_1405_, 7, v_messages_1387_);
lean_ctor_set(v_reuseFailAlloc_1405_, 8, v_infoState_1388_);
lean_ctor_set(v_reuseFailAlloc_1405_, 9, v_snapshotTasks_1389_);
v___x_1402_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_st_ref_put(v___y_1339_, v___x_1402_);
v___x_1404_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1341_);
return v___x_1404_;
}
}
}
}
}
else
{
goto v___jp_1372_;
}
}
else
{
goto v___jp_1372_;
}
}
v___jp_1409_:
{
double v___x_1411_; double v___x_1412_; double v___x_1413_; uint8_t v___x_1414_; 
v___x_1411_ = lean_unbox_float(v_snd_1358_);
v___x_1412_ = lean_unbox_float(v_fst_1357_);
v___x_1413_ = lean_float_sub(v___x_1411_, v___x_1412_);
v___x_1414_ = lean_float_decLt(v___y_1410_, v___x_1413_);
v___y_1378_ = v___x_1414_;
goto v___jp_1377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___boxed(lean_object** _args){
lean_object* v_cls_1425_ = _args[0];
lean_object* v_collapsed_1426_ = _args[1];
lean_object* v_tag_1427_ = _args[2];
lean_object* v_opts_1428_ = _args[3];
lean_object* v_clsEnabled_1429_ = _args[4];
lean_object* v_oldTraces_1430_ = _args[5];
lean_object* v_msg_1431_ = _args[6];
lean_object* v_resStartStop_1432_ = _args[7];
lean_object* v___y_1433_ = _args[8];
lean_object* v___y_1434_ = _args[9];
lean_object* v___y_1435_ = _args[10];
lean_object* v___y_1436_ = _args[11];
lean_object* v___y_1437_ = _args[12];
lean_object* v___y_1438_ = _args[13];
lean_object* v___y_1439_ = _args[14];
lean_object* v___y_1440_ = _args[15];
lean_object* v___y_1441_ = _args[16];
lean_object* v___y_1442_ = _args[17];
lean_object* v___y_1443_ = _args[18];
lean_object* v___y_1444_ = _args[19];
lean_object* v___y_1445_ = _args[20];
lean_object* v___y_1446_ = _args[21];
lean_object* v___y_1447_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_1448_; uint8_t v_clsEnabled_boxed_1449_; lean_object* v_res_1450_; 
v_collapsed_boxed_1448_ = lean_unbox(v_collapsed_1426_);
v_clsEnabled_boxed_1449_ = lean_unbox(v_clsEnabled_1429_);
v_res_1450_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v_cls_1425_, v_collapsed_boxed_1448_, v_tag_1427_, v_opts_1428_, v_clsEnabled_boxed_1449_, v_oldTraces_1430_, v_msg_1431_, v_resStartStop_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v_opts_1428_);
return v_res_1450_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(lean_object* v_a_1451_, lean_object* v_x_1452_){
_start:
{
if (lean_obj_tag(v_x_1452_) == 0)
{
uint8_t v___x_1453_; 
v___x_1453_ = 0;
return v___x_1453_;
}
else
{
lean_object* v_key_1454_; lean_object* v_tail_1455_; uint8_t v___x_1456_; 
v_key_1454_ = lean_ctor_get(v_x_1452_, 0);
v_tail_1455_ = lean_ctor_get(v_x_1452_, 2);
v___x_1456_ = lean_nat_dec_eq(v_key_1454_, v_a_1451_);
if (v___x_1456_ == 0)
{
v_x_1452_ = v_tail_1455_;
goto _start;
}
else
{
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg___boxed(lean_object* v_a_1458_, lean_object* v_x_1459_){
_start:
{
uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1458_, v_x_1459_);
lean_dec(v_x_1459_);
lean_dec(v_a_1458_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(lean_object* v___x_1462_, lean_object* v_m_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_buckets_1465_; lean_object* v___x_1466_; uint64_t v___x_1467_; uint64_t v___x_1468_; uint64_t v___x_1469_; uint64_t v_fold_1470_; uint64_t v___x_1471_; uint64_t v___x_1472_; uint64_t v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_buckets_1465_ = lean_ctor_get(v_m_1463_, 1);
v___x_1466_ = lean_array_get_size(v_buckets_1465_);
v___x_1467_ = lean_uint64_of_nat(v_a_1464_);
v___x_1468_ = 32ULL;
v___x_1469_ = lean_uint64_shift_right(v___x_1467_, v___x_1468_);
v_fold_1470_ = lean_uint64_xor(v___x_1467_, v___x_1469_);
v___x_1471_ = 16ULL;
v___x_1472_ = lean_uint64_shift_right(v_fold_1470_, v___x_1471_);
v___x_1473_ = lean_uint64_xor(v_fold_1470_, v___x_1472_);
v___x_1474_ = lean_uint64_to_usize(v___x_1473_);
v___x_1475_ = lean_usize_of_nat(v___x_1466_);
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_sub(v___x_1475_, v___x_1476_);
v___x_1478_ = lean_usize_land(v___x_1474_, v___x_1477_);
v___x_1479_ = lean_array_uget_borrowed(v_buckets_1465_, v___x_1478_);
v___x_1480_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1464_, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg___boxed(lean_object* v___x_1481_, lean_object* v_m_1482_, lean_object* v_a_1483_){
_start:
{
uint8_t v_res_1484_; lean_object* v_r_1485_; 
v_res_1484_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_1481_, v_m_1482_, v_a_1483_);
lean_dec(v_a_1483_);
lean_dec_ref(v_m_1482_);
lean_dec(v___x_1481_);
v_r_1485_ = lean_box(v_res_1484_);
return v_r_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(lean_object* v_x_1486_, lean_object* v_x_1487_){
_start:
{
if (lean_obj_tag(v_x_1487_) == 0)
{
return v_x_1486_;
}
else
{
lean_object* v_key_1488_; lean_object* v_value_1489_; lean_object* v_tail_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1513_; 
v_key_1488_ = lean_ctor_get(v_x_1487_, 0);
v_value_1489_ = lean_ctor_get(v_x_1487_, 1);
v_tail_1490_ = lean_ctor_get(v_x_1487_, 2);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_x_1487_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1492_ = v_x_1487_;
v_isShared_1493_ = v_isSharedCheck_1513_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_tail_1490_);
lean_inc(v_value_1489_);
lean_inc(v_key_1488_);
lean_dec(v_x_1487_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1513_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; uint64_t v___x_1495_; uint64_t v___x_1496_; uint64_t v___x_1497_; uint64_t v_fold_1498_; uint64_t v___x_1499_; uint64_t v___x_1500_; uint64_t v___x_1501_; size_t v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1494_ = lean_array_get_size(v_x_1486_);
v___x_1495_ = lean_uint64_of_nat(v_key_1488_);
v___x_1496_ = 32ULL;
v___x_1497_ = lean_uint64_shift_right(v___x_1495_, v___x_1496_);
v_fold_1498_ = lean_uint64_xor(v___x_1495_, v___x_1497_);
v___x_1499_ = 16ULL;
v___x_1500_ = lean_uint64_shift_right(v_fold_1498_, v___x_1499_);
v___x_1501_ = lean_uint64_xor(v_fold_1498_, v___x_1500_);
v___x_1502_ = lean_uint64_to_usize(v___x_1501_);
v___x_1503_ = lean_usize_of_nat(v___x_1494_);
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = lean_usize_sub(v___x_1503_, v___x_1504_);
v___x_1506_ = lean_usize_land(v___x_1502_, v___x_1505_);
v___x_1507_ = lean_array_uget_borrowed(v_x_1486_, v___x_1506_);
lean_inc(v___x_1507_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 2, v___x_1507_);
v___x_1509_ = v___x_1492_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_key_1488_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_value_1489_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_array_uset(v_x_1486_, v___x_1506_, v___x_1509_);
v_x_1486_ = v___x_1510_;
v_x_1487_ = v_tail_1490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(lean_object* v_i_1514_, lean_object* v_source_1515_, lean_object* v_target_1516_){
_start:
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = lean_array_get_size(v_source_1515_);
v___x_1518_ = lean_nat_dec_lt(v_i_1514_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_dec_ref(v_source_1515_);
lean_dec(v_i_1514_);
return v_target_1516_;
}
else
{
lean_object* v_es_1519_; lean_object* v___x_1520_; lean_object* v_source_1521_; lean_object* v_target_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_es_1519_ = lean_array_fget(v_source_1515_, v_i_1514_);
v___x_1520_ = lean_box(0);
v_source_1521_ = lean_array_fset(v_source_1515_, v_i_1514_, v___x_1520_);
v_target_1522_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(v_target_1516_, v_es_1519_);
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_add(v_i_1514_, v___x_1523_);
lean_dec(v_i_1514_);
v_i_1514_ = v___x_1524_;
v_source_1515_ = v_source_1521_;
v_target_1516_ = v_target_1522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(lean_object* v___x_1526_, lean_object* v_data_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_nbuckets_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1528_ = lean_array_get_size(v_data_1527_);
v___x_1529_ = lean_unsigned_to_nat(2u);
v_nbuckets_1530_ = lean_nat_mul(v___x_1528_, v___x_1529_);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_mk_array(v_nbuckets_1530_, v___x_1532_);
v___x_1534_ = lean_array_propagate_mark(v_data_1527_, v___x_1533_);
v___x_1535_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(v___x_1531_, v_data_1527_, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg___boxed(lean_object* v___x_1536_, lean_object* v_data_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_1536_, v_data_1537_);
lean_dec(v___x_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(lean_object* v___x_1539_, lean_object* v_m_1540_, lean_object* v_a_1541_, lean_object* v_b_1542_){
_start:
{
lean_object* v_size_1543_; lean_object* v_buckets_1544_; lean_object* v___x_1545_; uint64_t v___x_1546_; uint64_t v___x_1547_; uint64_t v___x_1548_; uint64_t v_fold_1549_; uint64_t v___x_1550_; uint64_t v___x_1551_; uint64_t v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; lean_object* v_bkt_1558_; uint8_t v___x_1559_; 
v_size_1543_ = lean_ctor_get(v_m_1540_, 0);
v_buckets_1544_ = lean_ctor_get(v_m_1540_, 1);
v___x_1545_ = lean_array_get_size(v_buckets_1544_);
v___x_1546_ = lean_uint64_of_nat(v_a_1541_);
v___x_1547_ = 32ULL;
v___x_1548_ = lean_uint64_shift_right(v___x_1546_, v___x_1547_);
v_fold_1549_ = lean_uint64_xor(v___x_1546_, v___x_1548_);
v___x_1550_ = 16ULL;
v___x_1551_ = lean_uint64_shift_right(v_fold_1549_, v___x_1550_);
v___x_1552_ = lean_uint64_xor(v_fold_1549_, v___x_1551_);
v___x_1553_ = lean_uint64_to_usize(v___x_1552_);
v___x_1554_ = lean_usize_of_nat(v___x_1545_);
v___x_1555_ = ((size_t)1ULL);
v___x_1556_ = lean_usize_sub(v___x_1554_, v___x_1555_);
v___x_1557_ = lean_usize_land(v___x_1553_, v___x_1556_);
v_bkt_1558_ = lean_array_uget_borrowed(v_buckets_1544_, v___x_1557_);
v___x_1559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1541_, v_bkt_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1580_; 
lean_inc_ref(v_buckets_1544_);
lean_inc(v_size_1543_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_m_1540_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; 
v_unused_1581_ = lean_ctor_get(v_m_1540_, 1);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_m_1540_, 0);
lean_dec(v_unused_1582_);
v___x_1561_ = v_m_1540_;
v_isShared_1562_ = v_isSharedCheck_1580_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_m_1540_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1580_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v_size_x27_1564_; lean_object* v___x_1565_; lean_object* v_buckets_x27_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1563_ = lean_unsigned_to_nat(1u);
v_size_x27_1564_ = lean_nat_add(v_size_1543_, v___x_1563_);
lean_dec(v_size_1543_);
lean_inc(v_bkt_1558_);
v___x_1565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1541_);
lean_ctor_set(v___x_1565_, 1, v_b_1542_);
lean_ctor_set(v___x_1565_, 2, v_bkt_1558_);
v_buckets_x27_1566_ = lean_array_uset(v_buckets_1544_, v___x_1557_, v___x_1565_);
v___x_1567_ = lean_unsigned_to_nat(4u);
v___x_1568_ = lean_nat_mul(v_size_x27_1564_, v___x_1567_);
v___x_1569_ = lean_unsigned_to_nat(3u);
v___x_1570_ = lean_nat_div(v___x_1568_, v___x_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_array_get_size(v_buckets_x27_1566_);
v___x_1572_ = lean_nat_dec_le(v___x_1570_, v___x_1571_);
lean_dec(v___x_1570_);
if (v___x_1572_ == 0)
{
lean_object* v_val_1573_; lean_object* v___x_1575_; 
v_val_1573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_1539_, v_buckets_x27_1566_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v_val_1573_);
lean_ctor_set(v___x_1561_, 0, v_size_x27_1564_);
v___x_1575_ = v___x_1561_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_size_x27_1564_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_val_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v___x_1578_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v_buckets_x27_1566_);
lean_ctor_set(v___x_1561_, 0, v_size_x27_1564_);
v___x_1578_ = v___x_1561_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_size_x27_1564_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_buckets_x27_1566_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_dec(v_b_1542_);
lean_dec(v_a_1541_);
return v_m_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg___boxed(lean_object* v___x_1583_, lean_object* v_m_1584_, lean_object* v_a_1585_, lean_object* v_b_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_1583_, v_m_1584_, v_a_1585_, v_b_1586_);
lean_dec(v___x_1583_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(lean_object* v_acc_1591_, lean_object* v_decls_1592_, lean_object* v_idx_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_array_get_size(v_decls_1592_);
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_1595_, v_a_1594_, v_idx_1593_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_box(0);
lean_inc(v_idx_1593_);
v___x_1598_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_1595_, v_a_1594_, v_idx_1593_, v___x_1597_);
v___x_1599_ = lean_array_fget_borrowed(v_decls_1592_, v_idx_1593_);
if (lean_obj_tag(v___x_1599_) == 2)
{
lean_object* v_l_1600_; lean_object* v_r_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___y_1605_; lean_object* v___y_1606_; uint8_t v___y_1607_; uint8_t v___y_1631_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_l_1600_ = lean_ctor_get(v___x_1599_, 0);
v_r_1601_ = lean_ctor_get(v___x_1599_, 1);
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_shiftr(v_l_1600_, v___x_1602_);
v___x_1637_ = lean_nat_land(v___x_1602_, v_l_1600_);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_nat_dec_eq(v___x_1637_, v___x_1638_);
lean_dec(v___x_1637_);
if (v___x_1639_ == 0)
{
uint8_t v___x_1640_; 
v___x_1640_ = 1;
v___y_1631_ = v___x_1640_;
goto v___jp_1630_;
}
else
{
v___y_1631_ = v___x_1596_;
goto v___jp_1630_;
}
v___jp_1604_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_fst_1627_; lean_object* v_snd_1628_; 
v___x_1608_ = l_Nat_reprFast(v_idx_1593_);
v___x_1609_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__0));
lean_inc_ref(v___x_1608_);
v___x_1610_ = lean_string_append(v___x_1608_, v___x_1609_);
lean_inc(v___x_1603_);
v___x_1611_ = l_Nat_reprFast(v___x_1603_);
v___x_1612_ = lean_string_append(v___x_1610_, v___x_1611_);
lean_dec_ref(v___x_1611_);
v___x_1613_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1605_);
v___x_1614_ = lean_string_append(v___x_1612_, v___x_1613_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__1));
v___x_1616_ = lean_string_append(v___x_1614_, v___x_1615_);
v___x_1617_ = lean_string_append(v___x_1616_, v___x_1608_);
lean_dec_ref(v___x_1608_);
v___x_1618_ = lean_string_append(v___x_1617_, v___x_1609_);
lean_inc(v___y_1606_);
v___x_1619_ = l_Nat_reprFast(v___y_1606_);
v___x_1620_ = lean_string_append(v___x_1618_, v___x_1619_);
lean_dec_ref(v___x_1619_);
v___x_1621_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1607_);
v___x_1622_ = lean_string_append(v___x_1620_, v___x_1621_);
lean_dec_ref(v___x_1621_);
v___x_1623_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__2));
v___x_1624_ = lean_string_append(v___x_1622_, v___x_1623_);
v___x_1625_ = lean_string_append(v_acc_1591_, v___x_1624_);
lean_dec_ref(v___x_1624_);
v___x_1626_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v___x_1625_, v_decls_1592_, v___x_1603_, v___x_1598_);
v_fst_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_fst_1627_);
v_snd_1628_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_snd_1628_);
lean_dec_ref(v___x_1626_);
v_acc_1591_ = v_fst_1627_;
v_idx_1593_ = v___y_1606_;
v_a_1594_ = v_snd_1628_;
goto _start;
}
v___jp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1632_ = lean_nat_shiftr(v_r_1601_, v___x_1602_);
v___x_1633_ = lean_nat_land(v___x_1602_, v_r_1601_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
lean_dec(v___x_1633_);
if (v___x_1635_ == 0)
{
uint8_t v___x_1636_; 
v___x_1636_ = 1;
v___y_1605_ = v___y_1631_;
v___y_1606_ = v___x_1632_;
v___y_1607_ = v___x_1636_;
goto v___jp_1604_;
}
else
{
v___y_1605_ = v___y_1631_;
v___y_1606_ = v___x_1632_;
v___y_1607_ = v___x_1596_;
goto v___jp_1604_;
}
}
}
else
{
lean_object* v___x_1641_; 
lean_dec(v_idx_1593_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_acc_1591_);
lean_ctor_set(v___x_1641_, 1, v___x_1598_);
return v___x_1641_;
}
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_idx_1593_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_acc_1591_);
lean_ctor_set(v___x_1642_, 1, v_a_1594_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___boxed(lean_object* v_acc_1643_, lean_object* v_decls_1644_, lean_object* v_idx_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v_acc_1643_, v_decls_1644_, v_idx_1645_, v_a_1646_);
lean_dec_ref(v_decls_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(lean_object* v_decls_1656_, lean_object* v_idx_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_array_fget_borrowed(v_decls_1656_, v_idx_1657_);
switch(lean_obj_tag(v___x_1658_))
{
case 0:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1659_ = l_Nat_reprFast(v_idx_1657_);
v___x_1660_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
v___x_1661_ = lean_string_append(v___x_1659_, v___x_1660_);
v___x_1662_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__1));
v___x_1663_ = lean_string_append(v___x_1661_, v___x_1662_);
v___x_1664_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__2));
v___x_1665_ = lean_string_append(v___x_1663_, v___x_1664_);
return v___x_1665_;
}
case 1:
{
lean_object* v_idx_1666_; lean_object* v_var_1667_; lean_object* v_idx_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_idx_1666_ = lean_ctor_get(v___x_1658_, 0);
v_var_1667_ = lean_ctor_get(v_idx_1666_, 0);
v_idx_1668_ = lean_ctor_get(v_idx_1666_, 2);
v___x_1669_ = l_Nat_reprFast(v_idx_1657_);
v___x_1670_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
v___x_1671_ = lean_string_append(v___x_1669_, v___x_1670_);
v___x_1672_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__3));
lean_inc(v_var_1667_);
v___x_1673_ = l_Nat_reprFast(v_var_1667_);
v___x_1674_ = lean_string_append(v___x_1672_, v___x_1673_);
lean_dec_ref(v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__4));
v___x_1676_ = lean_string_append(v___x_1674_, v___x_1675_);
lean_inc(v_idx_1668_);
v___x_1677_ = l_Nat_reprFast(v_idx_1668_);
v___x_1678_ = lean_string_append(v___x_1676_, v___x_1677_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__5));
v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
v___x_1681_ = lean_string_append(v___x_1671_, v___x_1680_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__6));
v___x_1683_ = lean_string_append(v___x_1681_, v___x_1682_);
return v___x_1683_;
}
default: 
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1684_ = l_Nat_reprFast(v_idx_1657_);
v___x_1685_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
lean_inc_ref(v___x_1684_);
v___x_1686_ = lean_string_append(v___x_1684_, v___x_1685_);
v___x_1687_ = lean_string_append(v___x_1686_, v___x_1684_);
lean_dec_ref(v___x_1684_);
v___x_1688_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__7));
v___x_1689_ = lean_string_append(v___x_1687_, v___x_1688_);
return v___x_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___boxed(lean_object* v_decls_1690_, lean_object* v_idx_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(v_decls_1690_, v_idx_1691_);
lean_dec_ref(v_decls_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(lean_object* v_decls_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
if (lean_obj_tag(v_x_1695_) == 0)
{
return v_x_1694_;
}
else
{
lean_object* v_key_1696_; lean_object* v_tail_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_key_1696_ = lean_ctor_get(v_x_1695_, 0);
lean_inc(v_key_1696_);
v_tail_1697_ = lean_ctor_get(v_x_1695_, 2);
lean_inc(v_tail_1697_);
lean_dec_ref_known(v_x_1695_, 3);
v___x_1698_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(v_decls_1693_, v_key_1696_);
v___x_1699_ = lean_string_append(v_x_1694_, v___x_1698_);
lean_dec_ref(v___x_1698_);
v_x_1694_ = v___x_1699_;
v_x_1695_ = v_tail_1697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17___boxed(lean_object* v_decls_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(v_decls_1701_, v_x_1702_, v_x_1703_);
lean_dec_ref(v_decls_1701_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(lean_object* v_decls_1705_, lean_object* v_as_1706_, size_t v_i_1707_, size_t v_stop_1708_, lean_object* v_b_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_eq(v_i_1707_, v_stop_1708_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; 
v___x_1711_ = lean_array_uget_borrowed(v_as_1706_, v_i_1707_);
lean_inc(v___x_1711_);
v___x_1712_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(v_decls_1705_, v_b_1709_, v___x_1711_);
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1707_, v___x_1713_);
v_i_1707_ = v___x_1714_;
v_b_1709_ = v___x_1712_;
goto _start;
}
else
{
return v_b_1709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18___boxed(lean_object* v_decls_1716_, lean_object* v_as_1717_, lean_object* v_i_1718_, lean_object* v_stop_1719_, lean_object* v_b_1720_){
_start:
{
size_t v_i_boxed_1721_; size_t v_stop_boxed_1722_; lean_object* v_res_1723_; 
v_i_boxed_1721_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_stop_boxed_1722_ = lean_unbox_usize(v_stop_1719_);
lean_dec(v_stop_1719_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(v_decls_1716_, v_as_1717_, v_i_boxed_1721_, v_stop_boxed_1722_, v_b_1720_);
lean_dec_ref(v_as_1717_);
lean_dec_ref(v_decls_1716_);
return v_res_1723_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = lean_unsigned_to_nat(16u);
v___x_1727_ = lean_mk_array(v___x_1726_, v___x_1725_);
return v___x_1727_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1);
v___x_1729_ = lean_unsigned_to_nat(0u);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v___x_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(lean_object* v_entry_1733_){
_start:
{
lean_object* v_aig_1734_; lean_object* v_ref_1735_; lean_object* v_decls_1736_; lean_object* v_gate_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_fst_1742_; lean_object* v_snd_1743_; lean_object* v___y_1745_; lean_object* v_buckets_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v_aig_1734_ = lean_ctor_get(v_entry_1733_, 0);
lean_inc_ref(v_aig_1734_);
v_ref_1735_ = lean_ctor_get(v_entry_1733_, 1);
lean_inc_ref(v_ref_1735_);
lean_dec_ref(v_entry_1733_);
v_decls_1736_ = lean_ctor_get(v_aig_1734_, 0);
lean_inc_ref(v_decls_1736_);
lean_dec_ref(v_aig_1734_);
v_gate_1737_ = lean_ctor_get(v_ref_1735_, 0);
lean_inc(v_gate_1737_);
lean_dec_ref(v_ref_1735_);
v___x_1738_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2);
v___x_1741_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v___x_1738_, v_decls_1736_, v_gate_1737_, v___x_1740_);
v_fst_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_fst_1742_);
v_snd_1743_ = lean_ctor_get(v___x_1741_, 1);
lean_inc(v_snd_1743_);
lean_dec_ref(v___x_1741_);
v_buckets_1751_ = lean_ctor_get(v_snd_1743_, 1);
lean_inc_ref(v_buckets_1751_);
lean_dec(v_snd_1743_);
v___x_1752_ = lean_array_get_size(v_buckets_1751_);
v___x_1753_ = lean_nat_dec_lt(v___x_1739_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_dec_ref(v_buckets_1751_);
lean_dec_ref(v_decls_1736_);
v___y_1745_ = v___x_1738_;
goto v___jp_1744_;
}
else
{
size_t v___x_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = ((size_t)0ULL);
v___x_1755_ = lean_usize_of_nat(v___x_1752_);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(v_decls_1736_, v_buckets_1751_, v___x_1754_, v___x_1755_, v___x_1738_);
lean_dec_ref(v_buckets_1751_);
lean_dec_ref(v_decls_1736_);
v___y_1745_ = v___x_1756_;
goto v___jp_1744_;
}
v___jp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1746_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__3));
v___x_1747_ = lean_string_append(v___x_1746_, v___y_1745_);
lean_dec_ref(v___y_1745_);
v___x_1748_ = lean_string_append(v___x_1747_, v_fst_1742_);
lean_dec(v_fst_1742_);
v___x_1749_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__4));
v___x_1750_ = lean_string_append(v___x_1748_, v___x_1749_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(lean_object* v_cls_1759_, lean_object* v_msg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_ref_1766_; lean_object* v___x_1767_; lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1813_; 
v_ref_1766_ = lean_ctor_get(v___y_1763_, 2);
v___x_1767_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1813_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1813_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v_traceState_1773_; lean_object* v_env_1774_; lean_object* v_nextMacroScope_1775_; lean_object* v_ngen_1776_; lean_object* v_auxDeclNGen_1777_; lean_object* v_cache_1778_; lean_object* v_recordedDeps_1779_; lean_object* v_messages_1780_; lean_object* v_infoState_1781_; lean_object* v_snapshotTasks_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1812_; 
v___x_1772_ = lean_st_ref_take(v___y_1764_);
v_traceState_1773_ = lean_ctor_get(v___x_1772_, 4);
v_env_1774_ = lean_ctor_get(v___x_1772_, 0);
v_nextMacroScope_1775_ = lean_ctor_get(v___x_1772_, 1);
v_ngen_1776_ = lean_ctor_get(v___x_1772_, 2);
v_auxDeclNGen_1777_ = lean_ctor_get(v___x_1772_, 3);
v_cache_1778_ = lean_ctor_get(v___x_1772_, 5);
v_recordedDeps_1779_ = lean_ctor_get(v___x_1772_, 6);
v_messages_1780_ = lean_ctor_get(v___x_1772_, 7);
v_infoState_1781_ = lean_ctor_get(v___x_1772_, 8);
v_snapshotTasks_1782_ = lean_ctor_get(v___x_1772_, 9);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1784_ = v___x_1772_;
v_isShared_1785_ = v_isSharedCheck_1812_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snapshotTasks_1782_);
lean_inc(v_infoState_1781_);
lean_inc(v_messages_1780_);
lean_inc(v_recordedDeps_1779_);
lean_inc(v_cache_1778_);
lean_inc(v_traceState_1773_);
lean_inc(v_auxDeclNGen_1777_);
lean_inc(v_ngen_1776_);
lean_inc(v_nextMacroScope_1775_);
lean_inc(v_env_1774_);
lean_dec(v___x_1772_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1812_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
uint64_t v_tid_1786_; lean_object* v_traces_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1811_; 
v_tid_1786_ = lean_ctor_get_uint64(v_traceState_1773_, sizeof(void*)*1);
v_traces_1787_ = lean_ctor_get(v_traceState_1773_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_traceState_1773_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1789_ = v_traceState_1773_;
v_isShared_1790_ = v_isSharedCheck_1811_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_traces_1787_);
lean_dec(v_traceState_1773_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1811_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; double v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
v___x_1794_ = 0;
v___x_1795_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_1796_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1796_, 0, v_cls_1759_);
lean_ctor_set(v___x_1796_, 1, v___x_1792_);
lean_ctor_set(v___x_1796_, 2, v___x_1795_);
lean_ctor_set_float(v___x_1796_, sizeof(void*)*3, v___x_1793_);
lean_ctor_set_float(v___x_1796_, sizeof(void*)*3 + 8, v___x_1793_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*3 + 16, v___x_1794_);
v___x_1797_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___closed__0));
v___x_1798_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1796_);
lean_ctor_set(v___x_1798_, 1, v_a_1768_);
lean_ctor_set(v___x_1798_, 2, v___x_1797_);
lean_inc(v_ref_1766_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_ref_1766_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_Lean_PersistentArray_push___redArg(v_traces_1787_, v___x_1799_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1800_);
v___x_1802_ = v___x_1789_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1800_);
lean_ctor_set_uint64(v_reuseFailAlloc_1810_, sizeof(void*)*1, v_tid_1786_);
v___x_1802_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 4, v___x_1802_);
v___x_1804_ = v___x_1784_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_env_1774_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_nextMacroScope_1775_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v_ngen_1776_);
lean_ctor_set(v_reuseFailAlloc_1809_, 3, v_auxDeclNGen_1777_);
lean_ctor_set(v_reuseFailAlloc_1809_, 4, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1809_, 5, v_cache_1778_);
lean_ctor_set(v_reuseFailAlloc_1809_, 6, v_recordedDeps_1779_);
lean_ctor_set(v_reuseFailAlloc_1809_, 7, v_messages_1780_);
lean_ctor_set(v_reuseFailAlloc_1809_, 8, v_infoState_1781_);
lean_ctor_set(v_reuseFailAlloc_1809_, 9, v_snapshotTasks_1782_);
v___x_1804_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = lean_st_ref_put(v___y_1764_, v___x_1804_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1791_);
v___x_1807_ = v___x_1770_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1791_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___boxed(lean_object* v_cls_1814_, lean_object* v_msg_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_1814_, v_msg_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(lean_object* v_msg_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_ref_1828_; lean_object* v___x_1829_; lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1838_; 
v_ref_1828_ = lean_ctor_get(v___y_1825_, 2);
v___x_1829_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_inc(v_ref_1828_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_ref_1828_);
lean_ctor_set(v___x_1834_, 1, v_a_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 1);
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg___boxed(lean_object* v_msg_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v_msg_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
return v_res_1845_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(lean_object* v_e_1846_){
_start:
{
if (lean_obj_tag(v_e_1846_) == 0)
{
uint8_t v___x_1847_; 
v___x_1847_ = 2;
return v___x_1847_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = 0;
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13___boxed(lean_object* v_e_1849_){
_start:
{
uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_res_1850_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(v_e_1849_);
lean_dec_ref(v_e_1849_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(lean_object* v_cls_1852_, uint8_t v_collapsed_1853_, lean_object* v_tag_1854_, lean_object* v_opts_1855_, uint8_t v_clsEnabled_1856_, lean_object* v_oldTraces_1857_, lean_object* v_msg_1858_, lean_object* v_resStartStop_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_fst_1875_; lean_object* v_snd_1876_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v_data_1880_; lean_object* v_fst_1891_; lean_object* v_snd_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___y_1896_; lean_object* v_a_1897_; uint8_t v___y_1912_; double v___y_1944_; 
v_fst_1875_ = lean_ctor_get(v_resStartStop_1859_, 0);
lean_inc(v_fst_1875_);
v_snd_1876_ = lean_ctor_get(v_resStartStop_1859_, 1);
lean_inc(v_snd_1876_);
lean_dec_ref(v_resStartStop_1859_);
v_fst_1891_ = lean_ctor_get(v_snd_1876_, 0);
lean_inc(v_fst_1891_);
v_snd_1892_ = lean_ctor_get(v_snd_1876_, 1);
lean_inc(v_snd_1892_);
lean_dec(v_snd_1876_);
v___x_1893_ = l_Lean_trace_profiler;
v___x_1894_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1855_, v___x_1893_);
if (v___x_1894_ == 0)
{
v___y_1912_ = v___x_1894_;
goto v___jp_1911_;
}
else
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1950_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1855_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; double v___x_1953_; double v___x_1954_; double v___x_1955_; 
v___x_1951_ = l_Lean_trace_profiler_threshold;
v___x_1952_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1855_, v___x_1951_);
v___x_1953_ = lean_float_of_nat(v___x_1952_);
v___x_1954_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_1955_ = lean_float_div(v___x_1953_, v___x_1954_);
v___y_1944_ = v___x_1955_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; double v___x_1958_; 
v___x_1956_ = l_Lean_trace_profiler_threshold;
v___x_1957_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1855_, v___x_1956_);
v___x_1958_ = lean_float_of_nat(v___x_1957_);
v___y_1944_ = v___x_1958_;
goto v___jp_1943_;
}
}
v___jp_1877_:
{
lean_object* v___x_1881_; 
lean_inc(v___y_1878_);
v___x_1881_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1857_, v_data_1880_, v___y_1878_, v___y_1879_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v___x_1882_; 
lean_dec_ref_known(v___x_1881_, 1);
v___x_1882_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1875_);
return v___x_1882_;
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_fst_1875_);
v_a_1883_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1881_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
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
v___jp_1895_:
{
uint8_t v_result_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; double v___x_1901_; lean_object* v_data_1902_; 
v_result_1898_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(v_fst_1875_);
v___x_1899_ = lean_box(v_result_1898_);
v___x_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
v___x_1901_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_1854_);
lean_inc_ref(v___x_1900_);
lean_inc(v_cls_1852_);
v_data_1902_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1902_, 0, v_cls_1852_);
lean_ctor_set(v_data_1902_, 1, v___x_1900_);
lean_ctor_set(v_data_1902_, 2, v_tag_1854_);
lean_ctor_set_float(v_data_1902_, sizeof(void*)*3, v___x_1901_);
lean_ctor_set_float(v_data_1902_, sizeof(void*)*3 + 8, v___x_1901_);
lean_ctor_set_uint8(v_data_1902_, sizeof(void*)*3 + 16, v_collapsed_1853_);
if (v___x_1894_ == 0)
{
lean_dec_ref_known(v___x_1900_, 1);
lean_dec(v_snd_1892_);
lean_dec(v_fst_1891_);
lean_dec_ref(v_tag_1854_);
lean_dec(v_cls_1852_);
v___y_1878_ = v___y_1896_;
v___y_1879_ = v_a_1897_;
v_data_1880_ = v_data_1902_;
goto v___jp_1877_;
}
else
{
lean_object* v_data_1903_; double v___x_1904_; double v___x_1905_; 
lean_dec_ref_known(v_data_1902_, 3);
v_data_1903_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1903_, 0, v_cls_1852_);
lean_ctor_set(v_data_1903_, 1, v___x_1900_);
lean_ctor_set(v_data_1903_, 2, v_tag_1854_);
v___x_1904_ = lean_unbox_float(v_fst_1891_);
lean_dec(v_fst_1891_);
lean_ctor_set_float(v_data_1903_, sizeof(void*)*3, v___x_1904_);
v___x_1905_ = lean_unbox_float(v_snd_1892_);
lean_dec(v_snd_1892_);
lean_ctor_set_float(v_data_1903_, sizeof(void*)*3 + 8, v___x_1905_);
lean_ctor_set_uint8(v_data_1903_, sizeof(void*)*3 + 16, v_collapsed_1853_);
v___y_1878_ = v___y_1896_;
v___y_1879_ = v_a_1897_;
v_data_1880_ = v_data_1903_;
goto v___jp_1877_;
}
}
v___jp_1906_:
{
lean_object* v_ref_1907_; lean_object* v___x_1908_; 
v_ref_1907_ = lean_ctor_get(v___y_1872_, 2);
lean_inc(v___y_1873_);
lean_inc_ref(v___y_1872_);
lean_inc(v___y_1871_);
lean_inc_ref(v___y_1870_);
lean_inc(v___y_1869_);
lean_inc_ref(v___y_1868_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc(v___y_1864_);
lean_inc_ref(v___y_1863_);
lean_inc(v___y_1862_);
lean_inc(v___y_1861_);
lean_inc_ref(v___y_1860_);
lean_inc(v_fst_1875_);
v___x_1908_ = lean_apply_16(v_msg_1858_, v_fst_1875_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, lean_box(0));
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___y_1896_ = v_ref_1907_;
v_a_1897_ = v_a_1909_;
goto v___jp_1895_;
}
else
{
lean_object* v___x_1910_; 
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_1896_ = v_ref_1907_;
v_a_1897_ = v___x_1910_;
goto v___jp_1895_;
}
}
v___jp_1911_:
{
if (v_clsEnabled_1856_ == 0)
{
if (v___y_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v_traceState_1914_; lean_object* v_env_1915_; lean_object* v_nextMacroScope_1916_; lean_object* v_ngen_1917_; lean_object* v_auxDeclNGen_1918_; lean_object* v_cache_1919_; lean_object* v_recordedDeps_1920_; lean_object* v_messages_1921_; lean_object* v_infoState_1922_; lean_object* v_snapshotTasks_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_snd_1892_);
lean_dec(v_fst_1891_);
lean_dec_ref(v_msg_1858_);
lean_dec_ref(v_tag_1854_);
lean_dec(v_cls_1852_);
v___x_1913_ = lean_st_ref_take(v___y_1873_);
v_traceState_1914_ = lean_ctor_get(v___x_1913_, 4);
v_env_1915_ = lean_ctor_get(v___x_1913_, 0);
v_nextMacroScope_1916_ = lean_ctor_get(v___x_1913_, 1);
v_ngen_1917_ = lean_ctor_get(v___x_1913_, 2);
v_auxDeclNGen_1918_ = lean_ctor_get(v___x_1913_, 3);
v_cache_1919_ = lean_ctor_get(v___x_1913_, 5);
v_recordedDeps_1920_ = lean_ctor_get(v___x_1913_, 6);
v_messages_1921_ = lean_ctor_get(v___x_1913_, 7);
v_infoState_1922_ = lean_ctor_get(v___x_1913_, 8);
v_snapshotTasks_1923_ = lean_ctor_get(v___x_1913_, 9);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1925_ = v___x_1913_;
v_isShared_1926_ = v_isSharedCheck_1942_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_snapshotTasks_1923_);
lean_inc(v_infoState_1922_);
lean_inc(v_messages_1921_);
lean_inc(v_recordedDeps_1920_);
lean_inc(v_cache_1919_);
lean_inc(v_traceState_1914_);
lean_inc(v_auxDeclNGen_1918_);
lean_inc(v_ngen_1917_);
lean_inc(v_nextMacroScope_1916_);
lean_inc(v_env_1915_);
lean_dec(v___x_1913_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1942_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
uint64_t v_tid_1927_; lean_object* v_traces_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1941_; 
v_tid_1927_ = lean_ctor_get_uint64(v_traceState_1914_, sizeof(void*)*1);
v_traces_1928_ = lean_ctor_get(v_traceState_1914_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_traceState_1914_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1930_ = v_traceState_1914_;
v_isShared_1931_ = v_isSharedCheck_1941_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_traces_1928_);
lean_dec(v_traceState_1914_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1941_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1857_, v_traces_1928_);
lean_dec_ref(v_traces_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1932_);
lean_ctor_set_uint64(v_reuseFailAlloc_1940_, sizeof(void*)*1, v_tid_1927_);
v___x_1934_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 4, v___x_1934_);
v___x_1936_ = v___x_1925_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_env_1915_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_nextMacroScope_1916_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_ngen_1917_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_auxDeclNGen_1918_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1939_, 5, v_cache_1919_);
lean_ctor_set(v_reuseFailAlloc_1939_, 6, v_recordedDeps_1920_);
lean_ctor_set(v_reuseFailAlloc_1939_, 7, v_messages_1921_);
lean_ctor_set(v_reuseFailAlloc_1939_, 8, v_infoState_1922_);
lean_ctor_set(v_reuseFailAlloc_1939_, 9, v_snapshotTasks_1923_);
v___x_1936_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_st_ref_put(v___y_1873_, v___x_1936_);
v___x_1938_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1875_);
return v___x_1938_;
}
}
}
}
}
else
{
goto v___jp_1906_;
}
}
else
{
goto v___jp_1906_;
}
}
v___jp_1943_:
{
double v___x_1945_; double v___x_1946_; double v___x_1947_; uint8_t v___x_1948_; 
v___x_1945_ = lean_unbox_float(v_snd_1892_);
v___x_1946_ = lean_unbox_float(v_fst_1891_);
v___x_1947_ = lean_float_sub(v___x_1945_, v___x_1946_);
v___x_1948_ = lean_float_decLt(v___y_1944_, v___x_1947_);
v___y_1912_ = v___x_1948_;
goto v___jp_1911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7___boxed(lean_object** _args){
lean_object* v_cls_1959_ = _args[0];
lean_object* v_collapsed_1960_ = _args[1];
lean_object* v_tag_1961_ = _args[2];
lean_object* v_opts_1962_ = _args[3];
lean_object* v_clsEnabled_1963_ = _args[4];
lean_object* v_oldTraces_1964_ = _args[5];
lean_object* v_msg_1965_ = _args[6];
lean_object* v_resStartStop_1966_ = _args[7];
lean_object* v___y_1967_ = _args[8];
lean_object* v___y_1968_ = _args[9];
lean_object* v___y_1969_ = _args[10];
lean_object* v___y_1970_ = _args[11];
lean_object* v___y_1971_ = _args[12];
lean_object* v___y_1972_ = _args[13];
lean_object* v___y_1973_ = _args[14];
lean_object* v___y_1974_ = _args[15];
lean_object* v___y_1975_ = _args[16];
lean_object* v___y_1976_ = _args[17];
lean_object* v___y_1977_ = _args[18];
lean_object* v___y_1978_ = _args[19];
lean_object* v___y_1979_ = _args[20];
lean_object* v___y_1980_ = _args[21];
lean_object* v___y_1981_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_1982_; uint8_t v_clsEnabled_boxed_1983_; lean_object* v_res_1984_; 
v_collapsed_boxed_1982_ = lean_unbox(v_collapsed_1960_);
v_clsEnabled_boxed_1983_ = lean_unbox(v_clsEnabled_1963_);
v_res_1984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v_cls_1959_, v_collapsed_boxed_1982_, v_tag_1961_, v_opts_1962_, v_clsEnabled_boxed_1983_, v_oldTraces_1964_, v_msg_1965_, v_resStartStop_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec_ref(v_opts_1962_);
return v_res_1984_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__2));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4(void){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
return v___x_1993_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5);
v___x_1995_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
lean_ctor_set(v___x_1995_, 2, v___x_1994_);
lean_ctor_set(v___x_1995_, 3, v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__7));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9(void){
_start:
{
lean_object* v___x_1999_; double v___x_2000_; 
v___x_1999_ = lean_unsigned_to_nat(1000000000u);
v___x_2000_ = lean_float_of_nat(v___x_1999_);
return v___x_2000_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__15));
v___x_2008_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__14));
v___x_2009_ = l_System_FilePath_join(v___x_2008_, v___x_2007_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(lean_object* v_tacticContext_2010_, lean_object* v___x_2011_, lean_object* v_aig_2012_, lean_object* v___x_2013_, lean_object* v___x_2014_, lean_object* v___x_2015_, uint8_t v_hasTrace_2016_, lean_object* v___x_2017_, lean_object* v___f_2018_, lean_object* v___x_2019_, lean_object* v_cache_2020_, lean_object* v_ref_2021_, uint8_t v___x_2022_, lean_object* v_cls_2023_, lean_object* v___f_2024_, lean_object* v_cnfCache_2025_, lean_object* v___x_2026_, lean_object* v_result_2027_, lean_object* v___x_2028_, lean_object* v___x_2029_, lean_object* v_____r_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; uint8_t v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v_a_2224_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; uint8_t v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v_a_2256_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; uint8_t v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2341_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; uint8_t v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v_a_2516_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; uint8_t v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v_a_2549_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; uint8_t v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v_config_2668_; uint8_t v_graphviz_2669_; 
v_config_2668_ = lean_ctor_get(v_tacticContext_2010_, 5);
v_graphviz_2669_ = lean_ctor_get_uint8(v_config_2668_, sizeof(void*)*3 + 8);
if (v_graphviz_2669_ == 0)
{
v___y_2635_ = v___y_2031_;
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
goto v___jp_2634_;
}
else
{
lean_object* v_ref_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_ref_2670_ = lean_ctor_get(v___y_2043_, 2);
v___x_2671_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
lean_inc_ref(v_result_2027_);
v___x_2672_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v_result_2027_);
v___x_2673_ = l_IO_FS_writeFile(v___x_2671_, v___x_2672_);
lean_dec_ref(v___x_2672_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_dec_ref_known(v___x_2673_, 1);
v___y_2635_ = v___y_2031_;
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
goto v___jp_2634_;
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2685_; 
lean_dec_ref(v___x_2029_);
lean_dec_ref(v___x_2028_);
lean_dec_ref(v_result_2027_);
lean_dec_ref(v___x_2026_);
lean_dec_ref(v_cnfCache_2025_);
lean_dec_ref(v___f_2024_);
lean_dec(v_cls_2023_);
lean_dec_ref(v_cache_2020_);
lean_dec_ref(v___f_2018_);
lean_dec_ref(v___x_2017_);
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_aig_2012_);
lean_dec_ref(v_tacticContext_2010_);
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2678_ = lean_io_error_to_string(v_a_2674_);
v___x_2679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
v___x_2680_ = l_Lean_MessageData_ofFormat(v___x_2679_);
lean_inc(v_ref_2670_);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v_ref_2670_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2681_);
v___x_2683_ = v___x_2676_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
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
v___jp_2046_:
{
lean_object* v___x_2061_; 
v___x_2061_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___x_2011_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2063_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2051_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2073_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2073_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2073_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2068_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2012_, v_a_2062_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec(v_a_2062_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2069_);
v___x_2071_ = v___x_2066_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_a_2062_);
lean_dec_ref(v_aig_2012_);
v_a_2074_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2063_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2063_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_aig_2012_);
v_a_2082_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2061_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2061_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
v___jp_2090_:
{
if (lean_obj_tag(v___y_2106_) == 0)
{
lean_object* v_a_2107_; uint8_t v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___y_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___y_2106_, 1);
v___x_2108_ = lean_unbox(v_a_2107_);
lean_dec(v_a_2107_);
switch(v___x_2108_)
{
case 0:
{
lean_object* v_toCold_2109_; lean_object* v_options_2110_; uint8_t v_hasTrace_2111_; 
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_tacticContext_2010_);
v_toCold_2109_ = lean_ctor_get(v___y_2097_, 0);
v_options_2110_ = lean_ctor_get(v_toCold_2109_, 2);
v_hasTrace_2111_ = lean_ctor_get_uint8(v_options_2110_, sizeof(void*)*1);
if (v_hasTrace_2111_ == 0)
{
lean_dec(v___y_2096_);
v___y_2047_ = v___y_2100_;
v___y_2048_ = v___y_2104_;
v___y_2049_ = v___y_2094_;
v___y_2050_ = v___y_2103_;
v___y_2051_ = v___y_2105_;
v___y_2052_ = v___y_2091_;
v___y_2053_ = v___y_2092_;
v___y_2054_ = v___y_2093_;
v___y_2055_ = v___y_2098_;
v___y_2056_ = v___y_2101_;
v___y_2057_ = v___y_2095_;
v___y_2058_ = v___y_2099_;
v___y_2059_ = v___y_2097_;
v___y_2060_ = v___y_2102_;
goto v___jp_2046_;
}
else
{
lean_object* v_inheritedTraceOptions_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_inheritedTraceOptions_2112_ = lean_ctor_get(v_toCold_2109_, 11);
v___x_2113_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2096_);
v___x_2114_ = l_Lean_Name_append(v___x_2113_, v___y_2096_);
v___x_2115_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2112_, v_options_2110_, v___x_2114_);
lean_dec(v___x_2114_);
if (v___x_2115_ == 0)
{
lean_dec(v___y_2096_);
v___y_2047_ = v___y_2100_;
v___y_2048_ = v___y_2104_;
v___y_2049_ = v___y_2094_;
v___y_2050_ = v___y_2103_;
v___y_2051_ = v___y_2105_;
v___y_2052_ = v___y_2091_;
v___y_2053_ = v___y_2092_;
v___y_2054_ = v___y_2093_;
v___y_2055_ = v___y_2098_;
v___y_2056_ = v___y_2101_;
v___y_2057_ = v___y_2095_;
v___y_2058_ = v___y_2099_;
v___y_2059_ = v___y_2097_;
v___y_2060_ = v___y_2102_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
v___x_2117_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_2096_, v___x_2116_, v___y_2095_, v___y_2099_, v___y_2097_, v___y_2102_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_dec_ref_known(v___x_2117_, 1);
v___y_2047_ = v___y_2100_;
v___y_2048_ = v___y_2104_;
v___y_2049_ = v___y_2094_;
v___y_2050_ = v___y_2103_;
v___y_2051_ = v___y_2105_;
v___y_2052_ = v___y_2091_;
v___y_2053_ = v___y_2092_;
v___y_2054_ = v___y_2093_;
v___y_2055_ = v___y_2098_;
v___y_2056_ = v___y_2101_;
v___y_2057_ = v___y_2095_;
v___y_2058_ = v___y_2099_;
v___y_2059_ = v___y_2097_;
v___y_2060_ = v___y_2102_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v_aig_2012_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_2126_; lean_object* v_satExpr_2127_; lean_object* v_hypQueue_2128_; lean_object* v_usedHyps_2129_; uint8_t v_didChange_2130_; lean_object* v_theoryState_2131_; lean_object* v_solverTimeBudgetMs_2132_; lean_object* v_roundBudget_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v___y_2096_);
lean_dec_ref(v_aig_2012_);
v___x_2126_ = lean_st_ref_take(v___y_2104_);
v_satExpr_2127_ = lean_ctor_get(v___x_2126_, 0);
v_hypQueue_2128_ = lean_ctor_get(v___x_2126_, 1);
v_usedHyps_2129_ = lean_ctor_get(v___x_2126_, 2);
v_didChange_2130_ = lean_ctor_get_uint8(v___x_2126_, sizeof(void*)*6);
v_theoryState_2131_ = lean_ctor_get(v___x_2126_, 3);
v_solverTimeBudgetMs_2132_ = lean_ctor_get(v___x_2126_, 4);
v_roundBudget_2133_ = lean_ctor_get(v___x_2126_, 5);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2135_ = v___x_2126_;
v_isShared_2136_ = v_isSharedCheck_2194_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_roundBudget_2133_);
lean_inc(v_solverTimeBudgetMs_2132_);
lean_inc(v_theoryState_2131_);
lean_inc(v_usedHyps_2129_);
lean_inc(v_hypQueue_2128_);
lean_inc(v_satExpr_2127_);
lean_dec(v___x_2126_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2194_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v_satSolver_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2190_; 
v___x_2137_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_2138_ = lean_ctor_get(v_theoryState_2131_, 3);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_theoryState_2131_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; lean_object* v_unused_2192_; lean_object* v_unused_2193_; 
v_unused_2191_ = lean_ctor_get(v_theoryState_2131_, 2);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_theoryState_2131_, 1);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_theoryState_2131_, 0);
lean_dec(v_unused_2193_);
v___x_2140_ = v_theoryState_2131_;
v_isShared_2141_ = v_isSharedCheck_2190_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_satSolver_2138_);
lean_dec(v_theoryState_2131_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2190_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = lean_mk_array(v___x_2013_, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2014_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 2, v___x_2137_);
lean_ctor_set(v___x_2140_, 1, v___x_2015_);
lean_ctor_set(v___x_2140_, 0, v___x_2144_);
v___x_2146_ = v___x_2140_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_satSolver_2138_);
v___x_2146_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 3, v___x_2146_);
v___x_2148_ = v___x_2135_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_satExpr_2127_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_hypQueue_2128_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_usedHyps_2129_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2188_, 4, v_solverTimeBudgetMs_2132_);
lean_ctor_set(v_reuseFailAlloc_2188_, 5, v_roundBudget_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2188_, sizeof(void*)*6, v_didChange_2130_);
v___x_2148_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_st_ref_put(v___y_2104_, v___x_2148_);
v___x_2150_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_2100_, v___y_2104_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v_goal_2152_; lean_object* v___x_2153_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v_goal_2152_ = lean_ctor_get(v___y_2100_, 0);
lean_inc(v_goal_2152_);
v___x_2153_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_tacticContext_2010_, v_goal_2152_, v_a_2151_, v___y_2094_, v___y_2103_, v___y_2105_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2098_, v___y_2101_, v___y_2095_, v___y_2099_, v___y_2097_, v___y_2102_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2171_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2171_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2171_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
if (lean_obj_tag(v_a_2154_) == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_dec_ref_known(v_a_2154_, 1);
lean_del_object(v___x_2156_);
v___x_2158_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_2159_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_2158_, v___y_2095_, v___y_2099_, v___y_2097_, v___y_2102_);
return v___x_2159_;
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2170_; 
v_a_2160_ = lean_ctor_get(v_a_2154_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2162_ = v_a_2154_;
v_isShared_2163_ = v_isSharedCheck_2170_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v_a_2154_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2170_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2165_);
v___x_2167_ = v___x_2156_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_a_2172_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2153_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2153_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_tacticContext_2010_);
v_a_2180_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2150_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2150_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
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
lean_object* v___x_2195_; 
lean_dec(v___y_2096_);
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_aig_2012_);
lean_dec_ref(v_tacticContext_2010_);
v___x_2195_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_2097_, v___y_2102_);
return v___x_2195_;
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec(v___y_2096_);
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_aig_2012_);
lean_dec_ref(v_tacticContext_2010_);
v_a_2196_ = lean_ctor_get(v___y_2106_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___y_2106_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___y_2106_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___y_2106_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
v___jp_2204_:
{
lean_object* v___x_2225_; double v___x_2226_; double v___x_2227_; double v___x_2228_; double v___x_2229_; double v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2225_ = lean_io_mono_nanos_now();
v___x_2226_ = lean_float_of_nat(v___y_2210_);
v___x_2227_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2228_ = lean_float_div(v___x_2226_, v___x_2227_);
v___x_2229_ = lean_float_of_nat(v___x_2225_);
v___x_2230_ = lean_float_div(v___x_2229_, v___x_2227_);
v___x_2231_ = lean_box_float(v___x_2228_);
v___x_2232_ = lean_box_float(v___x_2230_);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2231_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_a_2224_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
lean_inc(v___y_2212_);
v___x_2235_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2212_, v_hasTrace_2016_, v___x_2017_, v___y_2219_, v___y_2211_, v___y_2220_, v___f_2018_, v___x_2234_, v___y_2217_, v___y_2222_, v___y_2208_, v___y_2221_, v___y_2223_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2215_, v___y_2216_, v___y_2209_, v___y_2214_, v___y_2213_, v___y_2218_);
v___y_2091_ = v___y_2205_;
v___y_2092_ = v___y_2206_;
v___y_2093_ = v___y_2207_;
v___y_2094_ = v___y_2208_;
v___y_2095_ = v___y_2209_;
v___y_2096_ = v___y_2212_;
v___y_2097_ = v___y_2213_;
v___y_2098_ = v___y_2215_;
v___y_2099_ = v___y_2214_;
v___y_2100_ = v___y_2217_;
v___y_2101_ = v___y_2216_;
v___y_2102_ = v___y_2218_;
v___y_2103_ = v___y_2221_;
v___y_2104_ = v___y_2222_;
v___y_2105_ = v___y_2223_;
v___y_2106_ = v___x_2235_;
goto v___jp_2090_;
}
v___jp_2236_:
{
lean_object* v___x_2257_; double v___x_2258_; double v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2257_ = lean_io_get_num_heartbeats();
v___x_2258_ = lean_float_of_nat(v___y_2240_);
v___x_2259_ = lean_float_of_nat(v___x_2257_);
v___x_2260_ = lean_box_float(v___x_2258_);
v___x_2261_ = lean_box_float(v___x_2259_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v_a_2256_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
lean_inc(v___y_2244_);
v___x_2264_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2244_, v_hasTrace_2016_, v___x_2017_, v___y_2251_, v___y_2243_, v___y_2252_, v___f_2018_, v___x_2263_, v___y_2249_, v___y_2254_, v___y_2241_, v___y_2253_, v___y_2255_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2247_, v___y_2248_, v___y_2242_, v___y_2246_, v___y_2245_, v___y_2250_);
v___y_2091_ = v___y_2237_;
v___y_2092_ = v___y_2238_;
v___y_2093_ = v___y_2239_;
v___y_2094_ = v___y_2241_;
v___y_2095_ = v___y_2242_;
v___y_2096_ = v___y_2244_;
v___y_2097_ = v___y_2245_;
v___y_2098_ = v___y_2247_;
v___y_2099_ = v___y_2246_;
v___y_2100_ = v___y_2249_;
v___y_2101_ = v___y_2248_;
v___y_2102_ = v___y_2250_;
v___y_2103_ = v___y_2253_;
v___y_2104_ = v___y_2254_;
v___y_2105_ = v___y_2255_;
v___y_2106_ = v___x_2264_;
goto v___jp_2090_;
}
v___jp_2265_:
{
lean_object* v___x_2284_; lean_object* v_a_2285_; uint8_t v___x_2286_; 
v___x_2284_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_2279_);
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_2280_, v___x_2019_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_io_mono_nanos_now();
v___x_2288_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2278_, v___y_2276_, v___y_2282_, v___y_2269_, v___y_2281_, v___y_2283_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2273_, v___y_2277_, v___y_2270_, v___y_2274_, v___y_2275_, v___y_2279_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set_tag(v___x_2291_, 1);
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
v___y_2205_ = v___y_2266_;
v___y_2206_ = v___y_2267_;
v___y_2207_ = v___y_2268_;
v___y_2208_ = v___y_2269_;
v___y_2209_ = v___y_2270_;
v___y_2210_ = v___x_2287_;
v___y_2211_ = v___y_2271_;
v___y_2212_ = v___y_2272_;
v___y_2213_ = v___y_2275_;
v___y_2214_ = v___y_2274_;
v___y_2215_ = v___y_2273_;
v___y_2216_ = v___y_2277_;
v___y_2217_ = v___y_2276_;
v___y_2218_ = v___y_2279_;
v___y_2219_ = v___y_2280_;
v___y_2220_ = v_a_2285_;
v___y_2221_ = v___y_2281_;
v___y_2222_ = v___y_2282_;
v___y_2223_ = v___y_2283_;
v_a_2224_ = v___x_2294_;
goto v___jp_2204_;
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
v_a_2297_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2288_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2288_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set_tag(v___x_2299_, 0);
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
v___y_2205_ = v___y_2266_;
v___y_2206_ = v___y_2267_;
v___y_2207_ = v___y_2268_;
v___y_2208_ = v___y_2269_;
v___y_2209_ = v___y_2270_;
v___y_2210_ = v___x_2287_;
v___y_2211_ = v___y_2271_;
v___y_2212_ = v___y_2272_;
v___y_2213_ = v___y_2275_;
v___y_2214_ = v___y_2274_;
v___y_2215_ = v___y_2273_;
v___y_2216_ = v___y_2277_;
v___y_2217_ = v___y_2276_;
v___y_2218_ = v___y_2279_;
v___y_2219_ = v___y_2280_;
v___y_2220_ = v_a_2285_;
v___y_2221_ = v___y_2281_;
v___y_2222_ = v___y_2282_;
v___y_2223_ = v___y_2283_;
v_a_2224_ = v___x_2302_;
goto v___jp_2204_;
}
}
}
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = lean_io_get_num_heartbeats();
v___x_2306_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2278_, v___y_2276_, v___y_2282_, v___y_2269_, v___y_2281_, v___y_2283_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2273_, v___y_2277_, v___y_2270_, v___y_2274_, v___y_2275_, v___y_2279_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 1);
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
v___y_2237_ = v___y_2266_;
v___y_2238_ = v___y_2267_;
v___y_2239_ = v___y_2268_;
v___y_2240_ = v___x_2305_;
v___y_2241_ = v___y_2269_;
v___y_2242_ = v___y_2270_;
v___y_2243_ = v___y_2271_;
v___y_2244_ = v___y_2272_;
v___y_2245_ = v___y_2275_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___y_2273_;
v___y_2248_ = v___y_2277_;
v___y_2249_ = v___y_2276_;
v___y_2250_ = v___y_2279_;
v___y_2251_ = v___y_2280_;
v___y_2252_ = v_a_2285_;
v___y_2253_ = v___y_2281_;
v___y_2254_ = v___y_2282_;
v___y_2255_ = v___y_2283_;
v_a_2256_ = v___x_2312_;
goto v___jp_2236_;
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v_a_2315_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2306_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2306_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set_tag(v___x_2317_, 0);
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
v___y_2237_ = v___y_2266_;
v___y_2238_ = v___y_2267_;
v___y_2239_ = v___y_2268_;
v___y_2240_ = v___x_2305_;
v___y_2241_ = v___y_2269_;
v___y_2242_ = v___y_2270_;
v___y_2243_ = v___y_2271_;
v___y_2244_ = v___y_2272_;
v___y_2245_ = v___y_2275_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___y_2273_;
v___y_2248_ = v___y_2277_;
v___y_2249_ = v___y_2276_;
v___y_2250_ = v___y_2279_;
v___y_2251_ = v___y_2280_;
v___y_2252_ = v_a_2285_;
v___y_2253_ = v___y_2281_;
v___y_2254_ = v___y_2282_;
v___y_2255_ = v___y_2283_;
v_a_2256_ = v___x_2320_;
goto v___jp_2236_;
}
}
}
}
}
v___jp_2323_:
{
lean_object* v_toCold_2342_; lean_object* v_ref_2343_; lean_object* v___x_2344_; 
v_toCold_2342_ = lean_ctor_get(v___y_2331_, 0);
v_ref_2343_ = lean_ctor_get(v___y_2331_, 2);
lean_inc_ref(v___y_2336_);
v___x_2344_ = l_Lean_Cadical_Solver_assume(v___y_2336_, v___y_2333_, v___y_2341_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_options_2345_; uint8_t v_hasTrace_2346_; 
lean_dec_ref_known(v___x_2344_, 1);
v_options_2345_ = lean_ctor_get(v_toCold_2342_, 2);
v_hasTrace_2346_ = lean_ctor_get_uint8(v_options_2345_, sizeof(void*)*1);
if (v_hasTrace_2346_ == 0)
{
lean_object* v___x_2347_; 
lean_dec_ref(v___f_2018_);
lean_dec_ref(v___x_2017_);
v___x_2347_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2336_, v___y_2335_, v___y_2339_, v___y_2327_, v___y_2338_, v___y_2340_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2332_, v___y_2334_, v___y_2328_, v___y_2330_, v___y_2331_, v___y_2337_);
v___y_2091_ = v___y_2324_;
v___y_2092_ = v___y_2325_;
v___y_2093_ = v___y_2326_;
v___y_2094_ = v___y_2327_;
v___y_2095_ = v___y_2328_;
v___y_2096_ = v___y_2329_;
v___y_2097_ = v___y_2331_;
v___y_2098_ = v___y_2332_;
v___y_2099_ = v___y_2330_;
v___y_2100_ = v___y_2335_;
v___y_2101_ = v___y_2334_;
v___y_2102_ = v___y_2337_;
v___y_2103_ = v___y_2338_;
v___y_2104_ = v___y_2339_;
v___y_2105_ = v___y_2340_;
v___y_2106_ = v___x_2347_;
goto v___jp_2090_;
}
else
{
lean_object* v_inheritedTraceOptions_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_inheritedTraceOptions_2348_ = lean_ctor_get(v_toCold_2342_, 11);
v___x_2349_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2329_);
v___x_2350_ = l_Lean_Name_append(v___x_2349_, v___y_2329_);
v___x_2351_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2348_, v_options_2345_, v___x_2350_);
lean_dec(v___x_2350_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = l_Lean_trace_profiler;
v___x_2353_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_2345_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_dec_ref(v___f_2018_);
lean_dec_ref(v___x_2017_);
v___x_2354_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2336_, v___y_2335_, v___y_2339_, v___y_2327_, v___y_2338_, v___y_2340_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2332_, v___y_2334_, v___y_2328_, v___y_2330_, v___y_2331_, v___y_2337_);
v___y_2091_ = v___y_2324_;
v___y_2092_ = v___y_2325_;
v___y_2093_ = v___y_2326_;
v___y_2094_ = v___y_2327_;
v___y_2095_ = v___y_2328_;
v___y_2096_ = v___y_2329_;
v___y_2097_ = v___y_2331_;
v___y_2098_ = v___y_2332_;
v___y_2099_ = v___y_2330_;
v___y_2100_ = v___y_2335_;
v___y_2101_ = v___y_2334_;
v___y_2102_ = v___y_2337_;
v___y_2103_ = v___y_2338_;
v___y_2104_ = v___y_2339_;
v___y_2105_ = v___y_2340_;
v___y_2106_ = v___x_2354_;
goto v___jp_2090_;
}
else
{
v___y_2266_ = v___y_2324_;
v___y_2267_ = v___y_2325_;
v___y_2268_ = v___y_2326_;
v___y_2269_ = v___y_2327_;
v___y_2270_ = v___y_2328_;
v___y_2271_ = v___x_2351_;
v___y_2272_ = v___y_2329_;
v___y_2273_ = v___y_2332_;
v___y_2274_ = v___y_2330_;
v___y_2275_ = v___y_2331_;
v___y_2276_ = v___y_2335_;
v___y_2277_ = v___y_2334_;
v___y_2278_ = v___y_2336_;
v___y_2279_ = v___y_2337_;
v___y_2280_ = v_options_2345_;
v___y_2281_ = v___y_2338_;
v___y_2282_ = v___y_2339_;
v___y_2283_ = v___y_2340_;
goto v___jp_2265_;
}
}
else
{
v___y_2266_ = v___y_2324_;
v___y_2267_ = v___y_2325_;
v___y_2268_ = v___y_2326_;
v___y_2269_ = v___y_2327_;
v___y_2270_ = v___y_2328_;
v___y_2271_ = v___x_2351_;
v___y_2272_ = v___y_2329_;
v___y_2273_ = v___y_2332_;
v___y_2274_ = v___y_2330_;
v___y_2275_ = v___y_2331_;
v___y_2276_ = v___y_2335_;
v___y_2277_ = v___y_2334_;
v___y_2278_ = v___y_2336_;
v___y_2279_ = v___y_2337_;
v___y_2280_ = v_options_2345_;
v___y_2281_ = v___y_2338_;
v___y_2282_ = v___y_2339_;
v___y_2283_ = v___y_2340_;
goto v___jp_2265_;
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2329_);
lean_dec_ref(v___f_2018_);
lean_dec_ref(v___x_2017_);
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_aig_2012_);
lean_dec_ref(v_tacticContext_2010_);
v_a_2355_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2357_ = v___x_2344_;
v_isShared_2358_ = v_isSharedCheck_2366_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2344_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2366_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2359_ = lean_io_error_to_string(v_a_2355_);
v___x_2360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
v___x_2361_ = l_Lean_MessageData_ofFormat(v___x_2360_);
lean_inc(v_ref_2343_);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_ref_2343_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2362_);
v___x_2364_ = v___x_2357_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
v___jp_2367_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v_theoryState_2388_; lean_object* v_satExpr_2389_; lean_object* v_hypQueue_2390_; lean_object* v_usedHyps_2391_; uint8_t v_didChange_2392_; lean_object* v_solverTimeBudgetMs_2393_; lean_object* v_roundBudget_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2436_; 
lean_inc_ref(v_aig_2012_);
v___x_2386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2386_, 0, v_aig_2012_);
lean_ctor_set(v___x_2386_, 1, v_cache_2020_);
lean_ctor_set(v___x_2386_, 2, v___y_2368_);
v___x_2387_ = lean_st_ref_take(v___y_2373_);
v_theoryState_2388_ = lean_ctor_get(v___x_2387_, 3);
v_satExpr_2389_ = lean_ctor_get(v___x_2387_, 0);
v_hypQueue_2390_ = lean_ctor_get(v___x_2387_, 1);
v_usedHyps_2391_ = lean_ctor_get(v___x_2387_, 2);
v_didChange_2392_ = lean_ctor_get_uint8(v___x_2387_, sizeof(void*)*6);
v_solverTimeBudgetMs_2393_ = lean_ctor_get(v___x_2387_, 4);
v_roundBudget_2394_ = lean_ctor_get(v___x_2387_, 5);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2396_ = v___x_2387_;
v_isShared_2397_ = v_isSharedCheck_2436_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_roundBudget_2394_);
lean_inc(v_solverTimeBudgetMs_2393_);
lean_inc(v_theoryState_2388_);
lean_inc(v_usedHyps_2391_);
lean_inc(v_hypQueue_2390_);
lean_inc(v_satExpr_2389_);
lean_dec(v___x_2387_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2436_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_funState_2398_; lean_object* v_preprocessCaches_2399_; lean_object* v_satSolver_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2434_; 
v_funState_2398_ = lean_ctor_get(v_theoryState_2388_, 0);
v_preprocessCaches_2399_ = lean_ctor_get(v_theoryState_2388_, 2);
v_satSolver_2400_ = lean_ctor_get(v_theoryState_2388_, 3);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_theoryState_2388_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; 
v_unused_2435_ = lean_ctor_get(v_theoryState_2388_, 1);
lean_dec(v_unused_2435_);
v___x_2402_ = v_theoryState_2388_;
v_isShared_2403_ = v_isSharedCheck_2434_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_satSolver_2400_);
lean_inc(v_preprocessCaches_2399_);
lean_inc(v_funState_2398_);
lean_dec(v_theoryState_2388_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2434_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 1, v___x_2386_);
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_funState_2398_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_preprocessCaches_2399_);
lean_ctor_set(v_reuseFailAlloc_2433_, 3, v_satSolver_2400_);
v___x_2405_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 3, v___x_2405_);
v___x_2407_ = v___x_2396_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_satExpr_2389_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_hypQueue_2390_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_usedHyps_2391_);
lean_ctor_set(v_reuseFailAlloc_2432_, 3, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_solverTimeBudgetMs_2393_);
lean_ctor_set(v_reuseFailAlloc_2432_, 5, v_roundBudget_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2432_, sizeof(void*)*6, v_didChange_2392_);
v___x_2407_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_st_ref_put(v___y_2373_, v___x_2407_);
v___x_2409_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_2371_, v___y_2369_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v___x_2410_; 
lean_dec_ref_known(v___x_2409_, 1);
v___x_2410_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_2373_);
if (lean_obj_tag(v___x_2410_) == 0)
{
uint8_t v_invert_2411_; 
v_invert_2411_ = lean_ctor_get_uint8(v_ref_2021_, sizeof(void*)*1);
if (v_invert_2411_ == 0)
{
lean_object* v_a_2412_; lean_object* v_gate_2413_; 
v_a_2412_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2410_, 1);
v_gate_2413_ = lean_ctor_get(v_ref_2021_, 0);
v___y_2324_ = v___y_2377_;
v___y_2325_ = v___y_2378_;
v___y_2326_ = v___y_2379_;
v___y_2327_ = v___y_2374_;
v___y_2328_ = v___y_2382_;
v___y_2329_ = v___y_2370_;
v___y_2330_ = v___y_2383_;
v___y_2331_ = v___y_2384_;
v___y_2332_ = v___y_2380_;
v___y_2333_ = v_gate_2413_;
v___y_2334_ = v___y_2381_;
v___y_2335_ = v___y_2372_;
v___y_2336_ = v_a_2412_;
v___y_2337_ = v___y_2385_;
v___y_2338_ = v___y_2375_;
v___y_2339_ = v___y_2373_;
v___y_2340_ = v___y_2376_;
v___y_2341_ = v_hasTrace_2016_;
goto v___jp_2323_;
}
else
{
lean_object* v_a_2414_; lean_object* v_gate_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2410_, 1);
v_gate_2415_ = lean_ctor_get(v_ref_2021_, 0);
v___y_2324_ = v___y_2377_;
v___y_2325_ = v___y_2378_;
v___y_2326_ = v___y_2379_;
v___y_2327_ = v___y_2374_;
v___y_2328_ = v___y_2382_;
v___y_2329_ = v___y_2370_;
v___y_2330_ = v___y_2383_;
v___y_2331_ = v___y_2384_;
v___y_2332_ = v___y_2380_;
v___y_2333_ = v_gate_2415_;
v___y_2334_ = v___y_2381_;
v___y_2335_ = v___y_2372_;
v___y_2336_ = v_a_2414_;
v___y_2337_ = v___y_2385_;
v___y_2338_ = v___y_2375_;
v___y_2339_ = v___y_2373_;
v___y_2340_ = v___y_2376_;
v___y_2341_ = v___x_2022_;
goto v___jp_2323_;
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v___y_2370_);
lean_dec_ref(v___f_2018_);
lean_dec_ref(v___x_2017_);
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_aig_2012_);
lean_dec_ref(v_tacticContext_2010_);
v_a_2416_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2410_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2410_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v___y_2370_);
lean_dec_ref(v___f_2018_);
lean_dec_ref(v___x_2017_);
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_aig_2012_);
lean_dec_ref(v_tacticContext_2010_);
v_a_2424_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2409_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2409_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
}
}
v___jp_2437_:
{
if (lean_obj_tag(v___y_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_toCold_2456_; lean_object* v_options_2457_; uint8_t v_hasTrace_2458_; 
v_a_2455_ = lean_ctor_get(v___y_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___y_2454_, 1);
v_toCold_2456_ = lean_ctor_get(v___y_2439_, 0);
v_options_2457_ = lean_ctor_get(v_toCold_2456_, 2);
v_hasTrace_2458_ = lean_ctor_get_uint8(v_options_2457_, sizeof(void*)*1);
if (v_hasTrace_2458_ == 0)
{
lean_object* v_cnf_2459_; 
lean_dec(v_cls_2023_);
v_cnf_2459_ = lean_ctor_get(v_a_2455_, 0);
lean_inc_ref(v_cnf_2459_);
v___y_2368_ = v_a_2455_;
v___y_2369_ = v_cnf_2459_;
v___y_2370_ = v___y_2445_;
v___y_2371_ = v___y_2452_;
v___y_2372_ = v___y_2453_;
v___y_2373_ = v___y_2443_;
v___y_2374_ = v___y_2441_;
v___y_2375_ = v___y_2447_;
v___y_2376_ = v___y_2446_;
v___y_2377_ = v___y_2442_;
v___y_2378_ = v___y_2440_;
v___y_2379_ = v___y_2449_;
v___y_2380_ = v___y_2450_;
v___y_2381_ = v___y_2451_;
v___y_2382_ = v___y_2438_;
v___y_2383_ = v___y_2444_;
v___y_2384_ = v___y_2439_;
v___y_2385_ = v___y_2448_;
goto v___jp_2367_;
}
else
{
lean_object* v_cnf_2460_; lean_object* v_inheritedTraceOptions_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v_cnf_2460_ = lean_ctor_get(v_a_2455_, 0);
lean_inc_ref(v_cnf_2460_);
v_inheritedTraceOptions_2461_ = lean_ctor_get(v_toCold_2456_, 11);
v___x_2462_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v_cls_2023_);
v___x_2463_ = l_Lean_Name_append(v___x_2462_, v_cls_2023_);
v___x_2464_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2461_, v_options_2457_, v___x_2463_);
lean_dec(v___x_2463_);
if (v___x_2464_ == 0)
{
lean_dec(v_cls_2023_);
v___y_2368_ = v_a_2455_;
v___y_2369_ = v_cnf_2460_;
v___y_2370_ = v___y_2445_;
v___y_2371_ = v___y_2452_;
v___y_2372_ = v___y_2453_;
v___y_2373_ = v___y_2443_;
v___y_2374_ = v___y_2441_;
v___y_2375_ = v___y_2447_;
v___y_2376_ = v___y_2446_;
v___y_2377_ = v___y_2442_;
v___y_2378_ = v___y_2440_;
v___y_2379_ = v___y_2449_;
v___y_2380_ = v___y_2450_;
v___y_2381_ = v___y_2451_;
v___y_2382_ = v___y_2438_;
v___y_2383_ = v___y_2444_;
v___y_2384_ = v___y_2439_;
v___y_2385_ = v___y_2448_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2465_ = lean_array_get_size(v_cnf_2460_);
v___x_2466_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_2467_ = l_Nat_reprFast(v___x_2465_);
v___x_2468_ = lean_string_append(v___x_2466_, v___x_2467_);
lean_dec_ref(v___x_2467_);
v___x_2469_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_2470_ = lean_string_append(v___x_2468_, v___x_2469_);
v___x_2471_ = lean_nat_sub(v___x_2465_, v___y_2452_);
v___x_2472_ = l_Nat_reprFast(v___x_2471_);
v___x_2473_ = lean_string_append(v___x_2470_, v___x_2472_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_2475_ = lean_string_append(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
v___x_2477_ = l_Lean_MessageData_ofFormat(v___x_2476_);
v___x_2478_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_2023_, v___x_2477_, v___y_2438_, v___y_2444_, v___y_2439_, v___y_2448_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_dec_ref_known(v___x_2478_, 1);
v___y_2368_ = v_a_2455_;
v___y_2369_ = v_cnf_2460_;
v___y_2370_ = v___y_2445_;
v___y_2371_ = v___y_2452_;
v___y_2372_ = v___y_2453_;
v___y_2373_ = v___y_2443_;
v___y_2374_ = v___y_2441_;
v___y_2375_ = v___y_2447_;
v___y_2376_ = v___y_2446_;
v___y_2377_ = v___y_2442_;
v___y_2378_ = v___y_2440_;
v___y_2379_ = v___y_2449_;
v___y_2380_ = v___y_2450_;
v___y_2381_ = v___y_2451_;
v___y_2382_ = v___y_2438_;
v___y_2383_ = v___y_2444_;
v___y_2384_ = v___y_2439_;
v___y_2385_ = v___y_2448_;
goto v___jp_2367_;
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v_cnf_2460_);
lean_dec(v_a_2455_);
lean_dec(v___y_2452_);
lean_dec(v___y_2445_);
lean_dec_ref(v_cache_2020_);
lean_dec_ref(v___f_2018_);
lean_dec_ref(v___x_2017_);
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_aig_2012_);
lean_dec_ref(v_tacticContext_2010_);
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
return v___x_2484_;
}
}
}
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v___y_2452_);
lean_dec(v___y_2445_);
lean_dec(v_cls_2023_);
lean_dec_ref(v_cache_2020_);
lean_dec_ref(v___f_2018_);
lean_dec_ref(v___x_2017_);
lean_dec_ref(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v___x_2013_);
lean_dec_ref(v_aig_2012_);
lean_dec_ref(v_tacticContext_2010_);
v_a_2487_ = lean_ctor_get(v___y_2454_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___y_2454_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___y_2454_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___y_2454_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
v___jp_2495_:
{
lean_object* v___x_2517_; double v___x_2518_; double v___x_2519_; double v___x_2520_; double v___x_2521_; double v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2517_ = lean_io_mono_nanos_now();
v___x_2518_ = lean_float_of_nat(v___y_2506_);
v___x_2519_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2520_ = lean_float_div(v___x_2518_, v___x_2519_);
v___x_2521_ = lean_float_of_nat(v___x_2517_);
v___x_2522_ = lean_float_div(v___x_2521_, v___x_2519_);
v___x_2523_ = lean_box_float(v___x_2520_);
v___x_2524_ = lean_box_float(v___x_2522_);
v___x_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_a_2516_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
lean_inc_ref(v___x_2017_);
lean_inc(v___y_2505_);
v___x_2527_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_2505_, v_hasTrace_2016_, v___x_2017_, v___y_2499_, v___y_2502_, v___y_2507_, v___f_2024_, v___x_2526_, v___y_2515_, v___y_2503_, v___y_2500_, v___y_2509_, v___y_2508_, v___y_2501_, v___y_2498_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2496_, v___y_2504_, v___y_2497_, v___y_2510_);
v___y_2438_ = v___y_2496_;
v___y_2439_ = v___y_2497_;
v___y_2440_ = v___y_2498_;
v___y_2441_ = v___y_2500_;
v___y_2442_ = v___y_2501_;
v___y_2443_ = v___y_2503_;
v___y_2444_ = v___y_2504_;
v___y_2445_ = v___y_2505_;
v___y_2446_ = v___y_2508_;
v___y_2447_ = v___y_2509_;
v___y_2448_ = v___y_2510_;
v___y_2449_ = v___y_2511_;
v___y_2450_ = v___y_2512_;
v___y_2451_ = v___y_2513_;
v___y_2452_ = v___y_2514_;
v___y_2453_ = v___y_2515_;
v___y_2454_ = v___x_2527_;
goto v___jp_2437_;
}
v___jp_2528_:
{
lean_object* v___x_2550_; double v___x_2551_; double v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2550_ = lean_io_get_num_heartbeats();
v___x_2551_ = lean_float_of_nat(v___y_2543_);
v___x_2552_ = lean_float_of_nat(v___x_2550_);
v___x_2553_ = lean_box_float(v___x_2551_);
v___x_2554_ = lean_box_float(v___x_2552_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v_a_2549_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
lean_inc_ref(v___x_2017_);
lean_inc(v___y_2538_);
v___x_2557_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_2538_, v_hasTrace_2016_, v___x_2017_, v___y_2532_, v___y_2535_, v___y_2539_, v___f_2024_, v___x_2556_, v___y_2548_, v___y_2536_, v___y_2533_, v___y_2541_, v___y_2540_, v___y_2534_, v___y_2531_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2529_, v___y_2537_, v___y_2530_, v___y_2542_);
v___y_2438_ = v___y_2529_;
v___y_2439_ = v___y_2530_;
v___y_2440_ = v___y_2531_;
v___y_2441_ = v___y_2533_;
v___y_2442_ = v___y_2534_;
v___y_2443_ = v___y_2536_;
v___y_2444_ = v___y_2537_;
v___y_2445_ = v___y_2538_;
v___y_2446_ = v___y_2540_;
v___y_2447_ = v___y_2541_;
v___y_2448_ = v___y_2542_;
v___y_2449_ = v___y_2544_;
v___y_2450_ = v___y_2545_;
v___y_2451_ = v___y_2546_;
v___y_2452_ = v___y_2547_;
v___y_2453_ = v___y_2548_;
v___y_2454_ = v___x_2557_;
goto v___jp_2437_;
}
v___jp_2558_:
{
lean_object* v___x_2579_; lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2633_; 
v___x_2579_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_2571_);
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2633_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2633_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
uint8_t v___x_2584_; 
v___x_2584_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_2562_, v___x_2019_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_io_mono_nanos_now();
v___x_2586_ = l_IO_lazyPure___redArg(v___y_2576_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_del_object(v___x_2582_);
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 1);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
v___y_2496_ = v___y_2559_;
v___y_2497_ = v___y_2560_;
v___y_2498_ = v___y_2561_;
v___y_2499_ = v___y_2562_;
v___y_2500_ = v___y_2563_;
v___y_2501_ = v___y_2564_;
v___y_2502_ = v___y_2565_;
v___y_2503_ = v___y_2566_;
v___y_2504_ = v___y_2567_;
v___y_2505_ = v___y_2568_;
v___y_2506_ = v___x_2585_;
v___y_2507_ = v_a_2580_;
v___y_2508_ = v___y_2569_;
v___y_2509_ = v___y_2570_;
v___y_2510_ = v___y_2571_;
v___y_2511_ = v___y_2573_;
v___y_2512_ = v___y_2574_;
v___y_2513_ = v___y_2575_;
v___y_2514_ = v___y_2577_;
v___y_2515_ = v___y_2578_;
v_a_2516_ = v___x_2592_;
goto v___jp_2495_;
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2608_; 
v_a_2595_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2597_ = v___x_2586_;
v_isShared_2598_ = v_isSharedCheck_2608_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2586_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2608_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2599_ = lean_io_error_to_string(v_a_2595_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 3);
lean_ctor_set(v___x_2597_, 0, v___x_2599_);
v___x_2601_ = v___x_2597_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2602_ = l_Lean_MessageData_ofFormat(v___x_2601_);
lean_inc(v___y_2572_);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___y_2572_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2603_);
v___x_2605_ = v___x_2582_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
v___y_2496_ = v___y_2559_;
v___y_2497_ = v___y_2560_;
v___y_2498_ = v___y_2561_;
v___y_2499_ = v___y_2562_;
v___y_2500_ = v___y_2563_;
v___y_2501_ = v___y_2564_;
v___y_2502_ = v___y_2565_;
v___y_2503_ = v___y_2566_;
v___y_2504_ = v___y_2567_;
v___y_2505_ = v___y_2568_;
v___y_2506_ = v___x_2585_;
v___y_2507_ = v_a_2580_;
v___y_2508_ = v___y_2569_;
v___y_2509_ = v___y_2570_;
v___y_2510_ = v___y_2571_;
v___y_2511_ = v___y_2573_;
v___y_2512_ = v___y_2574_;
v___y_2513_ = v___y_2575_;
v___y_2514_ = v___y_2577_;
v___y_2515_ = v___y_2578_;
v_a_2516_ = v___x_2605_;
goto v___jp_2495_;
}
}
}
}
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_io_get_num_heartbeats();
v___x_2610_ = l_IO_lazyPure___redArg(v___y_2576_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_del_object(v___x_2582_);
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set_tag(v___x_2613_, 1);
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
v___y_2529_ = v___y_2559_;
v___y_2530_ = v___y_2560_;
v___y_2531_ = v___y_2561_;
v___y_2532_ = v___y_2562_;
v___y_2533_ = v___y_2563_;
v___y_2534_ = v___y_2564_;
v___y_2535_ = v___y_2565_;
v___y_2536_ = v___y_2566_;
v___y_2537_ = v___y_2567_;
v___y_2538_ = v___y_2568_;
v___y_2539_ = v_a_2580_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2570_;
v___y_2542_ = v___y_2571_;
v___y_2543_ = v___x_2609_;
v___y_2544_ = v___y_2573_;
v___y_2545_ = v___y_2574_;
v___y_2546_ = v___y_2575_;
v___y_2547_ = v___y_2577_;
v___y_2548_ = v___y_2578_;
v_a_2549_ = v___x_2616_;
goto v___jp_2528_;
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2632_; 
v_a_2619_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2621_ = v___x_2610_;
v_isShared_2622_ = v_isSharedCheck_2632_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2610_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2632_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2623_ = lean_io_error_to_string(v_a_2619_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 3);
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2626_ = l_Lean_MessageData_ofFormat(v___x_2625_);
lean_inc(v___y_2572_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___y_2572_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2627_);
v___x_2629_ = v___x_2582_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
v___y_2529_ = v___y_2559_;
v___y_2530_ = v___y_2560_;
v___y_2531_ = v___y_2561_;
v___y_2532_ = v___y_2562_;
v___y_2533_ = v___y_2563_;
v___y_2534_ = v___y_2564_;
v___y_2535_ = v___y_2565_;
v___y_2536_ = v___y_2566_;
v___y_2537_ = v___y_2567_;
v___y_2538_ = v___y_2568_;
v___y_2539_ = v_a_2580_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2570_;
v___y_2542_ = v___y_2571_;
v___y_2543_ = v___x_2609_;
v___y_2544_ = v___y_2573_;
v___y_2545_ = v___y_2574_;
v___y_2546_ = v___y_2575_;
v___y_2547_ = v___y_2577_;
v___y_2548_ = v___y_2578_;
v_a_2549_ = v___x_2629_;
goto v___jp_2528_;
}
}
}
}
}
}
}
v___jp_2634_:
{
lean_object* v_toCold_2649_; lean_object* v_options_2650_; lean_object* v_cnf_2651_; lean_object* v_ref_2652_; lean_object* v_inheritedTraceOptions_2653_; uint8_t v_hasTrace_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___f_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v_toCold_2649_ = lean_ctor_get(v___y_2647_, 0);
v_options_2650_ = lean_ctor_get(v_toCold_2649_, 2);
v_cnf_2651_ = lean_ctor_get(v_cnfCache_2025_, 0);
v_ref_2652_ = lean_ctor_get(v___y_2647_, 2);
v_inheritedTraceOptions_2653_ = lean_ctor_get(v_toCold_2649_, 11);
v_hasTrace_2654_ = lean_ctor_get_uint8(v_options_2650_, sizeof(void*)*1);
v___x_2655_ = lean_array_get_size(v_cnf_2651_);
v___x_2656_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_2657_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig_2012_, v_cnfCache_2025_);
v___f_2658_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2658_, 0, v___x_2026_);
lean_closure_set(v___f_2658_, 1, v___x_2656_);
lean_closure_set(v___f_2658_, 2, v_result_2027_);
lean_closure_set(v___f_2658_, 3, v___x_2657_);
v___x_2659_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13));
v___x_2660_ = l_Lean_Name_mkStr3(v___x_2028_, v___x_2029_, v___x_2659_);
if (v_hasTrace_2654_ == 0)
{
lean_object* v___x_2661_; 
lean_dec_ref(v___f_2024_);
v___x_2661_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_2658_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
v___y_2438_ = v___y_2645_;
v___y_2439_ = v___y_2647_;
v___y_2440_ = v___y_2641_;
v___y_2441_ = v___y_2637_;
v___y_2442_ = v___y_2640_;
v___y_2443_ = v___y_2636_;
v___y_2444_ = v___y_2646_;
v___y_2445_ = v___x_2660_;
v___y_2446_ = v___y_2639_;
v___y_2447_ = v___y_2638_;
v___y_2448_ = v___y_2648_;
v___y_2449_ = v___y_2642_;
v___y_2450_ = v___y_2643_;
v___y_2451_ = v___y_2644_;
v___y_2452_ = v___x_2655_;
v___y_2453_ = v___y_2635_;
v___y_2454_ = v___x_2661_;
goto v___jp_2437_;
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2662_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___x_2660_);
v___x_2663_ = l_Lean_Name_append(v___x_2662_, v___x_2660_);
v___x_2664_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2653_, v_options_2650_, v___x_2663_);
lean_dec(v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = l_Lean_trace_profiler;
v___x_2666_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_2650_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec_ref(v___f_2024_);
v___x_2667_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_2658_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
v___y_2438_ = v___y_2645_;
v___y_2439_ = v___y_2647_;
v___y_2440_ = v___y_2641_;
v___y_2441_ = v___y_2637_;
v___y_2442_ = v___y_2640_;
v___y_2443_ = v___y_2636_;
v___y_2444_ = v___y_2646_;
v___y_2445_ = v___x_2660_;
v___y_2446_ = v___y_2639_;
v___y_2447_ = v___y_2638_;
v___y_2448_ = v___y_2648_;
v___y_2449_ = v___y_2642_;
v___y_2450_ = v___y_2643_;
v___y_2451_ = v___y_2644_;
v___y_2452_ = v___x_2655_;
v___y_2453_ = v___y_2635_;
v___y_2454_ = v___x_2667_;
goto v___jp_2437_;
}
else
{
v___y_2559_ = v___y_2645_;
v___y_2560_ = v___y_2647_;
v___y_2561_ = v___y_2641_;
v___y_2562_ = v_options_2650_;
v___y_2563_ = v___y_2637_;
v___y_2564_ = v___y_2640_;
v___y_2565_ = v___x_2664_;
v___y_2566_ = v___y_2636_;
v___y_2567_ = v___y_2646_;
v___y_2568_ = v___x_2660_;
v___y_2569_ = v___y_2639_;
v___y_2570_ = v___y_2638_;
v___y_2571_ = v___y_2648_;
v___y_2572_ = v_ref_2652_;
v___y_2573_ = v___y_2642_;
v___y_2574_ = v___y_2643_;
v___y_2575_ = v___y_2644_;
v___y_2576_ = v___f_2658_;
v___y_2577_ = v___x_2655_;
v___y_2578_ = v___y_2635_;
goto v___jp_2558_;
}
}
else
{
v___y_2559_ = v___y_2645_;
v___y_2560_ = v___y_2647_;
v___y_2561_ = v___y_2641_;
v___y_2562_ = v_options_2650_;
v___y_2563_ = v___y_2637_;
v___y_2564_ = v___y_2640_;
v___y_2565_ = v___x_2664_;
v___y_2566_ = v___y_2636_;
v___y_2567_ = v___y_2646_;
v___y_2568_ = v___x_2660_;
v___y_2569_ = v___y_2639_;
v___y_2570_ = v___y_2638_;
v___y_2571_ = v___y_2648_;
v___y_2572_ = v_ref_2652_;
v___y_2573_ = v___y_2642_;
v___y_2574_ = v___y_2643_;
v___y_2575_ = v___y_2644_;
v___y_2576_ = v___f_2658_;
v___y_2577_ = v___x_2655_;
v___y_2578_ = v___y_2635_;
goto v___jp_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___boxed(lean_object** _args){
lean_object* v_tacticContext_2686_ = _args[0];
lean_object* v___x_2687_ = _args[1];
lean_object* v_aig_2688_ = _args[2];
lean_object* v___x_2689_ = _args[3];
lean_object* v___x_2690_ = _args[4];
lean_object* v___x_2691_ = _args[5];
lean_object* v_hasTrace_2692_ = _args[6];
lean_object* v___x_2693_ = _args[7];
lean_object* v___f_2694_ = _args[8];
lean_object* v___x_2695_ = _args[9];
lean_object* v_cache_2696_ = _args[10];
lean_object* v_ref_2697_ = _args[11];
lean_object* v___x_2698_ = _args[12];
lean_object* v_cls_2699_ = _args[13];
lean_object* v___f_2700_ = _args[14];
lean_object* v_cnfCache_2701_ = _args[15];
lean_object* v___x_2702_ = _args[16];
lean_object* v_result_2703_ = _args[17];
lean_object* v___x_2704_ = _args[18];
lean_object* v___x_2705_ = _args[19];
lean_object* v_____r_2706_ = _args[20];
lean_object* v___y_2707_ = _args[21];
lean_object* v___y_2708_ = _args[22];
lean_object* v___y_2709_ = _args[23];
lean_object* v___y_2710_ = _args[24];
lean_object* v___y_2711_ = _args[25];
lean_object* v___y_2712_ = _args[26];
lean_object* v___y_2713_ = _args[27];
lean_object* v___y_2714_ = _args[28];
lean_object* v___y_2715_ = _args[29];
lean_object* v___y_2716_ = _args[30];
lean_object* v___y_2717_ = _args[31];
lean_object* v___y_2718_ = _args[32];
lean_object* v___y_2719_ = _args[33];
lean_object* v___y_2720_ = _args[34];
lean_object* v___y_2721_ = _args[35];
_start:
{
uint8_t v_hasTrace_boxed_2722_; uint8_t v___x_1192835__boxed_2723_; lean_object* v_res_2724_; 
v_hasTrace_boxed_2722_ = lean_unbox(v_hasTrace_2692_);
v___x_1192835__boxed_2723_ = lean_unbox(v___x_2698_);
v_res_2724_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v_tacticContext_2686_, v___x_2687_, v_aig_2688_, v___x_2689_, v___x_2690_, v___x_2691_, v_hasTrace_boxed_2722_, v___x_2693_, v___f_2694_, v___x_2695_, v_cache_2696_, v_ref_2697_, v___x_1192835__boxed_2723_, v_cls_2699_, v___f_2700_, v_cnfCache_2701_, v___x_2702_, v_result_2703_, v___x_2704_, v___x_2705_, v_____r_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec_ref(v_ref_2697_);
lean_dec_ref(v___x_2695_);
lean_dec(v___x_2687_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(lean_object* v_tacticContext_2725_, lean_object* v___x_2726_, lean_object* v_aig_2727_, lean_object* v___x_2728_, lean_object* v___x_2729_, lean_object* v___x_2730_, uint8_t v___x_2731_, lean_object* v___x_2732_, lean_object* v___f_2733_, lean_object* v___x_2734_, lean_object* v_cache_2735_, lean_object* v_ref_2736_, lean_object* v_cls_2737_, lean_object* v___f_2738_, lean_object* v_cnfCache_2739_, lean_object* v___x_2740_, lean_object* v_result_2741_, lean_object* v___x_2742_, lean_object* v___x_2743_, lean_object* v_____r_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v_a_2938_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; uint8_t v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v_a_2970_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; uint8_t v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; uint8_t v___y_3055_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; uint8_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v_a_3231_; uint8_t v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v_a_3264_; uint8_t v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v_config_3383_; uint8_t v_graphviz_3384_; 
v_config_3383_ = lean_ctor_get(v_tacticContext_2725_, 5);
v_graphviz_3384_ = lean_ctor_get_uint8(v_config_3383_, sizeof(void*)*3 + 8);
if (v_graphviz_3384_ == 0)
{
v___y_3350_ = v___y_2745_;
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
goto v___jp_3349_;
}
else
{
lean_object* v_ref_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_ref_3385_ = lean_ctor_get(v___y_2757_, 2);
v___x_3386_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
lean_inc_ref(v_result_2741_);
v___x_3387_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v_result_2741_);
v___x_3388_ = l_IO_FS_writeFile(v___x_3386_, v___x_3387_);
lean_dec_ref(v___x_3387_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_dec_ref_known(v___x_3388_, 1);
v___y_3350_ = v___y_2745_;
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
goto v___jp_3349_;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v___x_2743_);
lean_dec_ref(v___x_2742_);
lean_dec_ref(v_result_2741_);
lean_dec_ref(v___x_2740_);
lean_dec_ref(v_cnfCache_2739_);
lean_dec_ref(v___f_2738_);
lean_dec(v_cls_2737_);
lean_dec_ref(v_cache_2735_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___x_2732_);
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_aig_2727_);
lean_dec_ref(v_tacticContext_2725_);
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3400_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3400_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3393_ = lean_io_error_to_string(v_a_3389_);
v___x_3394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
v___x_3395_ = l_Lean_MessageData_ofFormat(v___x_3394_);
lean_inc(v_ref_3385_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v_ref_3385_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3396_);
v___x_3398_ = v___x_3391_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
v___jp_2760_:
{
lean_object* v___x_2775_; 
v___x_2775_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___x_2726_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2765_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2787_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2787_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2787_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2782_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2727_, v_a_2776_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec(v_a_2776_);
v___x_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2783_);
v___x_2785_ = v___x_2780_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2776_);
lean_dec_ref(v_aig_2727_);
v_a_2788_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2777_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2777_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_aig_2727_);
v_a_2796_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2775_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2775_);
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
v___jp_2804_:
{
if (lean_obj_tag(v___y_2820_) == 0)
{
lean_object* v_a_2821_; uint8_t v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___y_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___y_2820_, 1);
v___x_2822_ = lean_unbox(v_a_2821_);
lean_dec(v_a_2821_);
switch(v___x_2822_)
{
case 0:
{
lean_object* v_toCold_2823_; lean_object* v_options_2824_; uint8_t v_hasTrace_2825_; 
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_tacticContext_2725_);
v_toCold_2823_ = lean_ctor_get(v___y_2807_, 0);
v_options_2824_ = lean_ctor_get(v_toCold_2823_, 2);
v_hasTrace_2825_ = lean_ctor_get_uint8(v_options_2824_, sizeof(void*)*1);
if (v_hasTrace_2825_ == 0)
{
lean_dec(v___y_2817_);
v___y_2761_ = v___y_2805_;
v___y_2762_ = v___y_2813_;
v___y_2763_ = v___y_2818_;
v___y_2764_ = v___y_2810_;
v___y_2765_ = v___y_2806_;
v___y_2766_ = v___y_2811_;
v___y_2767_ = v___y_2815_;
v___y_2768_ = v___y_2819_;
v___y_2769_ = v___y_2816_;
v___y_2770_ = v___y_2814_;
v___y_2771_ = v___y_2809_;
v___y_2772_ = v___y_2812_;
v___y_2773_ = v___y_2807_;
v___y_2774_ = v___y_2808_;
goto v___jp_2760_;
}
else
{
lean_object* v_inheritedTraceOptions_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v_inheritedTraceOptions_2826_ = lean_ctor_get(v_toCold_2823_, 11);
v___x_2827_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2817_);
v___x_2828_ = l_Lean_Name_append(v___x_2827_, v___y_2817_);
v___x_2829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2826_, v_options_2824_, v___x_2828_);
lean_dec(v___x_2828_);
if (v___x_2829_ == 0)
{
lean_dec(v___y_2817_);
v___y_2761_ = v___y_2805_;
v___y_2762_ = v___y_2813_;
v___y_2763_ = v___y_2818_;
v___y_2764_ = v___y_2810_;
v___y_2765_ = v___y_2806_;
v___y_2766_ = v___y_2811_;
v___y_2767_ = v___y_2815_;
v___y_2768_ = v___y_2819_;
v___y_2769_ = v___y_2816_;
v___y_2770_ = v___y_2814_;
v___y_2771_ = v___y_2809_;
v___y_2772_ = v___y_2812_;
v___y_2773_ = v___y_2807_;
v___y_2774_ = v___y_2808_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
v___x_2831_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_2817_, v___x_2830_, v___y_2809_, v___y_2812_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_dec_ref_known(v___x_2831_, 1);
v___y_2761_ = v___y_2805_;
v___y_2762_ = v___y_2813_;
v___y_2763_ = v___y_2818_;
v___y_2764_ = v___y_2810_;
v___y_2765_ = v___y_2806_;
v___y_2766_ = v___y_2811_;
v___y_2767_ = v___y_2815_;
v___y_2768_ = v___y_2819_;
v___y_2769_ = v___y_2816_;
v___y_2770_ = v___y_2814_;
v___y_2771_ = v___y_2809_;
v___y_2772_ = v___y_2812_;
v___y_2773_ = v___y_2807_;
v___y_2774_ = v___y_2808_;
goto v___jp_2760_;
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec_ref(v_aig_2727_);
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_2840_; lean_object* v_satExpr_2841_; lean_object* v_hypQueue_2842_; lean_object* v_usedHyps_2843_; uint8_t v_didChange_2844_; lean_object* v_theoryState_2845_; lean_object* v_solverTimeBudgetMs_2846_; lean_object* v_roundBudget_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2908_; 
lean_dec(v___y_2817_);
lean_dec_ref(v_aig_2727_);
v___x_2840_ = lean_st_ref_take(v___y_2813_);
v_satExpr_2841_ = lean_ctor_get(v___x_2840_, 0);
v_hypQueue_2842_ = lean_ctor_get(v___x_2840_, 1);
v_usedHyps_2843_ = lean_ctor_get(v___x_2840_, 2);
v_didChange_2844_ = lean_ctor_get_uint8(v___x_2840_, sizeof(void*)*6);
v_theoryState_2845_ = lean_ctor_get(v___x_2840_, 3);
v_solverTimeBudgetMs_2846_ = lean_ctor_get(v___x_2840_, 4);
v_roundBudget_2847_ = lean_ctor_get(v___x_2840_, 5);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2849_ = v___x_2840_;
v_isShared_2850_ = v_isSharedCheck_2908_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_roundBudget_2847_);
lean_inc(v_solverTimeBudgetMs_2846_);
lean_inc(v_theoryState_2845_);
lean_inc(v_usedHyps_2843_);
lean_inc(v_hypQueue_2842_);
lean_inc(v_satExpr_2841_);
lean_dec(v___x_2840_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2908_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v_satSolver_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2904_; 
v___x_2851_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_2852_ = lean_ctor_get(v_theoryState_2845_, 3);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_theoryState_2845_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; lean_object* v_unused_2906_; lean_object* v_unused_2907_; 
v_unused_2905_ = lean_ctor_get(v_theoryState_2845_, 2);
lean_dec(v_unused_2905_);
v_unused_2906_ = lean_ctor_get(v_theoryState_2845_, 1);
lean_dec(v_unused_2906_);
v_unused_2907_ = lean_ctor_get(v_theoryState_2845_, 0);
lean_dec(v_unused_2907_);
v___x_2854_ = v_theoryState_2845_;
v_isShared_2855_ = v_isSharedCheck_2904_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_satSolver_2852_);
lean_dec(v_theoryState_2845_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2904_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_mk_array(v___x_2728_, v___x_2856_);
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2729_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 2, v___x_2851_);
lean_ctor_set(v___x_2854_, 1, v___x_2730_);
lean_ctor_set(v___x_2854_, 0, v___x_2858_);
v___x_2860_ = v___x_2854_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_satSolver_2852_);
v___x_2860_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2862_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 3, v___x_2860_);
v___x_2862_ = v___x_2849_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_satExpr_2841_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_hypQueue_2842_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_usedHyps_2843_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2902_, 4, v_solverTimeBudgetMs_2846_);
lean_ctor_set(v_reuseFailAlloc_2902_, 5, v_roundBudget_2847_);
lean_ctor_set_uint8(v_reuseFailAlloc_2902_, sizeof(void*)*6, v_didChange_2844_);
v___x_2862_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_st_ref_put(v___y_2813_, v___x_2862_);
v___x_2864_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_2805_, v___y_2813_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v_goal_2866_; lean_object* v___x_2867_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v_goal_2866_ = lean_ctor_get(v___y_2805_, 0);
lean_inc(v_goal_2866_);
v___x_2867_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_tacticContext_2725_, v_goal_2866_, v_a_2865_, v___y_2818_, v___y_2810_, v___y_2806_, v___y_2811_, v___y_2815_, v___y_2819_, v___y_2816_, v___y_2814_, v___y_2809_, v___y_2812_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2885_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2885_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2885_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
if (lean_obj_tag(v_a_2868_) == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec_ref_known(v_a_2868_, 1);
lean_del_object(v___x_2870_);
v___x_2872_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_2873_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_2872_, v___y_2809_, v___y_2812_, v___y_2807_, v___y_2808_);
return v___x_2873_;
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2884_; 
v_a_2874_ = lean_ctor_get(v_a_2868_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2876_ = v_a_2868_;
v_isShared_2877_ = v_isSharedCheck_2884_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v_a_2868_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2884_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2881_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2879_);
v___x_2881_ = v___x_2870_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2867_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2867_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref(v_tacticContext_2725_);
v_a_2894_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2864_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2864_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
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
lean_object* v___x_2909_; 
lean_dec(v___y_2817_);
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_aig_2727_);
lean_dec_ref(v_tacticContext_2725_);
v___x_2909_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_2807_, v___y_2808_);
return v___x_2909_;
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v___y_2817_);
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_aig_2727_);
lean_dec_ref(v_tacticContext_2725_);
v_a_2910_ = lean_ctor_get(v___y_2820_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___y_2820_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___y_2820_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___y_2820_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
v___jp_2918_:
{
lean_object* v___x_2939_; double v___x_2940_; double v___x_2941_; double v___x_2942_; double v___x_2943_; double v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2939_ = lean_io_mono_nanos_now();
v___x_2940_ = lean_float_of_nat(v___y_2935_);
v___x_2941_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2942_ = lean_float_div(v___x_2940_, v___x_2941_);
v___x_2943_ = lean_float_of_nat(v___x_2939_);
v___x_2944_ = lean_float_div(v___x_2943_, v___x_2941_);
v___x_2945_ = lean_box_float(v___x_2942_);
v___x_2946_ = lean_box_float(v___x_2944_);
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2938_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
lean_inc(v___y_2934_);
v___x_2949_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2934_, v___x_2731_, v___x_2732_, v___y_2927_, v___y_2928_, v___y_2926_, v___f_2733_, v___x_2948_, v___y_2919_, v___y_2931_, v___y_2936_, v___y_2924_, v___y_2920_, v___y_2925_, v___y_2932_, v___y_2937_, v___y_2933_, v___y_2930_, v___y_2923_, v___y_2929_, v___y_2921_, v___y_2922_);
v___y_2805_ = v___y_2919_;
v___y_2806_ = v___y_2920_;
v___y_2807_ = v___y_2921_;
v___y_2808_ = v___y_2922_;
v___y_2809_ = v___y_2923_;
v___y_2810_ = v___y_2924_;
v___y_2811_ = v___y_2925_;
v___y_2812_ = v___y_2929_;
v___y_2813_ = v___y_2931_;
v___y_2814_ = v___y_2930_;
v___y_2815_ = v___y_2932_;
v___y_2816_ = v___y_2933_;
v___y_2817_ = v___y_2934_;
v___y_2818_ = v___y_2936_;
v___y_2819_ = v___y_2937_;
v___y_2820_ = v___x_2949_;
goto v___jp_2804_;
}
v___jp_2950_:
{
lean_object* v___x_2971_; double v___x_2972_; double v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2971_ = lean_io_get_num_heartbeats();
v___x_2972_ = lean_float_of_nat(v___y_2957_);
v___x_2973_ = lean_float_of_nat(v___x_2971_);
v___x_2974_ = lean_box_float(v___x_2972_);
v___x_2975_ = lean_box_float(v___x_2973_);
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2974_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v_a_2970_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
lean_inc(v___y_2967_);
v___x_2978_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2967_, v___x_2731_, v___x_2732_, v___y_2960_, v___y_2961_, v___y_2959_, v___f_2733_, v___x_2977_, v___y_2951_, v___y_2964_, v___y_2968_, v___y_2956_, v___y_2952_, v___y_2958_, v___y_2965_, v___y_2969_, v___y_2966_, v___y_2963_, v___y_2955_, v___y_2962_, v___y_2953_, v___y_2954_);
v___y_2805_ = v___y_2951_;
v___y_2806_ = v___y_2952_;
v___y_2807_ = v___y_2953_;
v___y_2808_ = v___y_2954_;
v___y_2809_ = v___y_2955_;
v___y_2810_ = v___y_2956_;
v___y_2811_ = v___y_2958_;
v___y_2812_ = v___y_2962_;
v___y_2813_ = v___y_2964_;
v___y_2814_ = v___y_2963_;
v___y_2815_ = v___y_2965_;
v___y_2816_ = v___y_2966_;
v___y_2817_ = v___y_2967_;
v___y_2818_ = v___y_2968_;
v___y_2819_ = v___y_2969_;
v___y_2820_ = v___x_2978_;
goto v___jp_2804_;
}
v___jp_2979_:
{
lean_object* v___x_2998_; lean_object* v_a_2999_; uint8_t v___x_3000_; 
v___x_2998_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_2984_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_2988_, v___x_2734_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_io_mono_nanos_now();
v___x_3002_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2983_, v___y_2980_, v___y_2991_, v___y_2996_, v___y_2986_, v___y_2981_, v___y_2987_, v___y_2993_, v___y_2997_, v___y_2994_, v___y_2992_, v___y_2985_, v___y_2990_, v___y_2982_, v___y_2984_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set_tag(v___x_3005_, 1);
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
v___y_2919_ = v___y_2980_;
v___y_2920_ = v___y_2981_;
v___y_2921_ = v___y_2982_;
v___y_2922_ = v___y_2984_;
v___y_2923_ = v___y_2985_;
v___y_2924_ = v___y_2986_;
v___y_2925_ = v___y_2987_;
v___y_2926_ = v_a_2999_;
v___y_2927_ = v___y_2988_;
v___y_2928_ = v___y_2989_;
v___y_2929_ = v___y_2990_;
v___y_2930_ = v___y_2992_;
v___y_2931_ = v___y_2991_;
v___y_2932_ = v___y_2993_;
v___y_2933_ = v___y_2994_;
v___y_2934_ = v___y_2995_;
v___y_2935_ = v___x_3001_;
v___y_2936_ = v___y_2996_;
v___y_2937_ = v___y_2997_;
v_a_2938_ = v___x_3008_;
goto v___jp_2918_;
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
v_a_3011_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3002_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3002_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set_tag(v___x_3013_, 0);
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
v___y_2919_ = v___y_2980_;
v___y_2920_ = v___y_2981_;
v___y_2921_ = v___y_2982_;
v___y_2922_ = v___y_2984_;
v___y_2923_ = v___y_2985_;
v___y_2924_ = v___y_2986_;
v___y_2925_ = v___y_2987_;
v___y_2926_ = v_a_2999_;
v___y_2927_ = v___y_2988_;
v___y_2928_ = v___y_2989_;
v___y_2929_ = v___y_2990_;
v___y_2930_ = v___y_2992_;
v___y_2931_ = v___y_2991_;
v___y_2932_ = v___y_2993_;
v___y_2933_ = v___y_2994_;
v___y_2934_ = v___y_2995_;
v___y_2935_ = v___x_3001_;
v___y_2936_ = v___y_2996_;
v___y_2937_ = v___y_2997_;
v_a_2938_ = v___x_3016_;
goto v___jp_2918_;
}
}
}
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_io_get_num_heartbeats();
v___x_3020_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2983_, v___y_2980_, v___y_2991_, v___y_2996_, v___y_2986_, v___y_2981_, v___y_2987_, v___y_2993_, v___y_2997_, v___y_2994_, v___y_2992_, v___y_2985_, v___y_2990_, v___y_2982_, v___y_2984_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set_tag(v___x_3023_, 1);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
v___y_2951_ = v___y_2980_;
v___y_2952_ = v___y_2981_;
v___y_2953_ = v___y_2982_;
v___y_2954_ = v___y_2984_;
v___y_2955_ = v___y_2985_;
v___y_2956_ = v___y_2986_;
v___y_2957_ = v___x_3019_;
v___y_2958_ = v___y_2987_;
v___y_2959_ = v_a_2999_;
v___y_2960_ = v___y_2988_;
v___y_2961_ = v___y_2989_;
v___y_2962_ = v___y_2990_;
v___y_2963_ = v___y_2992_;
v___y_2964_ = v___y_2991_;
v___y_2965_ = v___y_2993_;
v___y_2966_ = v___y_2994_;
v___y_2967_ = v___y_2995_;
v___y_2968_ = v___y_2996_;
v___y_2969_ = v___y_2997_;
v_a_2970_ = v___x_3026_;
goto v___jp_2950_;
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_a_3029_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3020_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3020_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set_tag(v___x_3031_, 0);
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
v___y_2951_ = v___y_2980_;
v___y_2952_ = v___y_2981_;
v___y_2953_ = v___y_2982_;
v___y_2954_ = v___y_2984_;
v___y_2955_ = v___y_2985_;
v___y_2956_ = v___y_2986_;
v___y_2957_ = v___x_3019_;
v___y_2958_ = v___y_2987_;
v___y_2959_ = v_a_2999_;
v___y_2960_ = v___y_2988_;
v___y_2961_ = v___y_2989_;
v___y_2962_ = v___y_2990_;
v___y_2963_ = v___y_2992_;
v___y_2964_ = v___y_2991_;
v___y_2965_ = v___y_2993_;
v___y_2966_ = v___y_2994_;
v___y_2967_ = v___y_2995_;
v___y_2968_ = v___y_2996_;
v___y_2969_ = v___y_2997_;
v_a_2970_ = v___x_3034_;
goto v___jp_2950_;
}
}
}
}
}
v___jp_3037_:
{
lean_object* v_toCold_3056_; lean_object* v_ref_3057_; lean_object* v___x_3058_; 
v_toCold_3056_ = lean_ctor_get(v___y_3040_, 0);
v_ref_3057_ = lean_ctor_get(v___y_3040_, 2);
lean_inc_ref(v___y_3043_);
v___x_3058_ = l_Lean_Cadical_Solver_assume(v___y_3043_, v___y_3045_, v___y_3055_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_options_3059_; uint8_t v_hasTrace_3060_; 
lean_dec_ref_known(v___x_3058_, 1);
v_options_3059_ = lean_ctor_get(v_toCold_3056_, 2);
v_hasTrace_3060_ = lean_ctor_get_uint8(v_options_3059_, sizeof(void*)*1);
if (v_hasTrace_3060_ == 0)
{
lean_object* v___x_3061_; 
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___x_2732_);
v___x_3061_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_3043_, v___y_3038_, v___y_3049_, v___y_3053_, v___y_3044_, v___y_3039_, v___y_3046_, v___y_3050_, v___y_3054_, v___y_3051_, v___y_3048_, v___y_3042_, v___y_3047_, v___y_3040_, v___y_3041_);
v___y_2805_ = v___y_3038_;
v___y_2806_ = v___y_3039_;
v___y_2807_ = v___y_3040_;
v___y_2808_ = v___y_3041_;
v___y_2809_ = v___y_3042_;
v___y_2810_ = v___y_3044_;
v___y_2811_ = v___y_3046_;
v___y_2812_ = v___y_3047_;
v___y_2813_ = v___y_3049_;
v___y_2814_ = v___y_3048_;
v___y_2815_ = v___y_3050_;
v___y_2816_ = v___y_3051_;
v___y_2817_ = v___y_3052_;
v___y_2818_ = v___y_3053_;
v___y_2819_ = v___y_3054_;
v___y_2820_ = v___x_3061_;
goto v___jp_2804_;
}
else
{
lean_object* v_inheritedTraceOptions_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v_inheritedTraceOptions_3062_ = lean_ctor_get(v_toCold_3056_, 11);
v___x_3063_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_3052_);
v___x_3064_ = l_Lean_Name_append(v___x_3063_, v___y_3052_);
v___x_3065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3062_, v_options_3059_, v___x_3064_);
lean_dec(v___x_3064_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = l_Lean_trace_profiler;
v___x_3067_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3059_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; 
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___x_2732_);
v___x_3068_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_3043_, v___y_3038_, v___y_3049_, v___y_3053_, v___y_3044_, v___y_3039_, v___y_3046_, v___y_3050_, v___y_3054_, v___y_3051_, v___y_3048_, v___y_3042_, v___y_3047_, v___y_3040_, v___y_3041_);
v___y_2805_ = v___y_3038_;
v___y_2806_ = v___y_3039_;
v___y_2807_ = v___y_3040_;
v___y_2808_ = v___y_3041_;
v___y_2809_ = v___y_3042_;
v___y_2810_ = v___y_3044_;
v___y_2811_ = v___y_3046_;
v___y_2812_ = v___y_3047_;
v___y_2813_ = v___y_3049_;
v___y_2814_ = v___y_3048_;
v___y_2815_ = v___y_3050_;
v___y_2816_ = v___y_3051_;
v___y_2817_ = v___y_3052_;
v___y_2818_ = v___y_3053_;
v___y_2819_ = v___y_3054_;
v___y_2820_ = v___x_3068_;
goto v___jp_2804_;
}
else
{
v___y_2980_ = v___y_3038_;
v___y_2981_ = v___y_3039_;
v___y_2982_ = v___y_3040_;
v___y_2983_ = v___y_3043_;
v___y_2984_ = v___y_3041_;
v___y_2985_ = v___y_3042_;
v___y_2986_ = v___y_3044_;
v___y_2987_ = v___y_3046_;
v___y_2988_ = v_options_3059_;
v___y_2989_ = v___x_3065_;
v___y_2990_ = v___y_3047_;
v___y_2991_ = v___y_3049_;
v___y_2992_ = v___y_3048_;
v___y_2993_ = v___y_3050_;
v___y_2994_ = v___y_3051_;
v___y_2995_ = v___y_3052_;
v___y_2996_ = v___y_3053_;
v___y_2997_ = v___y_3054_;
goto v___jp_2979_;
}
}
else
{
v___y_2980_ = v___y_3038_;
v___y_2981_ = v___y_3039_;
v___y_2982_ = v___y_3040_;
v___y_2983_ = v___y_3043_;
v___y_2984_ = v___y_3041_;
v___y_2985_ = v___y_3042_;
v___y_2986_ = v___y_3044_;
v___y_2987_ = v___y_3046_;
v___y_2988_ = v_options_3059_;
v___y_2989_ = v___x_3065_;
v___y_2990_ = v___y_3047_;
v___y_2991_ = v___y_3049_;
v___y_2992_ = v___y_3048_;
v___y_2993_ = v___y_3050_;
v___y_2994_ = v___y_3051_;
v___y_2995_ = v___y_3052_;
v___y_2996_ = v___y_3053_;
v___y_2997_ = v___y_3054_;
goto v___jp_2979_;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3080_; 
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3043_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___x_2732_);
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_aig_2727_);
lean_dec_ref(v_tacticContext_2725_);
v_a_3069_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3071_ = v___x_3058_;
v_isShared_3072_ = v_isSharedCheck_3080_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3058_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3080_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3073_ = lean_io_error_to_string(v_a_3069_);
v___x_3074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
v___x_3075_ = l_Lean_MessageData_ofFormat(v___x_3074_);
lean_inc(v_ref_3057_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v_ref_3057_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3076_);
v___x_3078_ = v___x_3071_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
v___jp_3081_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v_theoryState_3102_; lean_object* v_satExpr_3103_; lean_object* v_hypQueue_3104_; lean_object* v_usedHyps_3105_; uint8_t v_didChange_3106_; lean_object* v_solverTimeBudgetMs_3107_; lean_object* v_roundBudget_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3151_; 
lean_inc_ref(v_aig_2727_);
v___x_3100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3100_, 0, v_aig_2727_);
lean_ctor_set(v___x_3100_, 1, v_cache_2735_);
lean_ctor_set(v___x_3100_, 2, v___y_3085_);
v___x_3101_ = lean_st_ref_take(v___y_3087_);
v_theoryState_3102_ = lean_ctor_get(v___x_3101_, 3);
v_satExpr_3103_ = lean_ctor_get(v___x_3101_, 0);
v_hypQueue_3104_ = lean_ctor_get(v___x_3101_, 1);
v_usedHyps_3105_ = lean_ctor_get(v___x_3101_, 2);
v_didChange_3106_ = lean_ctor_get_uint8(v___x_3101_, sizeof(void*)*6);
v_solverTimeBudgetMs_3107_ = lean_ctor_get(v___x_3101_, 4);
v_roundBudget_3108_ = lean_ctor_get(v___x_3101_, 5);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3110_ = v___x_3101_;
v_isShared_3111_ = v_isSharedCheck_3151_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_roundBudget_3108_);
lean_inc(v_solverTimeBudgetMs_3107_);
lean_inc(v_theoryState_3102_);
lean_inc(v_usedHyps_3105_);
lean_inc(v_hypQueue_3104_);
lean_inc(v_satExpr_3103_);
lean_dec(v___x_3101_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3151_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v_funState_3112_; lean_object* v_preprocessCaches_3113_; lean_object* v_satSolver_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3149_; 
v_funState_3112_ = lean_ctor_get(v_theoryState_3102_, 0);
v_preprocessCaches_3113_ = lean_ctor_get(v_theoryState_3102_, 2);
v_satSolver_3114_ = lean_ctor_get(v_theoryState_3102_, 3);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_theoryState_3102_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v_theoryState_3102_, 1);
lean_dec(v_unused_3150_);
v___x_3116_ = v_theoryState_3102_;
v_isShared_3117_ = v_isSharedCheck_3149_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_satSolver_3114_);
lean_inc(v_preprocessCaches_3113_);
lean_inc(v_funState_3112_);
lean_dec(v_theoryState_3102_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3149_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 1, v___x_3100_);
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_funState_3112_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_preprocessCaches_3113_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_satSolver_3114_);
v___x_3119_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3121_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 3, v___x_3119_);
v___x_3121_ = v___x_3110_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_satExpr_3103_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_hypQueue_3104_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_usedHyps_3105_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_solverTimeBudgetMs_3107_);
lean_ctor_set(v_reuseFailAlloc_3147_, 5, v_roundBudget_3108_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*6, v_didChange_3106_);
v___x_3121_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_st_ref_put(v___y_3087_, v___x_3121_);
v___x_3123_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_3083_, v___y_3082_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v___x_3124_; 
lean_dec_ref_known(v___x_3123_, 1);
v___x_3124_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_3087_);
if (lean_obj_tag(v___x_3124_) == 0)
{
uint8_t v_invert_3125_; 
v_invert_3125_ = lean_ctor_get_uint8(v_ref_2736_, sizeof(void*)*1);
if (v_invert_3125_ == 0)
{
lean_object* v_a_3126_; lean_object* v_gate_3127_; 
v_a_3126_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3124_, 1);
v_gate_3127_ = lean_ctor_get(v_ref_2736_, 0);
v___y_3038_ = v___y_3086_;
v___y_3039_ = v___y_3090_;
v___y_3040_ = v___y_3098_;
v___y_3041_ = v___y_3099_;
v___y_3042_ = v___y_3096_;
v___y_3043_ = v_a_3126_;
v___y_3044_ = v___y_3089_;
v___y_3045_ = v_gate_3127_;
v___y_3046_ = v___y_3091_;
v___y_3047_ = v___y_3097_;
v___y_3048_ = v___y_3095_;
v___y_3049_ = v___y_3087_;
v___y_3050_ = v___y_3092_;
v___y_3051_ = v___y_3094_;
v___y_3052_ = v___y_3084_;
v___y_3053_ = v___y_3088_;
v___y_3054_ = v___y_3093_;
v___y_3055_ = v___x_2731_;
goto v___jp_3037_;
}
else
{
lean_object* v_a_3128_; lean_object* v_gate_3129_; uint8_t v___x_3130_; 
v_a_3128_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3124_, 1);
v_gate_3129_ = lean_ctor_get(v_ref_2736_, 0);
v___x_3130_ = 0;
v___y_3038_ = v___y_3086_;
v___y_3039_ = v___y_3090_;
v___y_3040_ = v___y_3098_;
v___y_3041_ = v___y_3099_;
v___y_3042_ = v___y_3096_;
v___y_3043_ = v_a_3128_;
v___y_3044_ = v___y_3089_;
v___y_3045_ = v_gate_3129_;
v___y_3046_ = v___y_3091_;
v___y_3047_ = v___y_3097_;
v___y_3048_ = v___y_3095_;
v___y_3049_ = v___y_3087_;
v___y_3050_ = v___y_3092_;
v___y_3051_ = v___y_3094_;
v___y_3052_ = v___y_3084_;
v___y_3053_ = v___y_3088_;
v___y_3054_ = v___y_3093_;
v___y_3055_ = v___x_3130_;
goto v___jp_3037_;
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v___y_3084_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___x_2732_);
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_aig_2727_);
lean_dec_ref(v_tacticContext_2725_);
v_a_3131_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3124_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3124_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v___y_3084_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___x_2732_);
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_aig_2727_);
lean_dec_ref(v_tacticContext_2725_);
v_a_3139_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3123_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3123_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
}
}
}
v___jp_3152_:
{
if (lean_obj_tag(v___y_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v_toCold_3171_; lean_object* v_options_3172_; uint8_t v_hasTrace_3173_; 
v_a_3170_ = lean_ctor_get(v___y_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___y_3169_, 1);
v_toCold_3171_ = lean_ctor_get(v___y_3167_, 0);
v_options_3172_ = lean_ctor_get(v_toCold_3171_, 2);
v_hasTrace_3173_ = lean_ctor_get_uint8(v_options_3172_, sizeof(void*)*1);
if (v_hasTrace_3173_ == 0)
{
lean_object* v_cnf_3174_; 
lean_dec(v_cls_2737_);
v_cnf_3174_ = lean_ctor_get(v_a_3170_, 0);
lean_inc_ref(v_cnf_3174_);
v___y_3082_ = v_cnf_3174_;
v___y_3083_ = v___y_3154_;
v___y_3084_ = v___y_3165_;
v___y_3085_ = v_a_3170_;
v___y_3086_ = v___y_3163_;
v___y_3087_ = v___y_3164_;
v___y_3088_ = v___y_3156_;
v___y_3089_ = v___y_3155_;
v___y_3090_ = v___y_3158_;
v___y_3091_ = v___y_3157_;
v___y_3092_ = v___y_3168_;
v___y_3093_ = v___y_3153_;
v___y_3094_ = v___y_3161_;
v___y_3095_ = v___y_3166_;
v___y_3096_ = v___y_3162_;
v___y_3097_ = v___y_3160_;
v___y_3098_ = v___y_3167_;
v___y_3099_ = v___y_3159_;
goto v___jp_3081_;
}
else
{
lean_object* v_cnf_3175_; lean_object* v_inheritedTraceOptions_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v_cnf_3175_ = lean_ctor_get(v_a_3170_, 0);
lean_inc_ref(v_cnf_3175_);
v_inheritedTraceOptions_3176_ = lean_ctor_get(v_toCold_3171_, 11);
v___x_3177_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v_cls_2737_);
v___x_3178_ = l_Lean_Name_append(v___x_3177_, v_cls_2737_);
v___x_3179_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3176_, v_options_3172_, v___x_3178_);
lean_dec(v___x_3178_);
if (v___x_3179_ == 0)
{
lean_dec(v_cls_2737_);
v___y_3082_ = v_cnf_3175_;
v___y_3083_ = v___y_3154_;
v___y_3084_ = v___y_3165_;
v___y_3085_ = v_a_3170_;
v___y_3086_ = v___y_3163_;
v___y_3087_ = v___y_3164_;
v___y_3088_ = v___y_3156_;
v___y_3089_ = v___y_3155_;
v___y_3090_ = v___y_3158_;
v___y_3091_ = v___y_3157_;
v___y_3092_ = v___y_3168_;
v___y_3093_ = v___y_3153_;
v___y_3094_ = v___y_3161_;
v___y_3095_ = v___y_3166_;
v___y_3096_ = v___y_3162_;
v___y_3097_ = v___y_3160_;
v___y_3098_ = v___y_3167_;
v___y_3099_ = v___y_3159_;
goto v___jp_3081_;
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3180_ = lean_array_get_size(v_cnf_3175_);
v___x_3181_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_3182_ = l_Nat_reprFast(v___x_3180_);
v___x_3183_ = lean_string_append(v___x_3181_, v___x_3182_);
lean_dec_ref(v___x_3182_);
v___x_3184_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_3185_ = lean_string_append(v___x_3183_, v___x_3184_);
v___x_3186_ = lean_nat_sub(v___x_3180_, v___y_3154_);
v___x_3187_ = l_Nat_reprFast(v___x_3186_);
v___x_3188_ = lean_string_append(v___x_3185_, v___x_3187_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_3190_ = lean_string_append(v___x_3188_, v___x_3189_);
v___x_3191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
v___x_3192_ = l_Lean_MessageData_ofFormat(v___x_3191_);
v___x_3193_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_2737_, v___x_3192_, v___y_3162_, v___y_3160_, v___y_3167_, v___y_3159_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_dec_ref_known(v___x_3193_, 1);
v___y_3082_ = v_cnf_3175_;
v___y_3083_ = v___y_3154_;
v___y_3084_ = v___y_3165_;
v___y_3085_ = v_a_3170_;
v___y_3086_ = v___y_3163_;
v___y_3087_ = v___y_3164_;
v___y_3088_ = v___y_3156_;
v___y_3089_ = v___y_3155_;
v___y_3090_ = v___y_3158_;
v___y_3091_ = v___y_3157_;
v___y_3092_ = v___y_3168_;
v___y_3093_ = v___y_3153_;
v___y_3094_ = v___y_3161_;
v___y_3095_ = v___y_3166_;
v___y_3096_ = v___y_3162_;
v___y_3097_ = v___y_3160_;
v___y_3098_ = v___y_3167_;
v___y_3099_ = v___y_3159_;
goto v___jp_3081_;
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v_cnf_3175_);
lean_dec(v_a_3170_);
lean_dec(v___y_3165_);
lean_dec(v___y_3154_);
lean_dec_ref(v_cache_2735_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___x_2732_);
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_aig_2727_);
lean_dec_ref(v_tacticContext_2725_);
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v___y_3165_);
lean_dec(v___y_3154_);
lean_dec(v_cls_2737_);
lean_dec_ref(v_cache_2735_);
lean_dec_ref(v___f_2733_);
lean_dec_ref(v___x_2732_);
lean_dec_ref(v___x_2730_);
lean_dec(v___x_2729_);
lean_dec(v___x_2728_);
lean_dec_ref(v_aig_2727_);
lean_dec_ref(v_tacticContext_2725_);
v_a_3202_ = lean_ctor_get(v___y_3169_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___y_3169_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___y_3169_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___y_3169_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
v___jp_3210_:
{
lean_object* v___x_3232_; double v___x_3233_; double v___x_3234_; double v___x_3235_; double v___x_3236_; double v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3232_ = lean_io_mono_nanos_now();
v___x_3233_ = lean_float_of_nat(v___y_3228_);
v___x_3234_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_3235_ = lean_float_div(v___x_3233_, v___x_3234_);
v___x_3236_ = lean_float_of_nat(v___x_3232_);
v___x_3237_ = lean_float_div(v___x_3236_, v___x_3234_);
v___x_3238_ = lean_box_float(v___x_3235_);
v___x_3239_ = lean_box_float(v___x_3237_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3238_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_a_3231_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
lean_inc_ref(v___x_2732_);
lean_inc(v___y_3226_);
v___x_3242_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_3226_, v___x_2731_, v___x_2732_, v___y_3220_, v___y_3211_, v___y_3221_, v___f_2738_, v___x_3241_, v___y_3224_, v___y_3225_, v___y_3215_, v___y_3214_, v___y_3217_, v___y_3216_, v___y_3230_, v___y_3212_, v___y_3222_, v___y_3227_, v___y_3223_, v___y_3219_, v___y_3229_, v___y_3218_);
v___y_3153_ = v___y_3212_;
v___y_3154_ = v___y_3213_;
v___y_3155_ = v___y_3214_;
v___y_3156_ = v___y_3215_;
v___y_3157_ = v___y_3216_;
v___y_3158_ = v___y_3217_;
v___y_3159_ = v___y_3218_;
v___y_3160_ = v___y_3219_;
v___y_3161_ = v___y_3222_;
v___y_3162_ = v___y_3223_;
v___y_3163_ = v___y_3224_;
v___y_3164_ = v___y_3225_;
v___y_3165_ = v___y_3226_;
v___y_3166_ = v___y_3227_;
v___y_3167_ = v___y_3229_;
v___y_3168_ = v___y_3230_;
v___y_3169_ = v___x_3242_;
goto v___jp_3152_;
}
v___jp_3243_:
{
lean_object* v___x_3265_; double v___x_3266_; double v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3265_ = lean_io_get_num_heartbeats();
v___x_3266_ = lean_float_of_nat(v___y_3245_);
v___x_3267_ = lean_float_of_nat(v___x_3265_);
v___x_3268_ = lean_box_float(v___x_3266_);
v___x_3269_ = lean_box_float(v___x_3267_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v_a_3264_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
lean_inc_ref(v___x_2732_);
lean_inc(v___y_3260_);
v___x_3272_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_3260_, v___x_2731_, v___x_2732_, v___y_3254_, v___y_3244_, v___y_3255_, v___f_2738_, v___x_3271_, v___y_3258_, v___y_3259_, v___y_3249_, v___y_3248_, v___y_3251_, v___y_3250_, v___y_3263_, v___y_3246_, v___y_3256_, v___y_3261_, v___y_3257_, v___y_3253_, v___y_3262_, v___y_3252_);
v___y_3153_ = v___y_3246_;
v___y_3154_ = v___y_3247_;
v___y_3155_ = v___y_3248_;
v___y_3156_ = v___y_3249_;
v___y_3157_ = v___y_3250_;
v___y_3158_ = v___y_3251_;
v___y_3159_ = v___y_3252_;
v___y_3160_ = v___y_3253_;
v___y_3161_ = v___y_3256_;
v___y_3162_ = v___y_3257_;
v___y_3163_ = v___y_3258_;
v___y_3164_ = v___y_3259_;
v___y_3165_ = v___y_3260_;
v___y_3166_ = v___y_3261_;
v___y_3167_ = v___y_3262_;
v___y_3168_ = v___y_3263_;
v___y_3169_ = v___x_3272_;
goto v___jp_3152_;
}
v___jp_3273_:
{
lean_object* v___x_3294_; lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3348_; 
v___x_3294_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_3281_);
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3348_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3348_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
uint8_t v___x_3299_; 
v___x_3299_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_3283_, v___x_2734_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = lean_io_mono_nanos_now();
v___x_3301_ = l_IO_lazyPure___redArg(v___y_3282_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_del_object(v___x_3297_);
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 1);
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
v___y_3211_ = v___y_3274_;
v___y_3212_ = v___y_3275_;
v___y_3213_ = v___y_3276_;
v___y_3214_ = v___y_3277_;
v___y_3215_ = v___y_3278_;
v___y_3216_ = v___y_3279_;
v___y_3217_ = v___y_3280_;
v___y_3218_ = v___y_3281_;
v___y_3219_ = v___y_3284_;
v___y_3220_ = v___y_3283_;
v___y_3221_ = v_a_3295_;
v___y_3222_ = v___y_3286_;
v___y_3223_ = v___y_3287_;
v___y_3224_ = v___y_3288_;
v___y_3225_ = v___y_3289_;
v___y_3226_ = v___y_3290_;
v___y_3227_ = v___y_3291_;
v___y_3228_ = v___x_3300_;
v___y_3229_ = v___y_3293_;
v___y_3230_ = v___y_3292_;
v_a_3231_ = v___x_3307_;
goto v___jp_3210_;
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3323_; 
v_a_3310_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3312_ = v___x_3301_;
v_isShared_3313_ = v_isSharedCheck_3323_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3301_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3323_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3314_ = lean_io_error_to_string(v_a_3310_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 3);
lean_ctor_set(v___x_3312_, 0, v___x_3314_);
v___x_3316_ = v___x_3312_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3317_ = l_Lean_MessageData_ofFormat(v___x_3316_);
lean_inc(v___y_3285_);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___y_3285_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3318_);
v___x_3320_ = v___x_3297_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
v___y_3211_ = v___y_3274_;
v___y_3212_ = v___y_3275_;
v___y_3213_ = v___y_3276_;
v___y_3214_ = v___y_3277_;
v___y_3215_ = v___y_3278_;
v___y_3216_ = v___y_3279_;
v___y_3217_ = v___y_3280_;
v___y_3218_ = v___y_3281_;
v___y_3219_ = v___y_3284_;
v___y_3220_ = v___y_3283_;
v___y_3221_ = v_a_3295_;
v___y_3222_ = v___y_3286_;
v___y_3223_ = v___y_3287_;
v___y_3224_ = v___y_3288_;
v___y_3225_ = v___y_3289_;
v___y_3226_ = v___y_3290_;
v___y_3227_ = v___y_3291_;
v___y_3228_ = v___x_3300_;
v___y_3229_ = v___y_3293_;
v___y_3230_ = v___y_3292_;
v_a_3231_ = v___x_3320_;
goto v___jp_3210_;
}
}
}
}
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_io_get_num_heartbeats();
v___x_3325_ = l_IO_lazyPure___redArg(v___y_3282_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_del_object(v___x_3297_);
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3325_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3325_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set_tag(v___x_3328_, 1);
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
v___y_3244_ = v___y_3274_;
v___y_3245_ = v___x_3324_;
v___y_3246_ = v___y_3275_;
v___y_3247_ = v___y_3276_;
v___y_3248_ = v___y_3277_;
v___y_3249_ = v___y_3278_;
v___y_3250_ = v___y_3279_;
v___y_3251_ = v___y_3280_;
v___y_3252_ = v___y_3281_;
v___y_3253_ = v___y_3284_;
v___y_3254_ = v___y_3283_;
v___y_3255_ = v_a_3295_;
v___y_3256_ = v___y_3286_;
v___y_3257_ = v___y_3287_;
v___y_3258_ = v___y_3288_;
v___y_3259_ = v___y_3289_;
v___y_3260_ = v___y_3290_;
v___y_3261_ = v___y_3291_;
v___y_3262_ = v___y_3293_;
v___y_3263_ = v___y_3292_;
v_a_3264_ = v___x_3331_;
goto v___jp_3243_;
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3347_; 
v_a_3334_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3336_ = v___x_3325_;
v_isShared_3337_ = v_isSharedCheck_3347_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3325_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3347_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3338_ = lean_io_error_to_string(v_a_3334_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 3);
lean_ctor_set(v___x_3336_, 0, v___x_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3341_ = l_Lean_MessageData_ofFormat(v___x_3340_);
lean_inc(v___y_3285_);
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___y_3285_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3342_);
v___x_3344_ = v___x_3297_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
v___y_3244_ = v___y_3274_;
v___y_3245_ = v___x_3324_;
v___y_3246_ = v___y_3275_;
v___y_3247_ = v___y_3276_;
v___y_3248_ = v___y_3277_;
v___y_3249_ = v___y_3278_;
v___y_3250_ = v___y_3279_;
v___y_3251_ = v___y_3280_;
v___y_3252_ = v___y_3281_;
v___y_3253_ = v___y_3284_;
v___y_3254_ = v___y_3283_;
v___y_3255_ = v_a_3295_;
v___y_3256_ = v___y_3286_;
v___y_3257_ = v___y_3287_;
v___y_3258_ = v___y_3288_;
v___y_3259_ = v___y_3289_;
v___y_3260_ = v___y_3290_;
v___y_3261_ = v___y_3291_;
v___y_3262_ = v___y_3293_;
v___y_3263_ = v___y_3292_;
v_a_3264_ = v___x_3344_;
goto v___jp_3243_;
}
}
}
}
}
}
}
v___jp_3349_:
{
lean_object* v_toCold_3364_; lean_object* v_options_3365_; lean_object* v_cnf_3366_; lean_object* v_ref_3367_; lean_object* v_inheritedTraceOptions_3368_; uint8_t v_hasTrace_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___f_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_toCold_3364_ = lean_ctor_get(v___y_3362_, 0);
v_options_3365_ = lean_ctor_get(v_toCold_3364_, 2);
v_cnf_3366_ = lean_ctor_get(v_cnfCache_2739_, 0);
v_ref_3367_ = lean_ctor_get(v___y_3362_, 2);
v_inheritedTraceOptions_3368_ = lean_ctor_get(v_toCold_3364_, 11);
v_hasTrace_3369_ = lean_ctor_get_uint8(v_options_3365_, sizeof(void*)*1);
v___x_3370_ = lean_array_get_size(v_cnf_3366_);
v___x_3371_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_3372_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig_2727_, v_cnfCache_2739_);
v___f_3373_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3373_, 0, v___x_2740_);
lean_closure_set(v___f_3373_, 1, v___x_3371_);
lean_closure_set(v___f_3373_, 2, v_result_2741_);
lean_closure_set(v___f_3373_, 3, v___x_3372_);
v___x_3374_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13));
v___x_3375_ = l_Lean_Name_mkStr3(v___x_2742_, v___x_2743_, v___x_3374_);
if (v_hasTrace_3369_ == 0)
{
lean_object* v___x_3376_; 
lean_dec_ref(v___f_2738_);
v___x_3376_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_3373_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
v___y_3153_ = v___y_3357_;
v___y_3154_ = v___x_3370_;
v___y_3155_ = v___y_3353_;
v___y_3156_ = v___y_3352_;
v___y_3157_ = v___y_3355_;
v___y_3158_ = v___y_3354_;
v___y_3159_ = v___y_3363_;
v___y_3160_ = v___y_3361_;
v___y_3161_ = v___y_3358_;
v___y_3162_ = v___y_3360_;
v___y_3163_ = v___y_3350_;
v___y_3164_ = v___y_3351_;
v___y_3165_ = v___x_3375_;
v___y_3166_ = v___y_3359_;
v___y_3167_ = v___y_3362_;
v___y_3168_ = v___y_3356_;
v___y_3169_ = v___x_3376_;
goto v___jp_3152_;
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3377_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___x_3375_);
v___x_3378_ = l_Lean_Name_append(v___x_3377_, v___x_3375_);
v___x_3379_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3368_, v_options_3365_, v___x_3378_);
lean_dec(v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3380_ = l_Lean_trace_profiler;
v___x_3381_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3365_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; 
lean_dec_ref(v___f_2738_);
v___x_3382_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_3373_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
v___y_3153_ = v___y_3357_;
v___y_3154_ = v___x_3370_;
v___y_3155_ = v___y_3353_;
v___y_3156_ = v___y_3352_;
v___y_3157_ = v___y_3355_;
v___y_3158_ = v___y_3354_;
v___y_3159_ = v___y_3363_;
v___y_3160_ = v___y_3361_;
v___y_3161_ = v___y_3358_;
v___y_3162_ = v___y_3360_;
v___y_3163_ = v___y_3350_;
v___y_3164_ = v___y_3351_;
v___y_3165_ = v___x_3375_;
v___y_3166_ = v___y_3359_;
v___y_3167_ = v___y_3362_;
v___y_3168_ = v___y_3356_;
v___y_3169_ = v___x_3382_;
goto v___jp_3152_;
}
else
{
v___y_3274_ = v___x_3379_;
v___y_3275_ = v___y_3357_;
v___y_3276_ = v___x_3370_;
v___y_3277_ = v___y_3353_;
v___y_3278_ = v___y_3352_;
v___y_3279_ = v___y_3355_;
v___y_3280_ = v___y_3354_;
v___y_3281_ = v___y_3363_;
v___y_3282_ = v___f_3373_;
v___y_3283_ = v_options_3365_;
v___y_3284_ = v___y_3361_;
v___y_3285_ = v_ref_3367_;
v___y_3286_ = v___y_3358_;
v___y_3287_ = v___y_3360_;
v___y_3288_ = v___y_3350_;
v___y_3289_ = v___y_3351_;
v___y_3290_ = v___x_3375_;
v___y_3291_ = v___y_3359_;
v___y_3292_ = v___y_3356_;
v___y_3293_ = v___y_3362_;
goto v___jp_3273_;
}
}
else
{
v___y_3274_ = v___x_3379_;
v___y_3275_ = v___y_3357_;
v___y_3276_ = v___x_3370_;
v___y_3277_ = v___y_3353_;
v___y_3278_ = v___y_3352_;
v___y_3279_ = v___y_3355_;
v___y_3280_ = v___y_3354_;
v___y_3281_ = v___y_3363_;
v___y_3282_ = v___f_3373_;
v___y_3283_ = v_options_3365_;
v___y_3284_ = v___y_3361_;
v___y_3285_ = v_ref_3367_;
v___y_3286_ = v___y_3358_;
v___y_3287_ = v___y_3360_;
v___y_3288_ = v___y_3350_;
v___y_3289_ = v___y_3351_;
v___y_3290_ = v___x_3375_;
v___y_3291_ = v___y_3359_;
v___y_3292_ = v___y_3356_;
v___y_3293_ = v___y_3362_;
goto v___jp_3273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11___boxed(lean_object** _args){
lean_object* v_tacticContext_3401_ = _args[0];
lean_object* v___x_3402_ = _args[1];
lean_object* v_aig_3403_ = _args[2];
lean_object* v___x_3404_ = _args[3];
lean_object* v___x_3405_ = _args[4];
lean_object* v___x_3406_ = _args[5];
lean_object* v___x_3407_ = _args[6];
lean_object* v___x_3408_ = _args[7];
lean_object* v___f_3409_ = _args[8];
lean_object* v___x_3410_ = _args[9];
lean_object* v_cache_3411_ = _args[10];
lean_object* v_ref_3412_ = _args[11];
lean_object* v_cls_3413_ = _args[12];
lean_object* v___f_3414_ = _args[13];
lean_object* v_cnfCache_3415_ = _args[14];
lean_object* v___x_3416_ = _args[15];
lean_object* v_result_3417_ = _args[16];
lean_object* v___x_3418_ = _args[17];
lean_object* v___x_3419_ = _args[18];
lean_object* v_____r_3420_ = _args[19];
lean_object* v___y_3421_ = _args[20];
lean_object* v___y_3422_ = _args[21];
lean_object* v___y_3423_ = _args[22];
lean_object* v___y_3424_ = _args[23];
lean_object* v___y_3425_ = _args[24];
lean_object* v___y_3426_ = _args[25];
lean_object* v___y_3427_ = _args[26];
lean_object* v___y_3428_ = _args[27];
lean_object* v___y_3429_ = _args[28];
lean_object* v___y_3430_ = _args[29];
lean_object* v___y_3431_ = _args[30];
lean_object* v___y_3432_ = _args[31];
lean_object* v___y_3433_ = _args[32];
lean_object* v___y_3434_ = _args[33];
lean_object* v___y_3435_ = _args[34];
_start:
{
uint8_t v___x_1194181__boxed_3436_; lean_object* v_res_3437_; 
v___x_1194181__boxed_3436_ = lean_unbox(v___x_3407_);
v_res_3437_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v_tacticContext_3401_, v___x_3402_, v_aig_3403_, v___x_3404_, v___x_3405_, v___x_3406_, v___x_1194181__boxed_3436_, v___x_3408_, v___f_3409_, v___x_3410_, v_cache_3411_, v_ref_3412_, v_cls_3413_, v___f_3414_, v_cnfCache_3415_, v___x_3416_, v_result_3417_, v___x_3418_, v___x_3419_, v_____r_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v_ref_3412_);
lean_dec_ref(v___x_3410_);
lean_dec(v___x_3402_);
return v_res_3437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(lean_object* v_e_3438_){
_start:
{
if (lean_obj_tag(v_e_3438_) == 0)
{
uint8_t v___x_3439_; 
v___x_3439_ = 2;
return v___x_3439_;
}
else
{
uint8_t v___x_3440_; 
v___x_3440_ = 0;
return v___x_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20___boxed(lean_object* v_e_3441_){
_start:
{
uint8_t v_res_3442_; lean_object* v_r_3443_; 
v_res_3442_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(v_e_3441_);
lean_dec_ref(v_e_3441_);
v_r_3443_ = lean_box(v_res_3442_);
return v_r_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(lean_object* v_cls_3444_, uint8_t v_collapsed_3445_, lean_object* v_tag_3446_, lean_object* v_opts_3447_, uint8_t v_clsEnabled_3448_, lean_object* v_oldTraces_3449_, lean_object* v_msg_3450_, lean_object* v_resStartStop_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v_data_3472_; lean_object* v_fst_3483_; lean_object* v_snd_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; lean_object* v___y_3488_; lean_object* v_a_3489_; uint8_t v___y_3504_; double v___y_3536_; 
v_fst_3467_ = lean_ctor_get(v_resStartStop_3451_, 0);
lean_inc(v_fst_3467_);
v_snd_3468_ = lean_ctor_get(v_resStartStop_3451_, 1);
lean_inc(v_snd_3468_);
lean_dec_ref(v_resStartStop_3451_);
v_fst_3483_ = lean_ctor_get(v_snd_3468_, 0);
lean_inc(v_fst_3483_);
v_snd_3484_ = lean_ctor_get(v_snd_3468_, 1);
lean_inc(v_snd_3484_);
lean_dec(v_snd_3468_);
v___x_3485_ = l_Lean_trace_profiler;
v___x_3486_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3447_, v___x_3485_);
if (v___x_3486_ == 0)
{
v___y_3504_ = v___x_3486_;
goto v___jp_3503_;
}
else
{
lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3541_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3542_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3447_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; double v___x_3545_; double v___x_3546_; double v___x_3547_; 
v___x_3543_ = l_Lean_trace_profiler_threshold;
v___x_3544_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3447_, v___x_3543_);
v___x_3545_ = lean_float_of_nat(v___x_3544_);
v___x_3546_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_3547_ = lean_float_div(v___x_3545_, v___x_3546_);
v___y_3536_ = v___x_3547_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; double v___x_3550_; 
v___x_3548_ = l_Lean_trace_profiler_threshold;
v___x_3549_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3447_, v___x_3548_);
v___x_3550_ = lean_float_of_nat(v___x_3549_);
v___y_3536_ = v___x_3550_;
goto v___jp_3535_;
}
}
v___jp_3469_:
{
lean_object* v___x_3473_; 
lean_inc(v___y_3471_);
v___x_3473_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_3449_, v_data_3472_, v___y_3471_, v___y_3470_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref_known(v___x_3473_, 1);
v___x_3474_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3467_);
return v___x_3474_;
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v_fst_3467_);
v_a_3475_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3473_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
v___jp_3487_:
{
uint8_t v_result_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; double v___x_3493_; lean_object* v_data_3494_; 
v_result_3490_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(v_fst_3467_);
v___x_3491_ = lean_box(v_result_3490_);
v___x_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
v___x_3493_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_3446_);
lean_inc_ref(v___x_3492_);
lean_inc(v_cls_3444_);
v_data_3494_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3494_, 0, v_cls_3444_);
lean_ctor_set(v_data_3494_, 1, v___x_3492_);
lean_ctor_set(v_data_3494_, 2, v_tag_3446_);
lean_ctor_set_float(v_data_3494_, sizeof(void*)*3, v___x_3493_);
lean_ctor_set_float(v_data_3494_, sizeof(void*)*3 + 8, v___x_3493_);
lean_ctor_set_uint8(v_data_3494_, sizeof(void*)*3 + 16, v_collapsed_3445_);
if (v___x_3486_ == 0)
{
lean_dec_ref_known(v___x_3492_, 1);
lean_dec(v_snd_3484_);
lean_dec(v_fst_3483_);
lean_dec_ref(v_tag_3446_);
lean_dec(v_cls_3444_);
v___y_3470_ = v_a_3489_;
v___y_3471_ = v___y_3488_;
v_data_3472_ = v_data_3494_;
goto v___jp_3469_;
}
else
{
lean_object* v_data_3495_; double v___x_3496_; double v___x_3497_; 
lean_dec_ref_known(v_data_3494_, 3);
v_data_3495_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3495_, 0, v_cls_3444_);
lean_ctor_set(v_data_3495_, 1, v___x_3492_);
lean_ctor_set(v_data_3495_, 2, v_tag_3446_);
v___x_3496_ = lean_unbox_float(v_fst_3483_);
lean_dec(v_fst_3483_);
lean_ctor_set_float(v_data_3495_, sizeof(void*)*3, v___x_3496_);
v___x_3497_ = lean_unbox_float(v_snd_3484_);
lean_dec(v_snd_3484_);
lean_ctor_set_float(v_data_3495_, sizeof(void*)*3 + 8, v___x_3497_);
lean_ctor_set_uint8(v_data_3495_, sizeof(void*)*3 + 16, v_collapsed_3445_);
v___y_3470_ = v_a_3489_;
v___y_3471_ = v___y_3488_;
v_data_3472_ = v_data_3495_;
goto v___jp_3469_;
}
}
v___jp_3498_:
{
lean_object* v_ref_3499_; lean_object* v___x_3500_; 
v_ref_3499_ = lean_ctor_get(v___y_3464_, 2);
lean_inc(v___y_3465_);
lean_inc_ref(v___y_3464_);
lean_inc(v___y_3463_);
lean_inc_ref(v___y_3462_);
lean_inc(v___y_3461_);
lean_inc_ref(v___y_3460_);
lean_inc(v___y_3459_);
lean_inc_ref(v___y_3458_);
lean_inc(v___y_3457_);
lean_inc(v___y_3456_);
lean_inc_ref(v___y_3455_);
lean_inc(v___y_3454_);
lean_inc(v___y_3453_);
lean_inc_ref(v___y_3452_);
lean_inc(v_fst_3467_);
v___x_3500_ = lean_apply_16(v_msg_3450_, v_fst_3467_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, lean_box(0));
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___y_3488_ = v_ref_3499_;
v_a_3489_ = v_a_3501_;
goto v___jp_3487_;
}
else
{
lean_object* v___x_3502_; 
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_3488_ = v_ref_3499_;
v_a_3489_ = v___x_3502_;
goto v___jp_3487_;
}
}
v___jp_3503_:
{
if (v_clsEnabled_3448_ == 0)
{
if (v___y_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v_traceState_3506_; lean_object* v_env_3507_; lean_object* v_nextMacroScope_3508_; lean_object* v_ngen_3509_; lean_object* v_auxDeclNGen_3510_; lean_object* v_cache_3511_; lean_object* v_recordedDeps_3512_; lean_object* v_messages_3513_; lean_object* v_infoState_3514_; lean_object* v_snapshotTasks_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_snd_3484_);
lean_dec(v_fst_3483_);
lean_dec_ref(v_msg_3450_);
lean_dec_ref(v_tag_3446_);
lean_dec(v_cls_3444_);
v___x_3505_ = lean_st_ref_take(v___y_3465_);
v_traceState_3506_ = lean_ctor_get(v___x_3505_, 4);
v_env_3507_ = lean_ctor_get(v___x_3505_, 0);
v_nextMacroScope_3508_ = lean_ctor_get(v___x_3505_, 1);
v_ngen_3509_ = lean_ctor_get(v___x_3505_, 2);
v_auxDeclNGen_3510_ = lean_ctor_get(v___x_3505_, 3);
v_cache_3511_ = lean_ctor_get(v___x_3505_, 5);
v_recordedDeps_3512_ = lean_ctor_get(v___x_3505_, 6);
v_messages_3513_ = lean_ctor_get(v___x_3505_, 7);
v_infoState_3514_ = lean_ctor_get(v___x_3505_, 8);
v_snapshotTasks_3515_ = lean_ctor_get(v___x_3505_, 9);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3517_ = v___x_3505_;
v_isShared_3518_ = v_isSharedCheck_3534_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_snapshotTasks_3515_);
lean_inc(v_infoState_3514_);
lean_inc(v_messages_3513_);
lean_inc(v_recordedDeps_3512_);
lean_inc(v_cache_3511_);
lean_inc(v_traceState_3506_);
lean_inc(v_auxDeclNGen_3510_);
lean_inc(v_ngen_3509_);
lean_inc(v_nextMacroScope_3508_);
lean_inc(v_env_3507_);
lean_dec(v___x_3505_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3534_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
uint64_t v_tid_3519_; lean_object* v_traces_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3533_; 
v_tid_3519_ = lean_ctor_get_uint64(v_traceState_3506_, sizeof(void*)*1);
v_traces_3520_ = lean_ctor_get(v_traceState_3506_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_traceState_3506_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3522_ = v_traceState_3506_;
v_isShared_3523_ = v_isSharedCheck_3533_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_traces_3520_);
lean_dec(v_traceState_3506_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3533_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3524_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3449_, v_traces_3520_);
lean_dec_ref(v_traces_3520_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3524_);
v___x_3526_ = v___x_3522_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3524_);
lean_ctor_set_uint64(v_reuseFailAlloc_3532_, sizeof(void*)*1, v_tid_3519_);
v___x_3526_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 4, v___x_3526_);
v___x_3528_ = v___x_3517_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_env_3507_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_nextMacroScope_3508_);
lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_ngen_3509_);
lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_auxDeclNGen_3510_);
lean_ctor_set(v_reuseFailAlloc_3531_, 4, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3531_, 5, v_cache_3511_);
lean_ctor_set(v_reuseFailAlloc_3531_, 6, v_recordedDeps_3512_);
lean_ctor_set(v_reuseFailAlloc_3531_, 7, v_messages_3513_);
lean_ctor_set(v_reuseFailAlloc_3531_, 8, v_infoState_3514_);
lean_ctor_set(v_reuseFailAlloc_3531_, 9, v_snapshotTasks_3515_);
v___x_3528_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = lean_st_ref_put(v___y_3465_, v___x_3528_);
v___x_3530_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3467_);
return v___x_3530_;
}
}
}
}
}
else
{
goto v___jp_3498_;
}
}
else
{
goto v___jp_3498_;
}
}
v___jp_3535_:
{
double v___x_3537_; double v___x_3538_; double v___x_3539_; uint8_t v___x_3540_; 
v___x_3537_ = lean_unbox_float(v_snd_3484_);
v___x_3538_ = lean_unbox_float(v_fst_3483_);
v___x_3539_ = lean_float_sub(v___x_3537_, v___x_3538_);
v___x_3540_ = lean_float_decLt(v___y_3536_, v___x_3539_);
v___y_3504_ = v___x_3540_;
goto v___jp_3503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9___boxed(lean_object** _args){
lean_object* v_cls_3551_ = _args[0];
lean_object* v_collapsed_3552_ = _args[1];
lean_object* v_tag_3553_ = _args[2];
lean_object* v_opts_3554_ = _args[3];
lean_object* v_clsEnabled_3555_ = _args[4];
lean_object* v_oldTraces_3556_ = _args[5];
lean_object* v_msg_3557_ = _args[6];
lean_object* v_resStartStop_3558_ = _args[7];
lean_object* v___y_3559_ = _args[8];
lean_object* v___y_3560_ = _args[9];
lean_object* v___y_3561_ = _args[10];
lean_object* v___y_3562_ = _args[11];
lean_object* v___y_3563_ = _args[12];
lean_object* v___y_3564_ = _args[13];
lean_object* v___y_3565_ = _args[14];
lean_object* v___y_3566_ = _args[15];
lean_object* v___y_3567_ = _args[16];
lean_object* v___y_3568_ = _args[17];
lean_object* v___y_3569_ = _args[18];
lean_object* v___y_3570_ = _args[19];
lean_object* v___y_3571_ = _args[20];
lean_object* v___y_3572_ = _args[21];
lean_object* v___y_3573_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_3574_; uint8_t v_clsEnabled_boxed_3575_; lean_object* v_res_3576_; 
v_collapsed_boxed_3574_ = lean_unbox(v_collapsed_3552_);
v_clsEnabled_boxed_3575_ = lean_unbox(v_clsEnabled_3555_);
v_res_3576_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_3551_, v_collapsed_boxed_3574_, v_tag_3553_, v_opts_3554_, v_clsEnabled_boxed_3575_, v_oldTraces_3556_, v_msg_3557_, v_resStartStop_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec_ref(v_opts_3554_);
return v_res_3576_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(lean_object* v_e_3577_){
_start:
{
if (lean_obj_tag(v_e_3577_) == 0)
{
uint8_t v___x_3578_; 
v___x_3578_ = 2;
return v___x_3578_;
}
else
{
uint8_t v___x_3579_; 
v___x_3579_ = 0;
return v___x_3579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22___boxed(lean_object* v_e_3580_){
_start:
{
uint8_t v_res_3581_; lean_object* v_r_3582_; 
v_res_3581_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(v_e_3580_);
lean_dec_ref(v_e_3580_);
v_r_3582_ = lean_box(v_res_3581_);
return v_r_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(lean_object* v_cls_3583_, uint8_t v_collapsed_3584_, lean_object* v_tag_3585_, lean_object* v_opts_3586_, uint8_t v_clsEnabled_3587_, lean_object* v_oldTraces_3588_, lean_object* v_msg_3589_, lean_object* v_resStartStop_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_fst_3606_; lean_object* v_snd_3607_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v_data_3611_; lean_object* v_fst_3622_; lean_object* v_snd_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; lean_object* v___y_3627_; lean_object* v_a_3628_; uint8_t v___y_3643_; double v___y_3675_; 
v_fst_3606_ = lean_ctor_get(v_resStartStop_3590_, 0);
lean_inc(v_fst_3606_);
v_snd_3607_ = lean_ctor_get(v_resStartStop_3590_, 1);
lean_inc(v_snd_3607_);
lean_dec_ref(v_resStartStop_3590_);
v_fst_3622_ = lean_ctor_get(v_snd_3607_, 0);
lean_inc(v_fst_3622_);
v_snd_3623_ = lean_ctor_get(v_snd_3607_, 1);
lean_inc(v_snd_3623_);
lean_dec(v_snd_3607_);
v___x_3624_ = l_Lean_trace_profiler;
v___x_3625_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3586_, v___x_3624_);
if (v___x_3625_ == 0)
{
v___y_3643_ = v___x_3625_;
goto v___jp_3642_;
}
else
{
lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3681_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3586_, v___x_3680_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; double v___x_3684_; double v___x_3685_; double v___x_3686_; 
v___x_3682_ = l_Lean_trace_profiler_threshold;
v___x_3683_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3586_, v___x_3682_);
v___x_3684_ = lean_float_of_nat(v___x_3683_);
v___x_3685_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_3686_ = lean_float_div(v___x_3684_, v___x_3685_);
v___y_3675_ = v___x_3686_;
goto v___jp_3674_;
}
else
{
lean_object* v___x_3687_; lean_object* v___x_3688_; double v___x_3689_; 
v___x_3687_ = l_Lean_trace_profiler_threshold;
v___x_3688_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3586_, v___x_3687_);
v___x_3689_ = lean_float_of_nat(v___x_3688_);
v___y_3675_ = v___x_3689_;
goto v___jp_3674_;
}
}
v___jp_3608_:
{
lean_object* v___x_3612_; 
lean_inc(v___y_3609_);
v___x_3612_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_3588_, v_data_3611_, v___y_3609_, v___y_3610_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v___x_3613_; 
lean_dec_ref_known(v___x_3612_, 1);
v___x_3613_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3606_);
return v___x_3613_;
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_fst_3606_);
v_a_3614_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3612_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3612_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
v___jp_3626_:
{
uint8_t v_result_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; double v___x_3632_; lean_object* v_data_3633_; 
v_result_3629_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(v_fst_3606_);
v___x_3630_ = lean_box(v_result_3629_);
v___x_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
v___x_3632_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_3585_);
lean_inc_ref(v___x_3631_);
lean_inc(v_cls_3583_);
v_data_3633_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3633_, 0, v_cls_3583_);
lean_ctor_set(v_data_3633_, 1, v___x_3631_);
lean_ctor_set(v_data_3633_, 2, v_tag_3585_);
lean_ctor_set_float(v_data_3633_, sizeof(void*)*3, v___x_3632_);
lean_ctor_set_float(v_data_3633_, sizeof(void*)*3 + 8, v___x_3632_);
lean_ctor_set_uint8(v_data_3633_, sizeof(void*)*3 + 16, v_collapsed_3584_);
if (v___x_3625_ == 0)
{
lean_dec_ref_known(v___x_3631_, 1);
lean_dec(v_snd_3623_);
lean_dec(v_fst_3622_);
lean_dec_ref(v_tag_3585_);
lean_dec(v_cls_3583_);
v___y_3609_ = v___y_3627_;
v___y_3610_ = v_a_3628_;
v_data_3611_ = v_data_3633_;
goto v___jp_3608_;
}
else
{
lean_object* v_data_3634_; double v___x_3635_; double v___x_3636_; 
lean_dec_ref_known(v_data_3633_, 3);
v_data_3634_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3634_, 0, v_cls_3583_);
lean_ctor_set(v_data_3634_, 1, v___x_3631_);
lean_ctor_set(v_data_3634_, 2, v_tag_3585_);
v___x_3635_ = lean_unbox_float(v_fst_3622_);
lean_dec(v_fst_3622_);
lean_ctor_set_float(v_data_3634_, sizeof(void*)*3, v___x_3635_);
v___x_3636_ = lean_unbox_float(v_snd_3623_);
lean_dec(v_snd_3623_);
lean_ctor_set_float(v_data_3634_, sizeof(void*)*3 + 8, v___x_3636_);
lean_ctor_set_uint8(v_data_3634_, sizeof(void*)*3 + 16, v_collapsed_3584_);
v___y_3609_ = v___y_3627_;
v___y_3610_ = v_a_3628_;
v_data_3611_ = v_data_3634_;
goto v___jp_3608_;
}
}
v___jp_3637_:
{
lean_object* v_ref_3638_; lean_object* v___x_3639_; 
v_ref_3638_ = lean_ctor_get(v___y_3603_, 2);
lean_inc(v___y_3604_);
lean_inc_ref(v___y_3603_);
lean_inc(v___y_3602_);
lean_inc_ref(v___y_3601_);
lean_inc(v___y_3600_);
lean_inc_ref(v___y_3599_);
lean_inc(v___y_3598_);
lean_inc_ref(v___y_3597_);
lean_inc(v___y_3596_);
lean_inc(v___y_3595_);
lean_inc_ref(v___y_3594_);
lean_inc(v___y_3593_);
lean_inc(v___y_3592_);
lean_inc_ref(v___y_3591_);
lean_inc(v_fst_3606_);
v___x_3639_ = lean_apply_16(v_msg_3589_, v_fst_3606_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, lean_box(0));
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v___y_3627_ = v_ref_3638_;
v_a_3628_ = v_a_3640_;
goto v___jp_3626_;
}
else
{
lean_object* v___x_3641_; 
lean_dec_ref_known(v___x_3639_, 1);
v___x_3641_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_3627_ = v_ref_3638_;
v_a_3628_ = v___x_3641_;
goto v___jp_3626_;
}
}
v___jp_3642_:
{
if (v_clsEnabled_3587_ == 0)
{
if (v___y_3643_ == 0)
{
lean_object* v___x_3644_; lean_object* v_traceState_3645_; lean_object* v_env_3646_; lean_object* v_nextMacroScope_3647_; lean_object* v_ngen_3648_; lean_object* v_auxDeclNGen_3649_; lean_object* v_cache_3650_; lean_object* v_recordedDeps_3651_; lean_object* v_messages_3652_; lean_object* v_infoState_3653_; lean_object* v_snapshotTasks_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_snd_3623_);
lean_dec(v_fst_3622_);
lean_dec_ref(v_msg_3589_);
lean_dec_ref(v_tag_3585_);
lean_dec(v_cls_3583_);
v___x_3644_ = lean_st_ref_take(v___y_3604_);
v_traceState_3645_ = lean_ctor_get(v___x_3644_, 4);
v_env_3646_ = lean_ctor_get(v___x_3644_, 0);
v_nextMacroScope_3647_ = lean_ctor_get(v___x_3644_, 1);
v_ngen_3648_ = lean_ctor_get(v___x_3644_, 2);
v_auxDeclNGen_3649_ = lean_ctor_get(v___x_3644_, 3);
v_cache_3650_ = lean_ctor_get(v___x_3644_, 5);
v_recordedDeps_3651_ = lean_ctor_get(v___x_3644_, 6);
v_messages_3652_ = lean_ctor_get(v___x_3644_, 7);
v_infoState_3653_ = lean_ctor_get(v___x_3644_, 8);
v_snapshotTasks_3654_ = lean_ctor_get(v___x_3644_, 9);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3656_ = v___x_3644_;
v_isShared_3657_ = v_isSharedCheck_3673_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_snapshotTasks_3654_);
lean_inc(v_infoState_3653_);
lean_inc(v_messages_3652_);
lean_inc(v_recordedDeps_3651_);
lean_inc(v_cache_3650_);
lean_inc(v_traceState_3645_);
lean_inc(v_auxDeclNGen_3649_);
lean_inc(v_ngen_3648_);
lean_inc(v_nextMacroScope_3647_);
lean_inc(v_env_3646_);
lean_dec(v___x_3644_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3673_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
uint64_t v_tid_3658_; lean_object* v_traces_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3672_; 
v_tid_3658_ = lean_ctor_get_uint64(v_traceState_3645_, sizeof(void*)*1);
v_traces_3659_ = lean_ctor_get(v_traceState_3645_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v_traceState_3645_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3661_ = v_traceState_3645_;
v_isShared_3662_ = v_isSharedCheck_3672_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_traces_3659_);
lean_dec(v_traceState_3645_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3672_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3663_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3588_, v_traces_3659_);
lean_dec_ref(v_traces_3659_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set(v___x_3661_, 0, v___x_3663_);
v___x_3665_ = v___x_3661_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3663_);
lean_ctor_set_uint64(v_reuseFailAlloc_3671_, sizeof(void*)*1, v_tid_3658_);
v___x_3665_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3667_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 4, v___x_3665_);
v___x_3667_ = v___x_3656_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_env_3646_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_nextMacroScope_3647_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_ngen_3648_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_auxDeclNGen_3649_);
lean_ctor_set(v_reuseFailAlloc_3670_, 4, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3670_, 5, v_cache_3650_);
lean_ctor_set(v_reuseFailAlloc_3670_, 6, v_recordedDeps_3651_);
lean_ctor_set(v_reuseFailAlloc_3670_, 7, v_messages_3652_);
lean_ctor_set(v_reuseFailAlloc_3670_, 8, v_infoState_3653_);
lean_ctor_set(v_reuseFailAlloc_3670_, 9, v_snapshotTasks_3654_);
v___x_3667_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = lean_st_ref_put(v___y_3604_, v___x_3667_);
v___x_3669_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3606_);
return v___x_3669_;
}
}
}
}
}
else
{
goto v___jp_3637_;
}
}
else
{
goto v___jp_3637_;
}
}
v___jp_3674_:
{
double v___x_3676_; double v___x_3677_; double v___x_3678_; uint8_t v___x_3679_; 
v___x_3676_ = lean_unbox_float(v_snd_3623_);
v___x_3677_ = lean_unbox_float(v_fst_3622_);
v___x_3678_ = lean_float_sub(v___x_3676_, v___x_3677_);
v___x_3679_ = lean_float_decLt(v___y_3675_, v___x_3678_);
v___y_3643_ = v___x_3679_;
goto v___jp_3642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10___boxed(lean_object** _args){
lean_object* v_cls_3690_ = _args[0];
lean_object* v_collapsed_3691_ = _args[1];
lean_object* v_tag_3692_ = _args[2];
lean_object* v_opts_3693_ = _args[3];
lean_object* v_clsEnabled_3694_ = _args[4];
lean_object* v_oldTraces_3695_ = _args[5];
lean_object* v_msg_3696_ = _args[6];
lean_object* v_resStartStop_3697_ = _args[7];
lean_object* v___y_3698_ = _args[8];
lean_object* v___y_3699_ = _args[9];
lean_object* v___y_3700_ = _args[10];
lean_object* v___y_3701_ = _args[11];
lean_object* v___y_3702_ = _args[12];
lean_object* v___y_3703_ = _args[13];
lean_object* v___y_3704_ = _args[14];
lean_object* v___y_3705_ = _args[15];
lean_object* v___y_3706_ = _args[16];
lean_object* v___y_3707_ = _args[17];
lean_object* v___y_3708_ = _args[18];
lean_object* v___y_3709_ = _args[19];
lean_object* v___y_3710_ = _args[20];
lean_object* v___y_3711_ = _args[21];
lean_object* v___y_3712_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_3713_; uint8_t v_clsEnabled_boxed_3714_; lean_object* v_res_3715_; 
v_collapsed_boxed_3713_ = lean_unbox(v_collapsed_3691_);
v_clsEnabled_boxed_3714_ = lean_unbox(v_clsEnabled_3694_);
v_res_3715_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_3690_, v_collapsed_boxed_3713_, v_tag_3692_, v_opts_3693_, v_clsEnabled_boxed_3714_, v_oldTraces_3695_, v_msg_3696_, v_resStartStop_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_opts_3693_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(lean_object* v_aig_3716_){
_start:
{
lean_object* v_decls_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_decls_3717_ = lean_ctor_get(v_aig_3716_, 0);
v___x_3718_ = lean_array_get_size(v_decls_3717_);
v___x_3719_ = 0;
v___x_3720_ = lean_box(v___x_3719_);
v___x_3721_ = lean_mk_array(v___x_3718_, v___x_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1___boxed(lean_object* v_aig_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(v_aig_3722_);
lean_dec_ref(v_aig_3722_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(lean_object* v_aig_3726_){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3727_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___closed__0));
v___x_3728_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(v_aig_3726_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___boxed(lean_object* v_aig_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(v_aig_3730_);
lean_dec_ref(v_aig_3730_);
return v_res_3731_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8(void){
_start:
{
lean_object* v_cls_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_cls_3743_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7));
v___x_3744_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
v___x_3745_ = l_Lean_Name_append(v___x_3744_, v_cls_3743_);
return v___x_3745_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3750_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9));
v___x_3751_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
v___x_3752_ = l_Lean_Name_append(v___x_3751_, v___x_3750_);
return v___x_3752_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14(void){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0;
v___x_3757_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(v___x_3756_);
return v___x_3757_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3758_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14);
v___x_3759_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2);
v___x_3760_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0;
v___x_3761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
lean_ctor_set(v___x_3761_, 1, v___x_3759_);
lean_ctor_set(v___x_3761_, 2, v___x_3758_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v_toCold_3944_; lean_object* v_options_3945_; lean_object* v_ref_3946_; lean_object* v_inheritedTraceOptions_3947_; uint8_t v_hasTrace_3948_; lean_object* v___f_3949_; lean_object* v___f_3950_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; uint8_t v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; uint8_t v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v_a_3979_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; uint8_t v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; uint8_t v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v_a_4016_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; uint8_t v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; uint8_t v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; uint8_t v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; uint8_t v___y_4121_; lean_object* v___y_4148_; uint8_t v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___f_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v_cls_4232_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; uint8_t v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; uint8_t v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v_a_4331_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; uint8_t v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; uint8_t v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v_a_4374_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; uint8_t v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; uint8_t v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; uint8_t v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; uint8_t v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; uint8_t v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; uint8_t v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; uint8_t v___y_4640_; lean_object* v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v_a_4653_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; uint8_t v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4676_; uint8_t v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v_a_4689_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___y_4705_; lean_object* v___y_4706_; lean_object* v___y_4707_; lean_object* v___y_4708_; lean_object* v___y_4709_; lean_object* v___y_4710_; uint8_t v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; uint8_t v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v_ctx_4785_; lean_object* v___y_4786_; lean_object* v___y_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v___y_4794_; lean_object* v___y_4795_; lean_object* v___y_4796_; lean_object* v___y_4797_; lean_object* v___y_4798_; lean_object* v___y_4799_; 
v_toCold_3944_ = lean_ctor_get(v_a_3775_, 0);
v_options_3945_ = lean_ctor_get(v_toCold_3944_, 2);
v_ref_3946_ = lean_ctor_get(v_a_3775_, 2);
v_inheritedTraceOptions_3947_ = lean_ctor_get(v_toCold_3944_, 11);
v_hasTrace_3948_ = lean_ctor_get_uint8(v_options_3945_, sizeof(void*)*1);
v___f_3949_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__0));
v___f_3950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__1));
v___f_4228_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__2));
v___x_4229_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__3));
v___x_4230_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__4));
v___x_4231_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__5));
v_cls_4232_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7));
if (v_hasTrace_3948_ == 0)
{
lean_object* v_tacticContext_4855_; 
v_tacticContext_4855_ = lean_ctor_get(v_a_3763_, 2);
v_ctx_4785_ = v_tacticContext_4855_;
v___y_4786_ = v_a_3763_;
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
goto v___jp_4784_;
}
else
{
lean_object* v___f_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; lean_object* v___y_4861_; lean_object* v___y_4862_; lean_object* v_a_4863_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v_a_4875_; lean_object* v___y_4878_; lean_object* v___y_4879_; lean_object* v___y_4880_; uint8_t v___y_4891_; lean_object* v___y_4892_; lean_object* v___y_4893_; lean_object* v___y_4894_; lean_object* v___y_4895_; lean_object* v___y_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4899_; lean_object* v___y_4900_; lean_object* v_a_4901_; uint8_t v___y_4927_; lean_object* v___y_4928_; lean_object* v___y_4929_; lean_object* v___y_4930_; lean_object* v___y_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; uint8_t v___y_4941_; lean_object* v___y_4942_; lean_object* v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; lean_object* v___y_4947_; uint8_t v___y_4948_; lean_object* v___y_4949_; lean_object* v___y_4950_; lean_object* v___y_4951_; uint8_t v___y_4952_; lean_object* v___y_4953_; lean_object* v___y_4954_; lean_object* v_a_4955_; uint8_t v___y_4965_; lean_object* v___y_4966_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; uint8_t v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; uint8_t v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v_a_4979_; uint8_t v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4996_; lean_object* v___y_4997_; lean_object* v___y_4998_; lean_object* v___y_4999_; uint8_t v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; uint8_t v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5065_; lean_object* v___y_5066_; lean_object* v_a_5067_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v_a_5082_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; uint8_t v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5103_; lean_object* v___y_5104_; lean_object* v___y_5105_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v_a_5108_; uint8_t v___y_5134_; lean_object* v___y_5135_; lean_object* v___y_5136_; lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v___y_5139_; lean_object* v___y_5140_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v___y_5143_; lean_object* v___y_5144_; uint8_t v___y_5148_; lean_object* v___y_5149_; lean_object* v___y_5150_; lean_object* v___y_5151_; lean_object* v___y_5152_; lean_object* v___y_5153_; lean_object* v___y_5154_; lean_object* v___y_5155_; uint8_t v___y_5156_; lean_object* v___y_5157_; lean_object* v___y_5158_; lean_object* v___y_5159_; lean_object* v___y_5160_; lean_object* v_a_5161_; uint8_t v___y_5171_; lean_object* v___y_5172_; lean_object* v___y_5173_; lean_object* v___y_5174_; lean_object* v___y_5175_; lean_object* v___y_5176_; lean_object* v___y_5177_; lean_object* v___y_5178_; uint8_t v___y_5179_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v_a_5184_; uint8_t v___y_5197_; lean_object* v___y_5198_; lean_object* v___y_5199_; lean_object* v___y_5200_; lean_object* v___y_5201_; lean_object* v___y_5202_; lean_object* v___y_5203_; lean_object* v___y_5204_; lean_object* v___y_5205_; uint8_t v___y_5206_; uint8_t v___y_5207_; lean_object* v___y_5208_; lean_object* v___y_5209_; 
v___f_4856_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__16));
v___x_4857_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_4858_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4859_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3947_, v_options_3945_, v___x_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_5392_; uint8_t v___x_5393_; 
v___x_5392_ = l_Lean_trace_profiler;
v___x_5393_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3945_, v___x_5392_);
if (v___x_5393_ == 0)
{
lean_object* v_tacticContext_5394_; 
v_tacticContext_5394_ = lean_ctor_get(v_a_3763_, 2);
v_ctx_4785_ = v_tacticContext_5394_;
v___y_4786_ = v_a_3763_;
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
goto v___jp_4784_;
}
else
{
goto v___jp_5269_;
}
}
else
{
goto v___jp_5269_;
}
v___jp_4860_:
{
lean_object* v___x_4864_; double v___x_4865_; double v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4864_ = lean_io_get_num_heartbeats();
v___x_4865_ = lean_float_of_nat(v___y_4862_);
v___x_4866_ = lean_float_of_nat(v___x_4864_);
v___x_4867_ = lean_box_float(v___x_4865_);
v___x_4868_ = lean_box_float(v___x_4866_);
v___x_4869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4867_);
lean_ctor_set(v___x_4869_, 1, v___x_4868_);
v___x_4870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4870_, 0, v_a_4863_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_4232_, v_hasTrace_3948_, v___x_4857_, v_options_3945_, v___x_4859_, v___y_4861_, v___f_4856_, v___x_4870_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
return v___x_4871_;
}
v___jp_4872_:
{
lean_object* v___x_4876_; 
v___x_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4876_, 0, v_a_4875_);
v___y_4861_ = v___y_4873_;
v___y_4862_ = v___y_4874_;
v_a_4863_ = v___x_4876_;
goto v___jp_4860_;
}
v___jp_4877_:
{
if (lean_obj_tag(v___y_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
v_a_4881_ = lean_ctor_get(v___y_4880_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___y_4880_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___y_4880_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___y_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4886_; 
if (v_isShared_4884_ == 0)
{
lean_ctor_set_tag(v___x_4883_, 1);
v___x_4886_ = v___x_4883_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
v___y_4861_ = v___y_4878_;
v___y_4862_ = v___y_4879_;
v_a_4863_ = v___x_4886_;
goto v___jp_4860_;
}
}
}
else
{
lean_object* v_a_4889_; 
v_a_4889_ = lean_ctor_get(v___y_4880_, 0);
lean_inc(v_a_4889_);
lean_dec_ref_known(v___y_4880_, 1);
v___y_4873_ = v___y_4878_;
v___y_4874_ = v___y_4879_;
v_a_4875_ = v_a_4889_;
goto v___jp_4872_;
}
}
v___jp_4890_:
{
lean_object* v_result_4902_; lean_object* v_aig_4903_; lean_object* v_cache_4904_; lean_object* v_ref_4905_; lean_object* v_decls_4906_; lean_object* v___x_4907_; 
v_result_4902_ = lean_ctor_get(v_a_4901_, 0);
lean_inc_ref(v_result_4902_);
v_aig_4903_ = lean_ctor_get(v_result_4902_, 0);
lean_inc_ref(v_aig_4903_);
v_cache_4904_ = lean_ctor_get(v_a_4901_, 1);
lean_inc_ref(v_cache_4904_);
lean_dec_ref(v_a_4901_);
v_ref_4905_ = lean_ctor_get(v_result_4902_, 1);
lean_inc_ref(v_ref_4905_);
v_decls_4906_ = lean_ctor_get(v_aig_4903_, 0);
v___x_4907_ = lean_array_get_size(v_decls_4906_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_dec(v___y_4900_);
v___x_4908_ = lean_box(0);
lean_inc_ref(v___y_4897_);
lean_inc_ref(v___y_4895_);
v___x_4909_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v___y_4895_, v___x_4907_, v_aig_4903_, v___y_4893_, v___y_4892_, v___y_4897_, v___y_4891_, v___x_4857_, v___f_3950_, v___y_4894_, v_cache_4904_, v_ref_4905_, v_cls_4232_, v___f_3949_, v___y_4896_, v___x_4229_, v_result_4902_, v___x_4230_, v___x_4231_, v___x_4908_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
lean_dec_ref(v_ref_4905_);
v___y_4878_ = v___y_4898_;
v___y_4879_ = v___y_4899_;
v___y_4880_ = v___x_4909_;
goto v___jp_4877_;
}
else
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4910_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_4911_ = l_Nat_reprFast(v___x_4907_);
v___x_4912_ = lean_string_append(v___x_4910_, v___x_4911_);
lean_dec_ref(v___x_4911_);
v___x_4913_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_4914_ = lean_string_append(v___x_4912_, v___x_4913_);
v___x_4915_ = lean_nat_sub(v___x_4907_, v___y_4900_);
lean_dec(v___y_4900_);
v___x_4916_ = l_Nat_reprFast(v___x_4915_);
v___x_4917_ = lean_string_append(v___x_4914_, v___x_4916_);
lean_dec_ref(v___x_4916_);
v___x_4918_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_4919_ = lean_string_append(v___x_4917_, v___x_4918_);
v___x_4920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4919_);
v___x_4921_ = l_Lean_MessageData_ofFormat(v___x_4920_);
v___x_4922_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4232_, v___x_4921_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4924_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4923_);
lean_dec_ref_known(v___x_4922_, 1);
lean_inc_ref(v___y_4897_);
lean_inc_ref(v___y_4895_);
v___x_4924_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v___y_4895_, v___x_4907_, v_aig_4903_, v___y_4893_, v___y_4892_, v___y_4897_, v___y_4891_, v___x_4857_, v___f_3950_, v___y_4894_, v_cache_4904_, v_ref_4905_, v_cls_4232_, v___f_3949_, v___y_4896_, v___x_4229_, v_result_4902_, v___x_4230_, v___x_4231_, v_a_4923_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
lean_dec_ref(v_ref_4905_);
v___y_4878_ = v___y_4898_;
v___y_4879_ = v___y_4899_;
v___y_4880_ = v___x_4924_;
goto v___jp_4877_;
}
else
{
lean_object* v_a_4925_; 
lean_dec_ref(v_ref_4905_);
lean_dec_ref(v_cache_4904_);
lean_dec_ref(v_aig_4903_);
lean_dec_ref(v_result_4902_);
lean_dec_ref(v___y_4896_);
lean_dec(v___y_4893_);
lean_dec(v___y_4892_);
v_a_4925_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4925_);
lean_dec_ref_known(v___x_4922_, 1);
v___y_4873_ = v___y_4898_;
v___y_4874_ = v___y_4899_;
v_a_4875_ = v_a_4925_;
goto v___jp_4872_;
}
}
}
v___jp_4926_:
{
if (lean_obj_tag(v___y_4937_) == 0)
{
lean_object* v_a_4938_; 
v_a_4938_ = lean_ctor_get(v___y_4937_, 0);
lean_inc(v_a_4938_);
lean_dec_ref_known(v___y_4937_, 1);
v___y_4891_ = v___y_4927_;
v___y_4892_ = v___y_4928_;
v___y_4893_ = v___y_4929_;
v___y_4894_ = v___y_4930_;
v___y_4895_ = v___y_4931_;
v___y_4896_ = v___y_4932_;
v___y_4897_ = v___y_4933_;
v___y_4898_ = v___y_4934_;
v___y_4899_ = v___y_4935_;
v___y_4900_ = v___y_4936_;
v_a_4901_ = v_a_4938_;
goto v___jp_4890_;
}
else
{
lean_object* v_a_4939_; 
lean_dec(v___y_4936_);
lean_dec_ref(v___y_4932_);
lean_dec(v___y_4929_);
lean_dec(v___y_4928_);
v_a_4939_ = lean_ctor_get(v___y_4937_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___y_4937_, 1);
v___y_4873_ = v___y_4934_;
v___y_4874_ = v___y_4935_;
v_a_4875_ = v_a_4939_;
goto v___jp_4872_;
}
}
v___jp_4940_:
{
lean_object* v___x_4956_; double v___x_4957_; double v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4956_ = lean_io_get_num_heartbeats();
v___x_4957_ = lean_float_of_nat(v___y_4953_);
v___x_4958_ = lean_float_of_nat(v___x_4956_);
v___x_4959_ = lean_box_float(v___x_4957_);
v___x_4960_ = lean_box_float(v___x_4958_);
v___x_4961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4959_);
lean_ctor_set(v___x_4961_, 1, v___x_4960_);
v___x_4962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4962_, 0, v_a_4955_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4232_, v___y_4948_, v___x_4857_, v_options_3945_, v___y_4952_, v___y_4951_, v___f_4228_, v___x_4962_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
v___y_4927_ = v___y_4941_;
v___y_4928_ = v___y_4942_;
v___y_4929_ = v___y_4943_;
v___y_4930_ = v___y_4944_;
v___y_4931_ = v___y_4945_;
v___y_4932_ = v___y_4946_;
v___y_4933_ = v___y_4947_;
v___y_4934_ = v___y_4949_;
v___y_4935_ = v___y_4950_;
v___y_4936_ = v___y_4954_;
v___y_4937_ = v___x_4963_;
goto v___jp_4926_;
}
v___jp_4964_:
{
lean_object* v___x_4980_; double v___x_4981_; double v___x_4982_; double v___x_4983_; double v___x_4984_; double v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4980_ = lean_io_mono_nanos_now();
v___x_4981_ = lean_float_of_nat(v___y_4978_);
v___x_4982_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4983_ = lean_float_div(v___x_4981_, v___x_4982_);
v___x_4984_ = lean_float_of_nat(v___x_4980_);
v___x_4985_ = lean_float_div(v___x_4984_, v___x_4982_);
v___x_4986_ = lean_box_float(v___x_4983_);
v___x_4987_ = lean_box_float(v___x_4985_);
v___x_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4986_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
v___x_4989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4989_, 0, v_a_4979_);
lean_ctor_set(v___x_4989_, 1, v___x_4988_);
v___x_4990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4232_, v___y_4972_, v___x_4857_, v_options_3945_, v___y_4976_, v___y_4975_, v___f_4228_, v___x_4989_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
v___y_4927_ = v___y_4965_;
v___y_4928_ = v___y_4966_;
v___y_4929_ = v___y_4967_;
v___y_4930_ = v___y_4968_;
v___y_4931_ = v___y_4969_;
v___y_4932_ = v___y_4970_;
v___y_4933_ = v___y_4971_;
v___y_4934_ = v___y_4973_;
v___y_4935_ = v___y_4974_;
v___y_4936_ = v___y_4977_;
v___y_4937_ = v___x_4990_;
goto v___jp_4926_;
}
v___jp_4991_:
{
lean_object* v___x_5005_; 
v___x_5005_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3776_);
if (v___y_5000_ == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5034_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5008_ = v___x_5005_;
v_isShared_5009_ = v_isSharedCheck_5034_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_5005_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5034_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5010_ = lean_io_mono_nanos_now();
v___x_5011_ = l_IO_lazyPure___redArg(v___y_4999_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_del_object(v___x_5008_);
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_5011_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_5011_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set_tag(v___x_5014_, 1);
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
v___y_4965_ = v___y_4992_;
v___y_4966_ = v___y_4993_;
v___y_4967_ = v___y_4994_;
v___y_4968_ = v___y_4995_;
v___y_4969_ = v___y_4996_;
v___y_4970_ = v___y_4997_;
v___y_4971_ = v___y_4998_;
v___y_4972_ = v___y_5000_;
v___y_4973_ = v___y_5001_;
v___y_4974_ = v___y_5002_;
v___y_4975_ = v_a_5006_;
v___y_4976_ = v___y_5003_;
v___y_4977_ = v___y_5004_;
v___y_4978_ = v___x_5010_;
v_a_4979_ = v___x_5017_;
goto v___jp_4964_;
}
}
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5033_; 
v_a_5020_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5022_ = v___x_5011_;
v_isShared_5023_ = v_isSharedCheck_5033_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5011_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5033_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5024_; lean_object* v___x_5026_; 
v___x_5024_ = lean_io_error_to_string(v_a_5020_);
if (v_isShared_5023_ == 0)
{
lean_ctor_set_tag(v___x_5022_, 3);
lean_ctor_set(v___x_5022_, 0, v___x_5024_);
v___x_5026_ = v___x_5022_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5024_);
v___x_5026_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5030_; 
v___x_5027_ = l_Lean_MessageData_ofFormat(v___x_5026_);
lean_inc(v_ref_3946_);
v___x_5028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5028_, 0, v_ref_3946_);
lean_ctor_set(v___x_5028_, 1, v___x_5027_);
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5028_);
v___x_5030_ = v___x_5008_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v___x_5028_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
v___y_4965_ = v___y_4992_;
v___y_4966_ = v___y_4993_;
v___y_4967_ = v___y_4994_;
v___y_4968_ = v___y_4995_;
v___y_4969_ = v___y_4996_;
v___y_4970_ = v___y_4997_;
v___y_4971_ = v___y_4998_;
v___y_4972_ = v___y_5000_;
v___y_4973_ = v___y_5001_;
v___y_4974_ = v___y_5002_;
v___y_4975_ = v_a_5006_;
v___y_4976_ = v___y_5003_;
v___y_4977_ = v___y_5004_;
v___y_4978_ = v___x_5010_;
v_a_4979_ = v___x_5030_;
goto v___jp_4964_;
}
}
}
}
}
}
else
{
lean_object* v_a_5035_; lean_object* v___x_5037_; uint8_t v_isShared_5038_; uint8_t v_isSharedCheck_5063_; 
v_a_5035_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5037_ = v___x_5005_;
v_isShared_5038_ = v_isSharedCheck_5063_;
goto v_resetjp_5036_;
}
else
{
lean_inc(v_a_5035_);
lean_dec(v___x_5005_);
v___x_5037_ = lean_box(0);
v_isShared_5038_ = v_isSharedCheck_5063_;
goto v_resetjp_5036_;
}
v_resetjp_5036_:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5039_ = lean_io_get_num_heartbeats();
v___x_5040_ = l_IO_lazyPure___redArg(v___y_4999_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
lean_del_object(v___x_5037_);
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_5040_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v___x_5040_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_5040_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
lean_ctor_set_tag(v___x_5043_, 1);
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
v___y_4941_ = v___y_4992_;
v___y_4942_ = v___y_4993_;
v___y_4943_ = v___y_4994_;
v___y_4944_ = v___y_4995_;
v___y_4945_ = v___y_4996_;
v___y_4946_ = v___y_4997_;
v___y_4947_ = v___y_4998_;
v___y_4948_ = v___y_5000_;
v___y_4949_ = v___y_5001_;
v___y_4950_ = v___y_5002_;
v___y_4951_ = v_a_5035_;
v___y_4952_ = v___y_5003_;
v___y_4953_ = v___x_5039_;
v___y_4954_ = v___y_5004_;
v_a_4955_ = v___x_5046_;
goto v___jp_4940_;
}
}
}
else
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5062_; 
v_a_5049_ = lean_ctor_get(v___x_5040_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_5040_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5051_ = v___x_5040_;
v_isShared_5052_ = v_isSharedCheck_5062_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___x_5040_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5062_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5053_; lean_object* v___x_5055_; 
v___x_5053_ = lean_io_error_to_string(v_a_5049_);
if (v_isShared_5052_ == 0)
{
lean_ctor_set_tag(v___x_5051_, 3);
lean_ctor_set(v___x_5051_, 0, v___x_5053_);
v___x_5055_ = v___x_5051_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5059_; 
v___x_5056_ = l_Lean_MessageData_ofFormat(v___x_5055_);
lean_inc(v_ref_3946_);
v___x_5057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5057_, 0, v_ref_3946_);
lean_ctor_set(v___x_5057_, 1, v___x_5056_);
if (v_isShared_5038_ == 0)
{
lean_ctor_set(v___x_5037_, 0, v___x_5057_);
v___x_5059_ = v___x_5037_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5057_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
v___y_4941_ = v___y_4992_;
v___y_4942_ = v___y_4993_;
v___y_4943_ = v___y_4994_;
v___y_4944_ = v___y_4995_;
v___y_4945_ = v___y_4996_;
v___y_4946_ = v___y_4997_;
v___y_4947_ = v___y_4998_;
v___y_4948_ = v___y_5000_;
v___y_4949_ = v___y_5001_;
v___y_4950_ = v___y_5002_;
v___y_4951_ = v_a_5035_;
v___y_4952_ = v___y_5003_;
v___y_4953_ = v___x_5039_;
v___y_4954_ = v___y_5004_;
v_a_4955_ = v___x_5059_;
goto v___jp_4940_;
}
}
}
}
}
}
}
v___jp_5064_:
{
lean_object* v___x_5068_; double v___x_5069_; double v___x_5070_; double v___x_5071_; double v___x_5072_; double v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5068_ = lean_io_mono_nanos_now();
v___x_5069_ = lean_float_of_nat(v___y_5066_);
v___x_5070_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_5071_ = lean_float_div(v___x_5069_, v___x_5070_);
v___x_5072_ = lean_float_of_nat(v___x_5068_);
v___x_5073_ = lean_float_div(v___x_5072_, v___x_5070_);
v___x_5074_ = lean_box_float(v___x_5071_);
v___x_5075_ = lean_box_float(v___x_5073_);
v___x_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5077_, 0, v_a_5067_);
lean_ctor_set(v___x_5077_, 1, v___x_5076_);
v___x_5078_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_4232_, v_hasTrace_3948_, v___x_4857_, v_options_3945_, v___x_4859_, v___y_5065_, v___f_4856_, v___x_5077_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
return v___x_5078_;
}
v___jp_5079_:
{
lean_object* v___x_5083_; 
v___x_5083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5083_, 0, v_a_5082_);
v___y_5065_ = v___y_5080_;
v___y_5066_ = v___y_5081_;
v_a_5067_ = v___x_5083_;
goto v___jp_5064_;
}
v___jp_5084_:
{
if (lean_obj_tag(v___y_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
v_a_5088_ = lean_ctor_get(v___y_5087_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___y_5087_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___y_5087_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___y_5087_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
lean_ctor_set_tag(v___x_5090_, 1);
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
v___y_5065_ = v___y_5085_;
v___y_5066_ = v___y_5086_;
v_a_5067_ = v___x_5093_;
goto v___jp_5064_;
}
}
}
else
{
lean_object* v_a_5096_; 
v_a_5096_ = lean_ctor_get(v___y_5087_, 0);
lean_inc(v_a_5096_);
lean_dec_ref_known(v___y_5087_, 1);
v___y_5080_ = v___y_5085_;
v___y_5081_ = v___y_5086_;
v_a_5082_ = v_a_5096_;
goto v___jp_5079_;
}
}
v___jp_5097_:
{
lean_object* v_result_5109_; lean_object* v_aig_5110_; lean_object* v_cache_5111_; lean_object* v_ref_5112_; lean_object* v_decls_5113_; lean_object* v___x_5114_; 
v_result_5109_ = lean_ctor_get(v_a_5108_, 0);
lean_inc_ref(v_result_5109_);
v_aig_5110_ = lean_ctor_get(v_result_5109_, 0);
lean_inc_ref(v_aig_5110_);
v_cache_5111_ = lean_ctor_get(v_a_5108_, 1);
lean_inc_ref(v_cache_5111_);
lean_dec_ref(v_a_5108_);
v_ref_5112_ = lean_ctor_get(v_result_5109_, 1);
lean_inc_ref(v_ref_5112_);
v_decls_5113_ = lean_ctor_get(v_aig_5110_, 0);
v___x_5114_ = lean_array_get_size(v_decls_5113_);
if (v___x_4859_ == 0)
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
lean_dec(v___y_5105_);
v___x_5115_ = lean_box(0);
lean_inc_ref(v___y_5099_);
lean_inc_ref(v___y_5104_);
v___x_5116_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v___y_5104_, v___x_5114_, v_aig_5110_, v___y_5100_, v___y_5102_, v___y_5099_, v_hasTrace_3948_, v___x_4857_, v___f_3950_, v___y_5101_, v_cache_5111_, v_ref_5112_, v___y_5098_, v_cls_4232_, v___f_3949_, v___y_5103_, v___x_4229_, v_result_5109_, v___x_4230_, v___x_4231_, v___x_5115_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
lean_dec_ref(v_ref_5112_);
v___y_5085_ = v___y_5106_;
v___y_5086_ = v___y_5107_;
v___y_5087_ = v___x_5116_;
goto v___jp_5084_;
}
else
{
lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5117_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_5118_ = l_Nat_reprFast(v___x_5114_);
v___x_5119_ = lean_string_append(v___x_5117_, v___x_5118_);
lean_dec_ref(v___x_5118_);
v___x_5120_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_5121_ = lean_string_append(v___x_5119_, v___x_5120_);
v___x_5122_ = lean_nat_sub(v___x_5114_, v___y_5105_);
lean_dec(v___y_5105_);
v___x_5123_ = l_Nat_reprFast(v___x_5122_);
v___x_5124_ = lean_string_append(v___x_5121_, v___x_5123_);
lean_dec_ref(v___x_5123_);
v___x_5125_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_5126_ = lean_string_append(v___x_5124_, v___x_5125_);
v___x_5127_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5127_, 0, v___x_5126_);
v___x_5128_ = l_Lean_MessageData_ofFormat(v___x_5127_);
v___x_5129_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4232_, v___x_5128_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5131_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
lean_inc_ref(v___y_5099_);
lean_inc_ref(v___y_5104_);
v___x_5131_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v___y_5104_, v___x_5114_, v_aig_5110_, v___y_5100_, v___y_5102_, v___y_5099_, v_hasTrace_3948_, v___x_4857_, v___f_3950_, v___y_5101_, v_cache_5111_, v_ref_5112_, v___y_5098_, v_cls_4232_, v___f_3949_, v___y_5103_, v___x_4229_, v_result_5109_, v___x_4230_, v___x_4231_, v_a_5130_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
lean_dec_ref(v_ref_5112_);
v___y_5085_ = v___y_5106_;
v___y_5086_ = v___y_5107_;
v___y_5087_ = v___x_5131_;
goto v___jp_5084_;
}
else
{
lean_object* v_a_5132_; 
lean_dec_ref(v_ref_5112_);
lean_dec_ref(v_cache_5111_);
lean_dec_ref(v_aig_5110_);
lean_dec_ref(v_result_5109_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
lean_dec(v___y_5100_);
v_a_5132_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5132_);
lean_dec_ref_known(v___x_5129_, 1);
v___y_5080_ = v___y_5106_;
v___y_5081_ = v___y_5107_;
v_a_5082_ = v_a_5132_;
goto v___jp_5079_;
}
}
}
v___jp_5133_:
{
if (lean_obj_tag(v___y_5144_) == 0)
{
lean_object* v_a_5145_; 
v_a_5145_ = lean_ctor_get(v___y_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___y_5144_, 1);
v___y_5098_ = v___y_5134_;
v___y_5099_ = v___y_5135_;
v___y_5100_ = v___y_5136_;
v___y_5101_ = v___y_5137_;
v___y_5102_ = v___y_5138_;
v___y_5103_ = v___y_5139_;
v___y_5104_ = v___y_5140_;
v___y_5105_ = v___y_5141_;
v___y_5106_ = v___y_5142_;
v___y_5107_ = v___y_5143_;
v_a_5108_ = v_a_5145_;
goto v___jp_5097_;
}
else
{
lean_object* v_a_5146_; 
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5139_);
lean_dec(v___y_5138_);
lean_dec(v___y_5136_);
v_a_5146_ = lean_ctor_get(v___y_5144_, 0);
lean_inc(v_a_5146_);
lean_dec_ref_known(v___y_5144_, 1);
v___y_5080_ = v___y_5142_;
v___y_5081_ = v___y_5143_;
v_a_5082_ = v_a_5146_;
goto v___jp_5079_;
}
}
v___jp_5147_:
{
lean_object* v___x_5162_; double v___x_5163_; double v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5162_ = lean_io_get_num_heartbeats();
v___x_5163_ = lean_float_of_nat(v___y_5160_);
v___x_5164_ = lean_float_of_nat(v___x_5162_);
v___x_5165_ = lean_box_float(v___x_5163_);
v___x_5166_ = lean_box_float(v___x_5164_);
v___x_5167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5165_);
lean_ctor_set(v___x_5167_, 1, v___x_5166_);
v___x_5168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5168_, 0, v_a_5161_);
lean_ctor_set(v___x_5168_, 1, v___x_5167_);
v___x_5169_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4232_, v_hasTrace_3948_, v___x_4857_, v_options_3945_, v___y_5156_, v___y_5159_, v___f_4228_, v___x_5168_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
v___y_5134_ = v___y_5148_;
v___y_5135_ = v___y_5149_;
v___y_5136_ = v___y_5150_;
v___y_5137_ = v___y_5151_;
v___y_5138_ = v___y_5152_;
v___y_5139_ = v___y_5153_;
v___y_5140_ = v___y_5154_;
v___y_5141_ = v___y_5155_;
v___y_5142_ = v___y_5157_;
v___y_5143_ = v___y_5158_;
v___y_5144_ = v___x_5169_;
goto v___jp_5133_;
}
v___jp_5170_:
{
lean_object* v___x_5185_; double v___x_5186_; double v___x_5187_; double v___x_5188_; double v___x_5189_; double v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v___x_5185_ = lean_io_mono_nanos_now();
v___x_5186_ = lean_float_of_nat(v___y_5182_);
v___x_5187_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_5188_ = lean_float_div(v___x_5186_, v___x_5187_);
v___x_5189_ = lean_float_of_nat(v___x_5185_);
v___x_5190_ = lean_float_div(v___x_5189_, v___x_5187_);
v___x_5191_ = lean_box_float(v___x_5188_);
v___x_5192_ = lean_box_float(v___x_5190_);
v___x_5193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5193_, 0, v___x_5191_);
lean_ctor_set(v___x_5193_, 1, v___x_5192_);
v___x_5194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5194_, 0, v_a_5184_);
lean_ctor_set(v___x_5194_, 1, v___x_5193_);
v___x_5195_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4232_, v_hasTrace_3948_, v___x_4857_, v_options_3945_, v___y_5179_, v___y_5183_, v___f_4228_, v___x_5194_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
v___y_5134_ = v___y_5171_;
v___y_5135_ = v___y_5172_;
v___y_5136_ = v___y_5173_;
v___y_5137_ = v___y_5174_;
v___y_5138_ = v___y_5175_;
v___y_5139_ = v___y_5176_;
v___y_5140_ = v___y_5177_;
v___y_5141_ = v___y_5178_;
v___y_5142_ = v___y_5180_;
v___y_5143_ = v___y_5181_;
v___y_5144_ = v___x_5195_;
goto v___jp_5133_;
}
v___jp_5196_:
{
lean_object* v___x_5210_; 
v___x_5210_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3776_);
if (v___y_5206_ == 0)
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5239_; 
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5213_ = v___x_5210_;
v_isShared_5214_ = v_isSharedCheck_5239_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5210_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5239_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5215_; lean_object* v___x_5216_; 
v___x_5215_ = lean_io_mono_nanos_now();
v___x_5216_ = l_IO_lazyPure___redArg(v___y_5204_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5224_; 
lean_del_object(v___x_5213_);
v_a_5217_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5219_ = v___x_5216_;
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v___x_5216_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5222_; 
if (v_isShared_5220_ == 0)
{
lean_ctor_set_tag(v___x_5219_, 1);
v___x_5222_ = v___x_5219_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
v___y_5171_ = v___y_5197_;
v___y_5172_ = v___y_5198_;
v___y_5173_ = v___y_5199_;
v___y_5174_ = v___y_5200_;
v___y_5175_ = v___y_5201_;
v___y_5176_ = v___y_5202_;
v___y_5177_ = v___y_5203_;
v___y_5178_ = v___y_5205_;
v___y_5179_ = v___y_5207_;
v___y_5180_ = v___y_5208_;
v___y_5181_ = v___y_5209_;
v___y_5182_ = v___x_5215_;
v___y_5183_ = v_a_5211_;
v_a_5184_ = v___x_5222_;
goto v___jp_5170_;
}
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5238_; 
v_a_5225_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5227_ = v___x_5216_;
v_isShared_5228_ = v_isSharedCheck_5238_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5216_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5238_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5229_; lean_object* v___x_5231_; 
v___x_5229_ = lean_io_error_to_string(v_a_5225_);
if (v_isShared_5228_ == 0)
{
lean_ctor_set_tag(v___x_5227_, 3);
lean_ctor_set(v___x_5227_, 0, v___x_5229_);
v___x_5231_ = v___x_5227_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5229_);
v___x_5231_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5235_; 
v___x_5232_ = l_Lean_MessageData_ofFormat(v___x_5231_);
lean_inc(v_ref_3946_);
v___x_5233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5233_, 0, v_ref_3946_);
lean_ctor_set(v___x_5233_, 1, v___x_5232_);
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 0, v___x_5233_);
v___x_5235_ = v___x_5213_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___x_5233_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
v___y_5171_ = v___y_5197_;
v___y_5172_ = v___y_5198_;
v___y_5173_ = v___y_5199_;
v___y_5174_ = v___y_5200_;
v___y_5175_ = v___y_5201_;
v___y_5176_ = v___y_5202_;
v___y_5177_ = v___y_5203_;
v___y_5178_ = v___y_5205_;
v___y_5179_ = v___y_5207_;
v___y_5180_ = v___y_5208_;
v___y_5181_ = v___y_5209_;
v___y_5182_ = v___x_5215_;
v___y_5183_ = v_a_5211_;
v_a_5184_ = v___x_5235_;
goto v___jp_5170_;
}
}
}
}
}
}
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5268_; 
v_a_5240_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5268_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5268_ == 0)
{
v___x_5242_ = v___x_5210_;
v_isShared_5243_ = v_isSharedCheck_5268_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5210_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5268_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5244_; lean_object* v___x_5245_; 
v___x_5244_ = lean_io_get_num_heartbeats();
v___x_5245_ = l_IO_lazyPure___redArg(v___y_5204_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5253_; 
lean_del_object(v___x_5242_);
v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5248_ = v___x_5245_;
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5245_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5251_; 
if (v_isShared_5249_ == 0)
{
lean_ctor_set_tag(v___x_5248_, 1);
v___x_5251_ = v___x_5248_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
v___y_5148_ = v___y_5197_;
v___y_5149_ = v___y_5198_;
v___y_5150_ = v___y_5199_;
v___y_5151_ = v___y_5200_;
v___y_5152_ = v___y_5201_;
v___y_5153_ = v___y_5202_;
v___y_5154_ = v___y_5203_;
v___y_5155_ = v___y_5205_;
v___y_5156_ = v___y_5207_;
v___y_5157_ = v___y_5208_;
v___y_5158_ = v___y_5209_;
v___y_5159_ = v_a_5240_;
v___y_5160_ = v___x_5244_;
v_a_5161_ = v___x_5251_;
goto v___jp_5147_;
}
}
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5267_; 
v_a_5254_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5256_ = v___x_5245_;
v_isShared_5257_ = v_isSharedCheck_5267_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5245_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5267_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5258_; lean_object* v___x_5260_; 
v___x_5258_ = lean_io_error_to_string(v_a_5254_);
if (v_isShared_5257_ == 0)
{
lean_ctor_set_tag(v___x_5256_, 3);
lean_ctor_set(v___x_5256_, 0, v___x_5258_);
v___x_5260_ = v___x_5256_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5258_);
v___x_5260_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5264_; 
v___x_5261_ = l_Lean_MessageData_ofFormat(v___x_5260_);
lean_inc(v_ref_3946_);
v___x_5262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5262_, 0, v_ref_3946_);
lean_ctor_set(v___x_5262_, 1, v___x_5261_);
if (v_isShared_5243_ == 0)
{
lean_ctor_set(v___x_5242_, 0, v___x_5262_);
v___x_5264_ = v___x_5242_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v___x_5262_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
v___y_5148_ = v___y_5197_;
v___y_5149_ = v___y_5198_;
v___y_5150_ = v___y_5199_;
v___y_5151_ = v___y_5200_;
v___y_5152_ = v___y_5201_;
v___y_5153_ = v___y_5202_;
v___y_5154_ = v___y_5203_;
v___y_5155_ = v___y_5205_;
v___y_5156_ = v___y_5207_;
v___y_5157_ = v___y_5208_;
v___y_5158_ = v___y_5209_;
v___y_5159_ = v_a_5240_;
v___y_5160_ = v___x_5244_;
v_a_5161_ = v___x_5264_;
goto v___jp_5147_;
}
}
}
}
}
}
}
v___jp_5269_:
{
lean_object* v___x_5270_; lean_object* v_a_5271_; lean_object* v___x_5272_; uint8_t v___x_5273_; 
v___x_5270_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3776_);
v_a_5271_ = lean_ctor_get(v___x_5270_, 0);
lean_inc(v_a_5271_);
lean_dec_ref(v___x_5270_);
v___x_5272_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5273_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3945_, v___x_5272_);
if (v___x_5273_ == 0)
{
lean_object* v___x_5274_; lean_object* v_tacticContext_5275_; lean_object* v___x_5276_; lean_object* v_satExpr_5277_; lean_object* v_bvExpr_5278_; lean_object* v___x_5279_; lean_object* v_theoryState_5280_; lean_object* v_bitvecState_5281_; lean_object* v___x_5282_; lean_object* v_theoryState_5283_; lean_object* v_satExpr_5284_; lean_object* v_hypQueue_5285_; lean_object* v_usedHyps_5286_; uint8_t v_didChange_5287_; lean_object* v_solverTimeBudgetMs_5288_; lean_object* v_roundBudget_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5332_; 
v___x_5274_ = lean_io_mono_nanos_now();
v_tacticContext_5275_ = lean_ctor_get(v_a_3763_, 2);
v___x_5276_ = lean_st_ref_get(v_a_3764_);
v_satExpr_5277_ = lean_ctor_get(v___x_5276_, 0);
lean_inc_ref(v_satExpr_5277_);
lean_dec(v___x_5276_);
v_bvExpr_5278_ = lean_ctor_get(v_satExpr_5277_, 0);
lean_inc_ref(v_bvExpr_5278_);
lean_dec_ref(v_satExpr_5277_);
v___x_5279_ = lean_st_ref_get(v_a_3764_);
v_theoryState_5280_ = lean_ctor_get(v___x_5279_, 3);
lean_inc_ref(v_theoryState_5280_);
lean_dec(v___x_5279_);
v_bitvecState_5281_ = lean_ctor_get(v_theoryState_5280_, 1);
lean_inc_ref(v_bitvecState_5281_);
lean_dec_ref(v_theoryState_5280_);
v___x_5282_ = lean_st_ref_take(v_a_3764_);
v_theoryState_5283_ = lean_ctor_get(v___x_5282_, 3);
v_satExpr_5284_ = lean_ctor_get(v___x_5282_, 0);
v_hypQueue_5285_ = lean_ctor_get(v___x_5282_, 1);
v_usedHyps_5286_ = lean_ctor_get(v___x_5282_, 2);
v_didChange_5287_ = lean_ctor_get_uint8(v___x_5282_, sizeof(void*)*6);
v_solverTimeBudgetMs_5288_ = lean_ctor_get(v___x_5282_, 4);
v_roundBudget_5289_ = lean_ctor_get(v___x_5282_, 5);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5291_ = v___x_5282_;
v_isShared_5292_ = v_isSharedCheck_5332_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_roundBudget_5289_);
lean_inc(v_solverTimeBudgetMs_5288_);
lean_inc(v_theoryState_5283_);
lean_inc(v_usedHyps_5286_);
lean_inc(v_hypQueue_5285_);
lean_inc(v_satExpr_5284_);
lean_dec(v___x_5282_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5332_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v_funState_5293_; lean_object* v_preprocessCaches_5294_; lean_object* v_satSolver_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5330_; 
v_funState_5293_ = lean_ctor_get(v_theoryState_5283_, 0);
v_preprocessCaches_5294_ = lean_ctor_get(v_theoryState_5283_, 2);
v_satSolver_5295_ = lean_ctor_get(v_theoryState_5283_, 3);
v_isSharedCheck_5330_ = !lean_is_exclusive(v_theoryState_5283_);
if (v_isSharedCheck_5330_ == 0)
{
lean_object* v_unused_5331_; 
v_unused_5331_ = lean_ctor_get(v_theoryState_5283_, 1);
lean_dec(v_unused_5331_);
v___x_5297_ = v_theoryState_5283_;
v_isShared_5298_ = v_isSharedCheck_5330_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_satSolver_5295_);
lean_inc(v_preprocessCaches_5294_);
lean_inc(v_funState_5293_);
lean_dec(v_theoryState_5283_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5330_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5299_ = lean_unsigned_to_nat(0u);
v___x_5300_ = lean_unsigned_to_nat(16u);
v___x_5301_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 1, v___x_5301_);
v___x_5303_ = v___x_5297_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_funState_5293_);
lean_ctor_set(v_reuseFailAlloc_5329_, 1, v___x_5301_);
lean_ctor_set(v_reuseFailAlloc_5329_, 2, v_preprocessCaches_5294_);
lean_ctor_set(v_reuseFailAlloc_5329_, 3, v_satSolver_5295_);
v___x_5303_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5305_; 
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 3, v___x_5303_);
v___x_5305_ = v___x_5291_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_satExpr_5284_);
lean_ctor_set(v_reuseFailAlloc_5328_, 1, v_hypQueue_5285_);
lean_ctor_set(v_reuseFailAlloc_5328_, 2, v_usedHyps_5286_);
lean_ctor_set(v_reuseFailAlloc_5328_, 3, v___x_5303_);
lean_ctor_set(v_reuseFailAlloc_5328_, 4, v_solverTimeBudgetMs_5288_);
lean_ctor_set(v_reuseFailAlloc_5328_, 5, v_roundBudget_5289_);
lean_ctor_set_uint8(v_reuseFailAlloc_5328_, sizeof(void*)*6, v_didChange_5287_);
v___x_5305_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
lean_object* v___x_5306_; lean_object* v_aig_5307_; lean_object* v_blastCache_5308_; lean_object* v_cnfCache_5309_; lean_object* v_decls_5310_; lean_object* v___f_5311_; lean_object* v___x_5312_; 
v___x_5306_ = lean_st_ref_put(v_a_3764_, v___x_5305_);
v_aig_5307_ = lean_ctor_get(v_bitvecState_5281_, 0);
lean_inc_ref(v_aig_5307_);
v_blastCache_5308_ = lean_ctor_get(v_bitvecState_5281_, 1);
lean_inc_ref(v_blastCache_5308_);
v_cnfCache_5309_ = lean_ctor_get(v_bitvecState_5281_, 2);
lean_inc_ref(v_cnfCache_5309_);
lean_dec_ref(v_bitvecState_5281_);
v_decls_5310_ = lean_ctor_get(v_aig_5307_, 0);
lean_inc_ref(v_decls_5310_);
v___f_5311_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_5311_, 0, v_aig_5307_);
lean_closure_set(v___f_5311_, 1, v_bvExpr_5278_);
lean_closure_set(v___f_5311_, 2, v_blastCache_5308_);
v___x_5312_ = lean_array_get_size(v_decls_5310_);
lean_dec_ref(v_decls_5310_);
if (v___x_4859_ == 0)
{
lean_object* v___x_5313_; uint8_t v___x_5314_; 
v___x_5313_ = l_Lean_trace_profiler;
v___x_5314_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3945_, v___x_5313_);
if (v___x_5314_ == 0)
{
lean_object* v___x_5315_; 
v___x_5315_ = l_IO_lazyPure___redArg(v___f_5311_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5316_);
lean_dec_ref_known(v___x_5315_, 1);
v___y_5098_ = v___x_5273_;
v___y_5099_ = v___x_5301_;
v___y_5100_ = v___x_5300_;
v___y_5101_ = v___x_5272_;
v___y_5102_ = v___x_5299_;
v___y_5103_ = v_cnfCache_5309_;
v___y_5104_ = v_tacticContext_5275_;
v___y_5105_ = v___x_5312_;
v___y_5106_ = v_a_5271_;
v___y_5107_ = v___x_5274_;
v_a_5108_ = v_a_5316_;
goto v___jp_5097_;
}
else
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5327_; 
lean_dec_ref(v_cnfCache_5309_);
v_a_5317_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5319_ = v___x_5315_;
v_isShared_5320_ = v_isSharedCheck_5327_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5315_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5327_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5321_; lean_object* v___x_5323_; 
v___x_5321_ = lean_io_error_to_string(v_a_5317_);
if (v_isShared_5320_ == 0)
{
lean_ctor_set_tag(v___x_5319_, 3);
lean_ctor_set(v___x_5319_, 0, v___x_5321_);
v___x_5323_ = v___x_5319_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5321_);
v___x_5323_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5324_ = l_Lean_MessageData_ofFormat(v___x_5323_);
lean_inc(v_ref_3946_);
v___x_5325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5325_, 0, v_ref_3946_);
lean_ctor_set(v___x_5325_, 1, v___x_5324_);
v___y_5080_ = v_a_5271_;
v___y_5081_ = v___x_5274_;
v_a_5082_ = v___x_5325_;
goto v___jp_5079_;
}
}
}
}
else
{
v___y_5197_ = v___x_5273_;
v___y_5198_ = v___x_5301_;
v___y_5199_ = v___x_5300_;
v___y_5200_ = v___x_5272_;
v___y_5201_ = v___x_5299_;
v___y_5202_ = v_cnfCache_5309_;
v___y_5203_ = v_tacticContext_5275_;
v___y_5204_ = v___f_5311_;
v___y_5205_ = v___x_5312_;
v___y_5206_ = v___x_5273_;
v___y_5207_ = v___x_4859_;
v___y_5208_ = v_a_5271_;
v___y_5209_ = v___x_5274_;
goto v___jp_5196_;
}
}
else
{
v___y_5197_ = v___x_5273_;
v___y_5198_ = v___x_5301_;
v___y_5199_ = v___x_5300_;
v___y_5200_ = v___x_5272_;
v___y_5201_ = v___x_5299_;
v___y_5202_ = v_cnfCache_5309_;
v___y_5203_ = v_tacticContext_5275_;
v___y_5204_ = v___f_5311_;
v___y_5205_ = v___x_5312_;
v___y_5206_ = v___x_5273_;
v___y_5207_ = v___x_4859_;
v___y_5208_ = v_a_5271_;
v___y_5209_ = v___x_5274_;
goto v___jp_5196_;
}
}
}
}
}
}
else
{
lean_object* v___x_5333_; lean_object* v_tacticContext_5334_; lean_object* v___x_5335_; lean_object* v_satExpr_5336_; lean_object* v_bvExpr_5337_; lean_object* v___x_5338_; lean_object* v_theoryState_5339_; lean_object* v_bitvecState_5340_; lean_object* v___x_5341_; lean_object* v_theoryState_5342_; lean_object* v_satExpr_5343_; lean_object* v_hypQueue_5344_; lean_object* v_usedHyps_5345_; uint8_t v_didChange_5346_; lean_object* v_solverTimeBudgetMs_5347_; lean_object* v_roundBudget_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5391_; 
v___x_5333_ = lean_io_get_num_heartbeats();
v_tacticContext_5334_ = lean_ctor_get(v_a_3763_, 2);
v___x_5335_ = lean_st_ref_get(v_a_3764_);
v_satExpr_5336_ = lean_ctor_get(v___x_5335_, 0);
lean_inc_ref(v_satExpr_5336_);
lean_dec(v___x_5335_);
v_bvExpr_5337_ = lean_ctor_get(v_satExpr_5336_, 0);
lean_inc_ref(v_bvExpr_5337_);
lean_dec_ref(v_satExpr_5336_);
v___x_5338_ = lean_st_ref_get(v_a_3764_);
v_theoryState_5339_ = lean_ctor_get(v___x_5338_, 3);
lean_inc_ref(v_theoryState_5339_);
lean_dec(v___x_5338_);
v_bitvecState_5340_ = lean_ctor_get(v_theoryState_5339_, 1);
lean_inc_ref(v_bitvecState_5340_);
lean_dec_ref(v_theoryState_5339_);
v___x_5341_ = lean_st_ref_take(v_a_3764_);
v_theoryState_5342_ = lean_ctor_get(v___x_5341_, 3);
v_satExpr_5343_ = lean_ctor_get(v___x_5341_, 0);
v_hypQueue_5344_ = lean_ctor_get(v___x_5341_, 1);
v_usedHyps_5345_ = lean_ctor_get(v___x_5341_, 2);
v_didChange_5346_ = lean_ctor_get_uint8(v___x_5341_, sizeof(void*)*6);
v_solverTimeBudgetMs_5347_ = lean_ctor_get(v___x_5341_, 4);
v_roundBudget_5348_ = lean_ctor_get(v___x_5341_, 5);
v_isSharedCheck_5391_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5391_ == 0)
{
v___x_5350_ = v___x_5341_;
v_isShared_5351_ = v_isSharedCheck_5391_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_roundBudget_5348_);
lean_inc(v_solverTimeBudgetMs_5347_);
lean_inc(v_theoryState_5342_);
lean_inc(v_usedHyps_5345_);
lean_inc(v_hypQueue_5344_);
lean_inc(v_satExpr_5343_);
lean_dec(v___x_5341_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5391_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v_funState_5352_; lean_object* v_preprocessCaches_5353_; lean_object* v_satSolver_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5389_; 
v_funState_5352_ = lean_ctor_get(v_theoryState_5342_, 0);
v_preprocessCaches_5353_ = lean_ctor_get(v_theoryState_5342_, 2);
v_satSolver_5354_ = lean_ctor_get(v_theoryState_5342_, 3);
v_isSharedCheck_5389_ = !lean_is_exclusive(v_theoryState_5342_);
if (v_isSharedCheck_5389_ == 0)
{
lean_object* v_unused_5390_; 
v_unused_5390_ = lean_ctor_get(v_theoryState_5342_, 1);
lean_dec(v_unused_5390_);
v___x_5356_ = v_theoryState_5342_;
v_isShared_5357_ = v_isSharedCheck_5389_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_satSolver_5354_);
lean_inc(v_preprocessCaches_5353_);
lean_inc(v_funState_5352_);
lean_dec(v_theoryState_5342_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5389_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5362_; 
v___x_5358_ = lean_unsigned_to_nat(0u);
v___x_5359_ = lean_unsigned_to_nat(16u);
v___x_5360_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_5357_ == 0)
{
lean_ctor_set(v___x_5356_, 1, v___x_5360_);
v___x_5362_ = v___x_5356_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_funState_5352_);
lean_ctor_set(v_reuseFailAlloc_5388_, 1, v___x_5360_);
lean_ctor_set(v_reuseFailAlloc_5388_, 2, v_preprocessCaches_5353_);
lean_ctor_set(v_reuseFailAlloc_5388_, 3, v_satSolver_5354_);
v___x_5362_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
lean_object* v___x_5364_; 
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 3, v___x_5362_);
v___x_5364_ = v___x_5350_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_satExpr_5343_);
lean_ctor_set(v_reuseFailAlloc_5387_, 1, v_hypQueue_5344_);
lean_ctor_set(v_reuseFailAlloc_5387_, 2, v_usedHyps_5345_);
lean_ctor_set(v_reuseFailAlloc_5387_, 3, v___x_5362_);
lean_ctor_set(v_reuseFailAlloc_5387_, 4, v_solverTimeBudgetMs_5347_);
lean_ctor_set(v_reuseFailAlloc_5387_, 5, v_roundBudget_5348_);
lean_ctor_set_uint8(v_reuseFailAlloc_5387_, sizeof(void*)*6, v_didChange_5346_);
v___x_5364_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
lean_object* v___x_5365_; lean_object* v_aig_5366_; lean_object* v_blastCache_5367_; lean_object* v_cnfCache_5368_; lean_object* v_decls_5369_; lean_object* v___f_5370_; lean_object* v___x_5371_; 
v___x_5365_ = lean_st_ref_put(v_a_3764_, v___x_5364_);
v_aig_5366_ = lean_ctor_get(v_bitvecState_5340_, 0);
lean_inc_ref(v_aig_5366_);
v_blastCache_5367_ = lean_ctor_get(v_bitvecState_5340_, 1);
lean_inc_ref(v_blastCache_5367_);
v_cnfCache_5368_ = lean_ctor_get(v_bitvecState_5340_, 2);
lean_inc_ref(v_cnfCache_5368_);
lean_dec_ref(v_bitvecState_5340_);
v_decls_5369_ = lean_ctor_get(v_aig_5366_, 0);
lean_inc_ref(v_decls_5369_);
v___f_5370_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_5370_, 0, v_aig_5366_);
lean_closure_set(v___f_5370_, 1, v_bvExpr_5337_);
lean_closure_set(v___f_5370_, 2, v_blastCache_5367_);
v___x_5371_ = lean_array_get_size(v_decls_5369_);
lean_dec_ref(v_decls_5369_);
if (v___x_4859_ == 0)
{
lean_object* v___x_5372_; uint8_t v___x_5373_; 
v___x_5372_ = l_Lean_trace_profiler;
v___x_5373_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3945_, v___x_5372_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; 
v___x_5374_ = l_IO_lazyPure___redArg(v___f_5370_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v_a_5375_; 
v_a_5375_ = lean_ctor_get(v___x_5374_, 0);
lean_inc(v_a_5375_);
lean_dec_ref_known(v___x_5374_, 1);
v___y_4891_ = v___x_5273_;
v___y_4892_ = v___x_5358_;
v___y_4893_ = v___x_5359_;
v___y_4894_ = v___x_5272_;
v___y_4895_ = v_tacticContext_5334_;
v___y_4896_ = v_cnfCache_5368_;
v___y_4897_ = v___x_5360_;
v___y_4898_ = v_a_5271_;
v___y_4899_ = v___x_5333_;
v___y_4900_ = v___x_5371_;
v_a_4901_ = v_a_5375_;
goto v___jp_4890_;
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5386_; 
lean_dec_ref(v_cnfCache_5368_);
v_a_5376_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5378_ = v___x_5374_;
v_isShared_5379_ = v_isSharedCheck_5386_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5374_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5386_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5380_; lean_object* v___x_5382_; 
v___x_5380_ = lean_io_error_to_string(v_a_5376_);
if (v_isShared_5379_ == 0)
{
lean_ctor_set_tag(v___x_5378_, 3);
lean_ctor_set(v___x_5378_, 0, v___x_5380_);
v___x_5382_ = v___x_5378_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v___x_5380_);
v___x_5382_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5383_ = l_Lean_MessageData_ofFormat(v___x_5382_);
lean_inc(v_ref_3946_);
v___x_5384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5384_, 0, v_ref_3946_);
lean_ctor_set(v___x_5384_, 1, v___x_5383_);
v___y_4873_ = v_a_5271_;
v___y_4874_ = v___x_5333_;
v_a_4875_ = v___x_5384_;
goto v___jp_4872_;
}
}
}
}
else
{
v___y_4992_ = v___x_5273_;
v___y_4993_ = v___x_5358_;
v___y_4994_ = v___x_5359_;
v___y_4995_ = v___x_5272_;
v___y_4996_ = v_tacticContext_5334_;
v___y_4997_ = v_cnfCache_5368_;
v___y_4998_ = v___x_5360_;
v___y_4999_ = v___f_5370_;
v___y_5000_ = v___x_5273_;
v___y_5001_ = v_a_5271_;
v___y_5002_ = v___x_5333_;
v___y_5003_ = v___x_4859_;
v___y_5004_ = v___x_5371_;
goto v___jp_4991_;
}
}
else
{
v___y_4992_ = v___x_5273_;
v___y_4993_ = v___x_5358_;
v___y_4994_ = v___x_5359_;
v___y_4995_ = v___x_5272_;
v___y_4996_ = v_tacticContext_5334_;
v___y_4997_ = v_cnfCache_5368_;
v___y_4998_ = v___x_5360_;
v___y_4999_ = v___f_5370_;
v___y_5000_ = v___x_5273_;
v___y_5001_ = v_a_5271_;
v___y_5002_ = v___x_5333_;
v___y_5003_ = v___x_4859_;
v___y_5004_ = v___x_5371_;
goto v___jp_4991_;
}
}
}
}
}
}
}
}
v___jp_3778_:
{
lean_object* v___x_3795_; 
v___x_3795_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___y_3779_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3779_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3797_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v___x_3797_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_3785_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3807_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3807_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3807_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3802_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3780_, v_a_3796_, v_a_3798_);
lean_dec(v_a_3798_);
lean_dec(v_a_3796_);
v___x_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3803_);
v___x_3805_ = v___x_3800_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_a_3796_);
lean_dec_ref(v___y_3780_);
v_a_3808_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3797_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3797_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec_ref(v___y_3780_);
v_a_3816_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3795_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3795_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
v___jp_3824_:
{
if (lean_obj_tag(v___y_3846_) == 0)
{
lean_object* v_a_3847_; uint8_t v___x_3848_; 
v_a_3847_ = lean_ctor_get(v___y_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___y_3846_, 1);
v___x_3848_ = lean_unbox(v_a_3847_);
lean_dec(v_a_3847_);
switch(v___x_3848_)
{
case 0:
{
lean_object* v_toCold_3849_; lean_object* v_options_3850_; uint8_t v_hasTrace_3851_; 
lean_dec(v___y_3836_);
lean_dec(v___y_3831_);
v_toCold_3849_ = lean_ctor_get(v___y_3845_, 0);
v_options_3850_ = lean_ctor_get(v_toCold_3849_, 2);
v_hasTrace_3851_ = lean_ctor_get_uint8(v_options_3850_, sizeof(void*)*1);
if (v_hasTrace_3851_ == 0)
{
v___y_3779_ = v___y_3838_;
v___y_3780_ = v___y_3826_;
v___y_3781_ = v___y_3830_;
v___y_3782_ = v___y_3832_;
v___y_3783_ = v___y_3842_;
v___y_3784_ = v___y_3839_;
v___y_3785_ = v___y_3841_;
v___y_3786_ = v___y_3833_;
v___y_3787_ = v___y_3827_;
v___y_3788_ = v___y_3825_;
v___y_3789_ = v___y_3840_;
v___y_3790_ = v___y_3834_;
v___y_3791_ = v___y_3844_;
v___y_3792_ = v___y_3828_;
v___y_3793_ = v___y_3845_;
v___y_3794_ = v___y_3843_;
goto v___jp_3778_;
}
else
{
lean_object* v_inheritedTraceOptions_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v_inheritedTraceOptions_3852_ = lean_ctor_get(v_toCold_3849_, 11);
v___x_3853_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_3837_);
v___x_3854_ = l_Lean_Name_append(v___x_3853_, v___y_3837_);
v___x_3855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3852_, v_options_3850_, v___x_3854_);
lean_dec(v___x_3854_);
if (v___x_3855_ == 0)
{
v___y_3779_ = v___y_3838_;
v___y_3780_ = v___y_3826_;
v___y_3781_ = v___y_3830_;
v___y_3782_ = v___y_3832_;
v___y_3783_ = v___y_3842_;
v___y_3784_ = v___y_3839_;
v___y_3785_ = v___y_3841_;
v___y_3786_ = v___y_3833_;
v___y_3787_ = v___y_3827_;
v___y_3788_ = v___y_3825_;
v___y_3789_ = v___y_3840_;
v___y_3790_ = v___y_3834_;
v___y_3791_ = v___y_3844_;
v___y_3792_ = v___y_3828_;
v___y_3793_ = v___y_3845_;
v___y_3794_ = v___y_3843_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
lean_inc(v___y_3837_);
v___x_3857_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_3837_, v___x_3856_, v___y_3844_, v___y_3828_, v___y_3845_, v___y_3843_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_dec_ref_known(v___x_3857_, 1);
v___y_3779_ = v___y_3838_;
v___y_3780_ = v___y_3826_;
v___y_3781_ = v___y_3830_;
v___y_3782_ = v___y_3832_;
v___y_3783_ = v___y_3842_;
v___y_3784_ = v___y_3839_;
v___y_3785_ = v___y_3841_;
v___y_3786_ = v___y_3833_;
v___y_3787_ = v___y_3827_;
v___y_3788_ = v___y_3825_;
v___y_3789_ = v___y_3840_;
v___y_3790_ = v___y_3834_;
v___y_3791_ = v___y_3844_;
v___y_3792_ = v___y_3828_;
v___y_3793_ = v___y_3845_;
v___y_3794_ = v___y_3843_;
goto v___jp_3778_;
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3826_);
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_3866_; lean_object* v_satExpr_3867_; lean_object* v_hypQueue_3868_; lean_object* v_usedHyps_3869_; uint8_t v_didChange_3870_; lean_object* v_theoryState_3871_; lean_object* v_solverTimeBudgetMs_3872_; lean_object* v_roundBudget_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3934_; 
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3826_);
v___x_3866_ = lean_st_ref_take(v___y_3832_);
v_satExpr_3867_ = lean_ctor_get(v___x_3866_, 0);
v_hypQueue_3868_ = lean_ctor_get(v___x_3866_, 1);
v_usedHyps_3869_ = lean_ctor_get(v___x_3866_, 2);
v_didChange_3870_ = lean_ctor_get_uint8(v___x_3866_, sizeof(void*)*6);
v_theoryState_3871_ = lean_ctor_get(v___x_3866_, 3);
v_solverTimeBudgetMs_3872_ = lean_ctor_get(v___x_3866_, 4);
v_roundBudget_3873_ = lean_ctor_get(v___x_3866_, 5);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3875_ = v___x_3866_;
v_isShared_3876_ = v_isSharedCheck_3934_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_roundBudget_3873_);
lean_inc(v_solverTimeBudgetMs_3872_);
lean_inc(v_theoryState_3871_);
lean_inc(v_usedHyps_3869_);
lean_inc(v_hypQueue_3868_);
lean_inc(v_satExpr_3867_);
lean_dec(v___x_3866_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3934_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v_satSolver_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3930_; 
v___x_3877_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_3878_ = lean_ctor_get(v_theoryState_3871_, 3);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_theoryState_3871_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; lean_object* v_unused_3932_; lean_object* v_unused_3933_; 
v_unused_3931_ = lean_ctor_get(v_theoryState_3871_, 2);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_theoryState_3871_, 1);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_theoryState_3871_, 0);
lean_dec(v_unused_3933_);
v___x_3880_ = v_theoryState_3871_;
v_isShared_3881_ = v_isSharedCheck_3930_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_satSolver_3878_);
lean_dec(v_theoryState_3871_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3930_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3882_ = lean_box(0);
v___x_3883_ = lean_mk_array(v___y_3836_, v___x_3882_);
v___x_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___y_3831_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
lean_inc_ref(v___y_3829_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 2, v___x_3877_);
lean_ctor_set(v___x_3880_, 1, v___y_3829_);
lean_ctor_set(v___x_3880_, 0, v___x_3884_);
v___x_3886_ = v___x_3880_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v___y_3829_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_satSolver_3878_);
v___x_3886_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3888_; 
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 3, v___x_3886_);
v___x_3888_ = v___x_3875_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_satExpr_3867_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_hypQueue_3868_);
lean_ctor_set(v_reuseFailAlloc_3928_, 2, v_usedHyps_3869_);
lean_ctor_set(v_reuseFailAlloc_3928_, 3, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3928_, 4, v_solverTimeBudgetMs_3872_);
lean_ctor_set(v_reuseFailAlloc_3928_, 5, v_roundBudget_3873_);
lean_ctor_set_uint8(v_reuseFailAlloc_3928_, sizeof(void*)*6, v_didChange_3870_);
v___x_3888_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_st_ref_put(v___y_3832_, v___x_3888_);
v___x_3890_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_3830_, v___y_3832_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v_goal_3892_; lean_object* v___x_3893_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v_goal_3892_ = lean_ctor_get(v___y_3830_, 0);
lean_inc(v_goal_3892_);
lean_inc_ref(v___y_3835_);
v___x_3893_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v___y_3835_, v_goal_3892_, v_a_3891_, v___y_3842_, v___y_3839_, v___y_3841_, v___y_3833_, v___y_3827_, v___y_3825_, v___y_3840_, v___y_3834_, v___y_3844_, v___y_3828_, v___y_3845_, v___y_3843_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3911_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3911_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3911_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
if (lean_obj_tag(v_a_3894_) == 0)
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec_ref_known(v_a_3894_, 1);
lean_del_object(v___x_3896_);
v___x_3898_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_3899_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_3898_, v___y_3844_, v___y_3828_, v___y_3845_, v___y_3843_);
return v___x_3899_;
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3910_; 
v_a_3900_ = lean_ctor_get(v_a_3894_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_a_3894_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3902_ = v_a_3894_;
v_isShared_3903_ = v_isSharedCheck_3910_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v_a_3894_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3910_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3907_; 
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_3905_);
v___x_3907_ = v___x_3896_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
v_a_3912_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3893_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3893_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
v_a_3920_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3890_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3890_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
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
lean_object* v___x_3935_; 
lean_dec(v___y_3838_);
lean_dec(v___y_3836_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3826_);
v___x_3935_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_3845_, v___y_3843_);
return v___x_3935_;
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec(v___y_3838_);
lean_dec(v___y_3836_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3826_);
v_a_3936_ = lean_ctor_get(v___y_3846_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___y_3846_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___y_3846_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___y_3846_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
v___jp_3951_:
{
lean_object* v___x_3980_; double v___x_3981_; double v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3980_ = lean_io_get_num_heartbeats();
v___x_3981_ = lean_float_of_nat(v___y_3974_);
v___x_3982_ = lean_float_of_nat(v___x_3980_);
v___x_3983_ = lean_box_float(v___x_3981_);
v___x_3984_ = lean_box_float(v___x_3982_);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v_a_3979_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
lean_inc_ref(v___y_3958_);
lean_inc(v___y_3970_);
v___x_3987_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_3970_, v___y_3961_, v___y_3958_, v___y_3976_, v___y_3966_, v___y_3952_, v___f_3950_, v___x_3986_, v___y_3953_, v___y_3967_, v___y_3975_, v___y_3972_, v___y_3973_, v___y_3968_, v___y_3963_, v___y_3960_, v___y_3957_, v___y_3969_, v___y_3977_, v___y_3964_, v___y_3959_, v___y_3978_);
v___y_3825_ = v___y_3960_;
v___y_3826_ = v___y_3962_;
v___y_3827_ = v___y_3963_;
v___y_3828_ = v___y_3964_;
v___y_3829_ = v___y_3965_;
v___y_3830_ = v___y_3953_;
v___y_3831_ = v___y_3954_;
v___y_3832_ = v___y_3967_;
v___y_3833_ = v___y_3968_;
v___y_3834_ = v___y_3969_;
v___y_3835_ = v___y_3971_;
v___y_3836_ = v___y_3955_;
v___y_3837_ = v___y_3970_;
v___y_3838_ = v___y_3956_;
v___y_3839_ = v___y_3972_;
v___y_3840_ = v___y_3957_;
v___y_3841_ = v___y_3973_;
v___y_3842_ = v___y_3975_;
v___y_3843_ = v___y_3978_;
v___y_3844_ = v___y_3977_;
v___y_3845_ = v___y_3959_;
v___y_3846_ = v___x_3987_;
goto v___jp_3824_;
}
v___jp_3988_:
{
lean_object* v___x_4017_; double v___x_4018_; double v___x_4019_; double v___x_4020_; double v___x_4021_; double v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4017_ = lean_io_mono_nanos_now();
v___x_4018_ = lean_float_of_nat(v___y_3997_);
v___x_4019_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4020_ = lean_float_div(v___x_4018_, v___x_4019_);
v___x_4021_ = lean_float_of_nat(v___x_4017_);
v___x_4022_ = lean_float_div(v___x_4021_, v___x_4019_);
v___x_4023_ = lean_box_float(v___x_4020_);
v___x_4024_ = lean_box_float(v___x_4022_);
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4023_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v_a_4016_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
lean_inc_ref(v___y_3995_);
lean_inc(v___y_4008_);
v___x_4027_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_4008_, v___y_3999_, v___y_3995_, v___y_4013_, v___y_4004_, v___y_3989_, v___f_3950_, v___x_4026_, v___y_3990_, v___y_4005_, v___y_4012_, v___y_4010_, v___y_4011_, v___y_4006_, v___y_4001_, v___y_3998_, v___y_3994_, v___y_4007_, v___y_4014_, v___y_4002_, v___y_3996_, v___y_4015_);
v___y_3825_ = v___y_3998_;
v___y_3826_ = v___y_4000_;
v___y_3827_ = v___y_4001_;
v___y_3828_ = v___y_4002_;
v___y_3829_ = v___y_4003_;
v___y_3830_ = v___y_3990_;
v___y_3831_ = v___y_3991_;
v___y_3832_ = v___y_4005_;
v___y_3833_ = v___y_4006_;
v___y_3834_ = v___y_4007_;
v___y_3835_ = v___y_4009_;
v___y_3836_ = v___y_3992_;
v___y_3837_ = v___y_4008_;
v___y_3838_ = v___y_3993_;
v___y_3839_ = v___y_4010_;
v___y_3840_ = v___y_3994_;
v___y_3841_ = v___y_4011_;
v___y_3842_ = v___y_4012_;
v___y_3843_ = v___y_4015_;
v___y_3844_ = v___y_4014_;
v___y_3845_ = v___y_3996_;
v___y_3846_ = v___x_4027_;
goto v___jp_3824_;
}
v___jp_4028_:
{
lean_object* v___x_4055_; lean_object* v_a_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v___x_4055_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4054_);
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref(v___x_4055_);
v___x_4057_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4058_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4052_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = lean_io_mono_nanos_now();
v___x_4060_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4030_, v___y_4029_, v___y_4044_, v___y_4051_, v___y_4049_, v___y_4050_, v___y_4046_, v___y_4040_, v___y_4037_, v___y_4034_, v___y_4045_, v___y_4053_, v___y_4041_, v___y_4036_, v___y_4054_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
lean_ctor_set_tag(v___x_4063_, 1);
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
v___y_3989_ = v_a_4056_;
v___y_3990_ = v___y_4029_;
v___y_3991_ = v___y_4031_;
v___y_3992_ = v___y_4032_;
v___y_3993_ = v___y_4033_;
v___y_3994_ = v___y_4034_;
v___y_3995_ = v___y_4035_;
v___y_3996_ = v___y_4036_;
v___y_3997_ = v___x_4059_;
v___y_3998_ = v___y_4037_;
v___y_3999_ = v___y_4038_;
v___y_4000_ = v___y_4039_;
v___y_4001_ = v___y_4040_;
v___y_4002_ = v___y_4041_;
v___y_4003_ = v___y_4042_;
v___y_4004_ = v___y_4043_;
v___y_4005_ = v___y_4044_;
v___y_4006_ = v___y_4046_;
v___y_4007_ = v___y_4045_;
v___y_4008_ = v___y_4048_;
v___y_4009_ = v___y_4047_;
v___y_4010_ = v___y_4049_;
v___y_4011_ = v___y_4050_;
v___y_4012_ = v___y_4051_;
v___y_4013_ = v___y_4052_;
v___y_4014_ = v___y_4053_;
v___y_4015_ = v___y_4054_;
v_a_4016_ = v___x_4066_;
goto v___jp_3988_;
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
v_a_4069_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4060_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4060_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
lean_ctor_set_tag(v___x_4071_, 0);
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
v___y_3989_ = v_a_4056_;
v___y_3990_ = v___y_4029_;
v___y_3991_ = v___y_4031_;
v___y_3992_ = v___y_4032_;
v___y_3993_ = v___y_4033_;
v___y_3994_ = v___y_4034_;
v___y_3995_ = v___y_4035_;
v___y_3996_ = v___y_4036_;
v___y_3997_ = v___x_4059_;
v___y_3998_ = v___y_4037_;
v___y_3999_ = v___y_4038_;
v___y_4000_ = v___y_4039_;
v___y_4001_ = v___y_4040_;
v___y_4002_ = v___y_4041_;
v___y_4003_ = v___y_4042_;
v___y_4004_ = v___y_4043_;
v___y_4005_ = v___y_4044_;
v___y_4006_ = v___y_4046_;
v___y_4007_ = v___y_4045_;
v___y_4008_ = v___y_4048_;
v___y_4009_ = v___y_4047_;
v___y_4010_ = v___y_4049_;
v___y_4011_ = v___y_4050_;
v___y_4012_ = v___y_4051_;
v___y_4013_ = v___y_4052_;
v___y_4014_ = v___y_4053_;
v___y_4015_ = v___y_4054_;
v_a_4016_ = v___x_4074_;
goto v___jp_3988_;
}
}
}
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_io_get_num_heartbeats();
v___x_4078_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4030_, v___y_4029_, v___y_4044_, v___y_4051_, v___y_4049_, v___y_4050_, v___y_4046_, v___y_4040_, v___y_4037_, v___y_4034_, v___y_4045_, v___y_4053_, v___y_4041_, v___y_4036_, v___y_4054_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
lean_ctor_set_tag(v___x_4081_, 1);
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
v___y_3952_ = v_a_4056_;
v___y_3953_ = v___y_4029_;
v___y_3954_ = v___y_4031_;
v___y_3955_ = v___y_4032_;
v___y_3956_ = v___y_4033_;
v___y_3957_ = v___y_4034_;
v___y_3958_ = v___y_4035_;
v___y_3959_ = v___y_4036_;
v___y_3960_ = v___y_4037_;
v___y_3961_ = v___y_4038_;
v___y_3962_ = v___y_4039_;
v___y_3963_ = v___y_4040_;
v___y_3964_ = v___y_4041_;
v___y_3965_ = v___y_4042_;
v___y_3966_ = v___y_4043_;
v___y_3967_ = v___y_4044_;
v___y_3968_ = v___y_4046_;
v___y_3969_ = v___y_4045_;
v___y_3970_ = v___y_4048_;
v___y_3971_ = v___y_4047_;
v___y_3972_ = v___y_4049_;
v___y_3973_ = v___y_4050_;
v___y_3974_ = v___x_4077_;
v___y_3975_ = v___y_4051_;
v___y_3976_ = v___y_4052_;
v___y_3977_ = v___y_4053_;
v___y_3978_ = v___y_4054_;
v_a_3979_ = v___x_4084_;
goto v___jp_3951_;
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
v_a_4087_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4078_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4078_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
lean_ctor_set_tag(v___x_4089_, 0);
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
v___y_3952_ = v_a_4056_;
v___y_3953_ = v___y_4029_;
v___y_3954_ = v___y_4031_;
v___y_3955_ = v___y_4032_;
v___y_3956_ = v___y_4033_;
v___y_3957_ = v___y_4034_;
v___y_3958_ = v___y_4035_;
v___y_3959_ = v___y_4036_;
v___y_3960_ = v___y_4037_;
v___y_3961_ = v___y_4038_;
v___y_3962_ = v___y_4039_;
v___y_3963_ = v___y_4040_;
v___y_3964_ = v___y_4041_;
v___y_3965_ = v___y_4042_;
v___y_3966_ = v___y_4043_;
v___y_3967_ = v___y_4044_;
v___y_3968_ = v___y_4046_;
v___y_3969_ = v___y_4045_;
v___y_3970_ = v___y_4048_;
v___y_3971_ = v___y_4047_;
v___y_3972_ = v___y_4049_;
v___y_3973_ = v___y_4050_;
v___y_3974_ = v___x_4077_;
v___y_3975_ = v___y_4051_;
v___y_3976_ = v___y_4052_;
v___y_3977_ = v___y_4053_;
v___y_3978_ = v___y_4054_;
v_a_3979_ = v___x_4092_;
goto v___jp_3951_;
}
}
}
}
}
v___jp_4095_:
{
lean_object* v_toCold_4122_; lean_object* v_ref_4123_; lean_object* v___x_4124_; 
v_toCold_4122_ = lean_ctor_get(v___y_4104_, 0);
v_ref_4123_ = lean_ctor_get(v___y_4104_, 2);
lean_inc_ref(v___y_4097_);
v___x_4124_ = l_Lean_Cadical_Solver_assume(v___y_4097_, v___y_4103_, v___y_4121_);
lean_dec(v___y_4103_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_options_4125_; uint8_t v_hasTrace_4126_; 
lean_dec_ref_known(v___x_4124_, 1);
v_options_4125_ = lean_ctor_get(v_toCold_4122_, 2);
v_hasTrace_4126_ = lean_ctor_get_uint8(v_options_4125_, sizeof(void*)*1);
if (v_hasTrace_4126_ == 0)
{
lean_object* v___x_4127_; 
v___x_4127_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4097_, v___y_4096_, v___y_4111_, v___y_4118_, v___y_4116_, v___y_4117_, v___y_4112_, v___y_4108_, v___y_4105_, v___y_4101_, v___y_4113_, v___y_4119_, v___y_4109_, v___y_4104_, v___y_4120_);
v___y_3825_ = v___y_4105_;
v___y_3826_ = v___y_4107_;
v___y_3827_ = v___y_4108_;
v___y_3828_ = v___y_4109_;
v___y_3829_ = v___y_4110_;
v___y_3830_ = v___y_4096_;
v___y_3831_ = v___y_4098_;
v___y_3832_ = v___y_4111_;
v___y_3833_ = v___y_4112_;
v___y_3834_ = v___y_4113_;
v___y_3835_ = v___y_4114_;
v___y_3836_ = v___y_4099_;
v___y_3837_ = v___y_4115_;
v___y_3838_ = v___y_4100_;
v___y_3839_ = v___y_4116_;
v___y_3840_ = v___y_4101_;
v___y_3841_ = v___y_4117_;
v___y_3842_ = v___y_4118_;
v___y_3843_ = v___y_4120_;
v___y_3844_ = v___y_4119_;
v___y_3845_ = v___y_4104_;
v___y_3846_ = v___x_4127_;
goto v___jp_3824_;
}
else
{
lean_object* v_inheritedTraceOptions_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; 
v_inheritedTraceOptions_4128_ = lean_ctor_get(v_toCold_4122_, 11);
v___x_4129_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_4115_);
v___x_4130_ = l_Lean_Name_append(v___x_4129_, v___y_4115_);
v___x_4131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4128_, v_options_4125_, v___x_4130_);
lean_dec(v___x_4130_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; uint8_t v___x_4133_; 
v___x_4132_ = l_Lean_trace_profiler;
v___x_4133_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4125_, v___x_4132_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; 
v___x_4134_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4097_, v___y_4096_, v___y_4111_, v___y_4118_, v___y_4116_, v___y_4117_, v___y_4112_, v___y_4108_, v___y_4105_, v___y_4101_, v___y_4113_, v___y_4119_, v___y_4109_, v___y_4104_, v___y_4120_);
v___y_3825_ = v___y_4105_;
v___y_3826_ = v___y_4107_;
v___y_3827_ = v___y_4108_;
v___y_3828_ = v___y_4109_;
v___y_3829_ = v___y_4110_;
v___y_3830_ = v___y_4096_;
v___y_3831_ = v___y_4098_;
v___y_3832_ = v___y_4111_;
v___y_3833_ = v___y_4112_;
v___y_3834_ = v___y_4113_;
v___y_3835_ = v___y_4114_;
v___y_3836_ = v___y_4099_;
v___y_3837_ = v___y_4115_;
v___y_3838_ = v___y_4100_;
v___y_3839_ = v___y_4116_;
v___y_3840_ = v___y_4101_;
v___y_3841_ = v___y_4117_;
v___y_3842_ = v___y_4118_;
v___y_3843_ = v___y_4120_;
v___y_3844_ = v___y_4119_;
v___y_3845_ = v___y_4104_;
v___y_3846_ = v___x_4134_;
goto v___jp_3824_;
}
else
{
v___y_4029_ = v___y_4096_;
v___y_4030_ = v___y_4097_;
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___y_4099_;
v___y_4033_ = v___y_4100_;
v___y_4034_ = v___y_4101_;
v___y_4035_ = v___y_4102_;
v___y_4036_ = v___y_4104_;
v___y_4037_ = v___y_4105_;
v___y_4038_ = v___y_4106_;
v___y_4039_ = v___y_4107_;
v___y_4040_ = v___y_4108_;
v___y_4041_ = v___y_4109_;
v___y_4042_ = v___y_4110_;
v___y_4043_ = v___x_4131_;
v___y_4044_ = v___y_4111_;
v___y_4045_ = v___y_4113_;
v___y_4046_ = v___y_4112_;
v___y_4047_ = v___y_4114_;
v___y_4048_ = v___y_4115_;
v___y_4049_ = v___y_4116_;
v___y_4050_ = v___y_4117_;
v___y_4051_ = v___y_4118_;
v___y_4052_ = v_options_4125_;
v___y_4053_ = v___y_4119_;
v___y_4054_ = v___y_4120_;
goto v___jp_4028_;
}
}
else
{
v___y_4029_ = v___y_4096_;
v___y_4030_ = v___y_4097_;
v___y_4031_ = v___y_4098_;
v___y_4032_ = v___y_4099_;
v___y_4033_ = v___y_4100_;
v___y_4034_ = v___y_4101_;
v___y_4035_ = v___y_4102_;
v___y_4036_ = v___y_4104_;
v___y_4037_ = v___y_4105_;
v___y_4038_ = v___y_4106_;
v___y_4039_ = v___y_4107_;
v___y_4040_ = v___y_4108_;
v___y_4041_ = v___y_4109_;
v___y_4042_ = v___y_4110_;
v___y_4043_ = v___x_4131_;
v___y_4044_ = v___y_4111_;
v___y_4045_ = v___y_4113_;
v___y_4046_ = v___y_4112_;
v___y_4047_ = v___y_4114_;
v___y_4048_ = v___y_4115_;
v___y_4049_ = v___y_4116_;
v___y_4050_ = v___y_4117_;
v___y_4051_ = v___y_4118_;
v___y_4052_ = v_options_4125_;
v___y_4053_ = v___y_4119_;
v___y_4054_ = v___y_4120_;
goto v___jp_4028_;
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4146_; 
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
v_a_4135_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4137_ = v___x_4124_;
v_isShared_4138_ = v_isSharedCheck_4146_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4124_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4146_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4144_; 
v___x_4139_ = lean_io_error_to_string(v_a_4135_);
v___x_4140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4139_);
v___x_4141_ = l_Lean_MessageData_ofFormat(v___x_4140_);
lean_inc(v_ref_4123_);
v___x_4142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4142_, 0, v_ref_4123_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 0, v___x_4142_);
v___x_4144_ = v___x_4137_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
v___jp_4147_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v_theoryState_4178_; lean_object* v_satExpr_4179_; lean_object* v_hypQueue_4180_; lean_object* v_usedHyps_4181_; uint8_t v_didChange_4182_; lean_object* v_solverTimeBudgetMs_4183_; lean_object* v_roundBudget_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4227_; 
lean_inc_ref(v___y_4150_);
v___x_4176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4176_, 0, v___y_4150_);
lean_ctor_set(v___x_4176_, 1, v___y_4161_);
lean_ctor_set(v___x_4176_, 2, v___y_4151_);
v___x_4177_ = lean_st_ref_take(v___y_4163_);
v_theoryState_4178_ = lean_ctor_get(v___x_4177_, 3);
v_satExpr_4179_ = lean_ctor_get(v___x_4177_, 0);
v_hypQueue_4180_ = lean_ctor_get(v___x_4177_, 1);
v_usedHyps_4181_ = lean_ctor_get(v___x_4177_, 2);
v_didChange_4182_ = lean_ctor_get_uint8(v___x_4177_, sizeof(void*)*6);
v_solverTimeBudgetMs_4183_ = lean_ctor_get(v___x_4177_, 4);
v_roundBudget_4184_ = lean_ctor_get(v___x_4177_, 5);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4186_ = v___x_4177_;
v_isShared_4187_ = v_isSharedCheck_4227_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_roundBudget_4184_);
lean_inc(v_solverTimeBudgetMs_4183_);
lean_inc(v_theoryState_4178_);
lean_inc(v_usedHyps_4181_);
lean_inc(v_hypQueue_4180_);
lean_inc(v_satExpr_4179_);
lean_dec(v___x_4177_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4227_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v_funState_4188_; lean_object* v_preprocessCaches_4189_; lean_object* v_satSolver_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4225_; 
v_funState_4188_ = lean_ctor_get(v_theoryState_4178_, 0);
v_preprocessCaches_4189_ = lean_ctor_get(v_theoryState_4178_, 2);
v_satSolver_4190_ = lean_ctor_get(v_theoryState_4178_, 3);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_theoryState_4178_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; 
v_unused_4226_ = lean_ctor_get(v_theoryState_4178_, 1);
lean_dec(v_unused_4226_);
v___x_4192_ = v_theoryState_4178_;
v_isShared_4193_ = v_isSharedCheck_4225_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_satSolver_4190_);
lean_inc(v_preprocessCaches_4189_);
lean_inc(v_funState_4188_);
lean_dec(v_theoryState_4178_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4225_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 1, v___x_4176_);
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_funState_4188_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4224_, 2, v_preprocessCaches_4189_);
lean_ctor_set(v_reuseFailAlloc_4224_, 3, v_satSolver_4190_);
v___x_4195_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4197_; 
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 3, v___x_4195_);
v___x_4197_ = v___x_4186_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_satExpr_4179_);
lean_ctor_set(v_reuseFailAlloc_4223_, 1, v_hypQueue_4180_);
lean_ctor_set(v_reuseFailAlloc_4223_, 2, v_usedHyps_4181_);
lean_ctor_set(v_reuseFailAlloc_4223_, 3, v___x_4195_);
lean_ctor_set(v_reuseFailAlloc_4223_, 4, v_solverTimeBudgetMs_4183_);
lean_ctor_set(v_reuseFailAlloc_4223_, 5, v_roundBudget_4184_);
lean_ctor_set_uint8(v_reuseFailAlloc_4223_, sizeof(void*)*6, v_didChange_4182_);
v___x_4197_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = lean_st_ref_put(v___y_4163_, v___x_4197_);
v___x_4199_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_4160_, v___y_4148_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v___x_4200_; 
lean_dec_ref_known(v___x_4199_, 1);
v___x_4200_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_4163_);
if (lean_obj_tag(v___x_4200_) == 0)
{
uint8_t v_invert_4201_; 
v_invert_4201_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*1);
if (v_invert_4201_ == 0)
{
lean_object* v_a_4202_; lean_object* v_gate_4203_; 
v_a_4202_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4202_);
lean_dec_ref_known(v___x_4200_, 1);
v_gate_4203_ = lean_ctor_get(v___y_4153_, 0);
lean_inc(v_gate_4203_);
lean_dec_ref(v___y_4153_);
v___y_4096_ = v___y_4162_;
v___y_4097_ = v_a_4202_;
v___y_4098_ = v___y_4154_;
v___y_4099_ = v___y_4156_;
v___y_4100_ = v___y_4158_;
v___y_4101_ = v___y_4170_;
v___y_4102_ = v___y_4159_;
v___y_4103_ = v_gate_4203_;
v___y_4104_ = v___y_4174_;
v___y_4105_ = v___y_4169_;
v___y_4106_ = v___y_4149_;
v___y_4107_ = v___y_4150_;
v___y_4108_ = v___y_4168_;
v___y_4109_ = v___y_4173_;
v___y_4110_ = v___y_4152_;
v___y_4111_ = v___y_4163_;
v___y_4112_ = v___y_4167_;
v___y_4113_ = v___y_4171_;
v___y_4114_ = v___y_4155_;
v___y_4115_ = v___y_4157_;
v___y_4116_ = v___y_4165_;
v___y_4117_ = v___y_4166_;
v___y_4118_ = v___y_4164_;
v___y_4119_ = v___y_4172_;
v___y_4120_ = v___y_4175_;
v___y_4121_ = v___y_4149_;
goto v___jp_4095_;
}
else
{
lean_object* v_a_4204_; lean_object* v_gate_4205_; uint8_t v___x_4206_; 
v_a_4204_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4200_, 1);
v_gate_4205_ = lean_ctor_get(v___y_4153_, 0);
lean_inc(v_gate_4205_);
lean_dec_ref(v___y_4153_);
v___x_4206_ = 0;
v___y_4096_ = v___y_4162_;
v___y_4097_ = v_a_4204_;
v___y_4098_ = v___y_4154_;
v___y_4099_ = v___y_4156_;
v___y_4100_ = v___y_4158_;
v___y_4101_ = v___y_4170_;
v___y_4102_ = v___y_4159_;
v___y_4103_ = v_gate_4205_;
v___y_4104_ = v___y_4174_;
v___y_4105_ = v___y_4169_;
v___y_4106_ = v___y_4149_;
v___y_4107_ = v___y_4150_;
v___y_4108_ = v___y_4168_;
v___y_4109_ = v___y_4173_;
v___y_4110_ = v___y_4152_;
v___y_4111_ = v___y_4163_;
v___y_4112_ = v___y_4167_;
v___y_4113_ = v___y_4171_;
v___y_4114_ = v___y_4155_;
v___y_4115_ = v___y_4157_;
v___y_4116_ = v___y_4165_;
v___y_4117_ = v___y_4166_;
v___y_4118_ = v___y_4164_;
v___y_4119_ = v___y_4172_;
v___y_4120_ = v___y_4175_;
v___y_4121_ = v___x_4206_;
goto v___jp_4095_;
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v___y_4158_);
lean_dec(v___y_4156_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v___y_4150_);
v_a_4207_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4200_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4200_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec(v___y_4158_);
lean_dec(v___y_4156_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v___y_4150_);
v_a_4215_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4199_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4199_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
}
}
}
v___jp_4233_:
{
if (lean_obj_tag(v___y_4260_) == 0)
{
lean_object* v_a_4261_; lean_object* v_toCold_4262_; lean_object* v_options_4263_; uint8_t v_hasTrace_4264_; 
v_a_4261_ = lean_ctor_get(v___y_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___y_4260_, 1);
v_toCold_4262_ = lean_ctor_get(v___y_4236_, 0);
v_options_4263_ = lean_ctor_get(v_toCold_4262_, 2);
v_hasTrace_4264_ = lean_ctor_get_uint8(v_options_4263_, sizeof(void*)*1);
if (v_hasTrace_4264_ == 0)
{
lean_object* v_cnf_4265_; 
v_cnf_4265_ = lean_ctor_get(v_a_4261_, 0);
lean_inc_ref(v_cnf_4265_);
v___y_4148_ = v_cnf_4265_;
v___y_4149_ = v___y_4248_;
v___y_4150_ = v___y_4247_;
v___y_4151_ = v_a_4261_;
v___y_4152_ = v___y_4249_;
v___y_4153_ = v___y_4240_;
v___y_4154_ = v___y_4241_;
v___y_4155_ = v___y_4252_;
v___y_4156_ = v___y_4242_;
v___y_4157_ = v___y_4251_;
v___y_4158_ = v___y_4243_;
v___y_4159_ = v___y_4244_;
v___y_4160_ = v___y_4255_;
v___y_4161_ = v___y_4259_;
v___y_4162_ = v___y_4237_;
v___y_4163_ = v___y_4234_;
v___y_4164_ = v___y_4235_;
v___y_4165_ = v___y_4250_;
v___y_4166_ = v___y_4253_;
v___y_4167_ = v___y_4257_;
v___y_4168_ = v___y_4246_;
v___y_4169_ = v___y_4238_;
v___y_4170_ = v___y_4254_;
v___y_4171_ = v___y_4245_;
v___y_4172_ = v___y_4258_;
v___y_4173_ = v___y_4239_;
v___y_4174_ = v___y_4236_;
v___y_4175_ = v___y_4256_;
goto v___jp_4147_;
}
else
{
lean_object* v_cnf_4266_; lean_object* v_inheritedTraceOptions_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v_cnf_4266_ = lean_ctor_get(v_a_4261_, 0);
lean_inc_ref(v_cnf_4266_);
v_inheritedTraceOptions_4267_ = lean_ctor_get(v_toCold_4262_, 11);
v___x_4268_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4269_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4267_, v_options_4263_, v___x_4268_);
if (v___x_4269_ == 0)
{
v___y_4148_ = v_cnf_4266_;
v___y_4149_ = v___y_4248_;
v___y_4150_ = v___y_4247_;
v___y_4151_ = v_a_4261_;
v___y_4152_ = v___y_4249_;
v___y_4153_ = v___y_4240_;
v___y_4154_ = v___y_4241_;
v___y_4155_ = v___y_4252_;
v___y_4156_ = v___y_4242_;
v___y_4157_ = v___y_4251_;
v___y_4158_ = v___y_4243_;
v___y_4159_ = v___y_4244_;
v___y_4160_ = v___y_4255_;
v___y_4161_ = v___y_4259_;
v___y_4162_ = v___y_4237_;
v___y_4163_ = v___y_4234_;
v___y_4164_ = v___y_4235_;
v___y_4165_ = v___y_4250_;
v___y_4166_ = v___y_4253_;
v___y_4167_ = v___y_4257_;
v___y_4168_ = v___y_4246_;
v___y_4169_ = v___y_4238_;
v___y_4170_ = v___y_4254_;
v___y_4171_ = v___y_4245_;
v___y_4172_ = v___y_4258_;
v___y_4173_ = v___y_4239_;
v___y_4174_ = v___y_4236_;
v___y_4175_ = v___y_4256_;
goto v___jp_4147_;
}
else
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4270_ = lean_array_get_size(v_cnf_4266_);
v___x_4271_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_4272_ = l_Nat_reprFast(v___x_4270_);
v___x_4273_ = lean_string_append(v___x_4271_, v___x_4272_);
lean_dec_ref(v___x_4272_);
v___x_4274_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_4275_ = lean_string_append(v___x_4273_, v___x_4274_);
v___x_4276_ = lean_nat_sub(v___x_4270_, v___y_4255_);
v___x_4277_ = l_Nat_reprFast(v___x_4276_);
v___x_4278_ = lean_string_append(v___x_4275_, v___x_4277_);
lean_dec_ref(v___x_4277_);
v___x_4279_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_4280_ = lean_string_append(v___x_4278_, v___x_4279_);
v___x_4281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
v___x_4282_ = l_Lean_MessageData_ofFormat(v___x_4281_);
v___x_4283_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4232_, v___x_4282_, v___y_4258_, v___y_4239_, v___y_4236_, v___y_4256_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_dec_ref_known(v___x_4283_, 1);
v___y_4148_ = v_cnf_4266_;
v___y_4149_ = v___y_4248_;
v___y_4150_ = v___y_4247_;
v___y_4151_ = v_a_4261_;
v___y_4152_ = v___y_4249_;
v___y_4153_ = v___y_4240_;
v___y_4154_ = v___y_4241_;
v___y_4155_ = v___y_4252_;
v___y_4156_ = v___y_4242_;
v___y_4157_ = v___y_4251_;
v___y_4158_ = v___y_4243_;
v___y_4159_ = v___y_4244_;
v___y_4160_ = v___y_4255_;
v___y_4161_ = v___y_4259_;
v___y_4162_ = v___y_4237_;
v___y_4163_ = v___y_4234_;
v___y_4164_ = v___y_4235_;
v___y_4165_ = v___y_4250_;
v___y_4166_ = v___y_4253_;
v___y_4167_ = v___y_4257_;
v___y_4168_ = v___y_4246_;
v___y_4169_ = v___y_4238_;
v___y_4170_ = v___y_4254_;
v___y_4171_ = v___y_4245_;
v___y_4172_ = v___y_4258_;
v___y_4173_ = v___y_4239_;
v___y_4174_ = v___y_4236_;
v___y_4175_ = v___y_4256_;
goto v___jp_4147_;
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v_cnf_4266_);
lean_dec(v_a_4261_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4283_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4283_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
v_a_4292_ = lean_ctor_get(v___y_4260_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___y_4260_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___y_4260_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___y_4260_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
v___jp_4300_:
{
lean_object* v___x_4332_; double v___x_4333_; double v___x_4334_; double v___x_4335_; double v___x_4336_; double v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4332_ = lean_io_mono_nanos_now();
v___x_4333_ = lean_float_of_nat(v___y_4309_);
v___x_4334_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4335_ = lean_float_div(v___x_4333_, v___x_4334_);
v___x_4336_ = lean_float_of_nat(v___x_4332_);
v___x_4337_ = lean_float_div(v___x_4336_, v___x_4334_);
v___x_4338_ = lean_box_float(v___x_4335_);
v___x_4339_ = lean_box_float(v___x_4337_);
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4341_, 0, v_a_4331_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
lean_inc_ref(v___y_4312_);
lean_inc(v___y_4322_);
v___x_4342_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_4322_, v___y_4317_, v___y_4312_, v___y_4321_, v___y_4324_, v___y_4316_, v___f_3949_, v___x_4341_, v___y_4303_, v___y_4301_, v___y_4302_, v___y_4319_, v___y_4323_, v___y_4328_, v___y_4314_, v___y_4305_, v___y_4325_, v___y_4313_, v___y_4329_, v___y_4306_, v___y_4304_, v___y_4327_);
v___y_4234_ = v___y_4301_;
v___y_4235_ = v___y_4302_;
v___y_4236_ = v___y_4304_;
v___y_4237_ = v___y_4303_;
v___y_4238_ = v___y_4305_;
v___y_4239_ = v___y_4306_;
v___y_4240_ = v___y_4307_;
v___y_4241_ = v___y_4308_;
v___y_4242_ = v___y_4310_;
v___y_4243_ = v___y_4311_;
v___y_4244_ = v___y_4312_;
v___y_4245_ = v___y_4313_;
v___y_4246_ = v___y_4314_;
v___y_4247_ = v___y_4315_;
v___y_4248_ = v___y_4317_;
v___y_4249_ = v___y_4318_;
v___y_4250_ = v___y_4319_;
v___y_4251_ = v___y_4322_;
v___y_4252_ = v___y_4320_;
v___y_4253_ = v___y_4323_;
v___y_4254_ = v___y_4325_;
v___y_4255_ = v___y_4326_;
v___y_4256_ = v___y_4327_;
v___y_4257_ = v___y_4328_;
v___y_4258_ = v___y_4329_;
v___y_4259_ = v___y_4330_;
v___y_4260_ = v___x_4342_;
goto v___jp_4233_;
}
v___jp_4343_:
{
lean_object* v___x_4375_; double v___x_4376_; double v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4375_ = lean_io_get_num_heartbeats();
v___x_4376_ = lean_float_of_nat(v___y_4357_);
v___x_4377_ = lean_float_of_nat(v___x_4375_);
v___x_4378_ = lean_box_float(v___x_4376_);
v___x_4379_ = lean_box_float(v___x_4377_);
v___x_4380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4378_);
lean_ctor_set(v___x_4380_, 1, v___x_4379_);
v___x_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4381_, 0, v_a_4374_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
lean_inc_ref(v___y_4354_);
lean_inc(v___y_4365_);
v___x_4382_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_4365_, v___y_4360_, v___y_4354_, v___y_4364_, v___y_4367_, v___y_4359_, v___f_3949_, v___x_4381_, v___y_4346_, v___y_4344_, v___y_4345_, v___y_4362_, v___y_4366_, v___y_4371_, v___y_4356_, v___y_4348_, v___y_4368_, v___y_4355_, v___y_4372_, v___y_4349_, v___y_4347_, v___y_4370_);
v___y_4234_ = v___y_4344_;
v___y_4235_ = v___y_4345_;
v___y_4236_ = v___y_4347_;
v___y_4237_ = v___y_4346_;
v___y_4238_ = v___y_4348_;
v___y_4239_ = v___y_4349_;
v___y_4240_ = v___y_4350_;
v___y_4241_ = v___y_4351_;
v___y_4242_ = v___y_4352_;
v___y_4243_ = v___y_4353_;
v___y_4244_ = v___y_4354_;
v___y_4245_ = v___y_4355_;
v___y_4246_ = v___y_4356_;
v___y_4247_ = v___y_4358_;
v___y_4248_ = v___y_4360_;
v___y_4249_ = v___y_4361_;
v___y_4250_ = v___y_4362_;
v___y_4251_ = v___y_4365_;
v___y_4252_ = v___y_4363_;
v___y_4253_ = v___y_4366_;
v___y_4254_ = v___y_4368_;
v___y_4255_ = v___y_4369_;
v___y_4256_ = v___y_4370_;
v___y_4257_ = v___y_4371_;
v___y_4258_ = v___y_4372_;
v___y_4259_ = v___y_4373_;
v___y_4260_ = v___x_4382_;
goto v___jp_4233_;
}
v___jp_4383_:
{
lean_object* v___x_4414_; lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4469_; 
v___x_4414_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4410_);
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4417_ = v___x_4414_;
v_isShared_4418_ = v_isSharedCheck_4469_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4414_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4469_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; uint8_t v___x_4420_; 
v___x_4419_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4420_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4404_, v___x_4419_);
if (v___x_4420_ == 0)
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = lean_io_mono_nanos_now();
v___x_4422_ = l_IO_lazyPure___redArg(v___y_4400_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_del_object(v___x_4417_);
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
lean_ctor_set_tag(v___x_4425_, 1);
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
v___y_4301_ = v___y_4384_;
v___y_4302_ = v___y_4385_;
v___y_4303_ = v___y_4387_;
v___y_4304_ = v___y_4386_;
v___y_4305_ = v___y_4389_;
v___y_4306_ = v___y_4388_;
v___y_4307_ = v___y_4390_;
v___y_4308_ = v___y_4391_;
v___y_4309_ = v___x_4421_;
v___y_4310_ = v___y_4392_;
v___y_4311_ = v___y_4393_;
v___y_4312_ = v___y_4395_;
v___y_4313_ = v___y_4396_;
v___y_4314_ = v___y_4397_;
v___y_4315_ = v___y_4398_;
v___y_4316_ = v_a_4415_;
v___y_4317_ = v___y_4399_;
v___y_4318_ = v___y_4402_;
v___y_4319_ = v___y_4401_;
v___y_4320_ = v___y_4405_;
v___y_4321_ = v___y_4404_;
v___y_4322_ = v___y_4403_;
v___y_4323_ = v___y_4407_;
v___y_4324_ = v___y_4406_;
v___y_4325_ = v___y_4408_;
v___y_4326_ = v___y_4409_;
v___y_4327_ = v___y_4410_;
v___y_4328_ = v___y_4411_;
v___y_4329_ = v___y_4412_;
v___y_4330_ = v___y_4413_;
v_a_4331_ = v___x_4428_;
goto v___jp_4300_;
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4444_; 
v_a_4431_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4433_ = v___x_4422_;
v_isShared_4434_ = v_isSharedCheck_4444_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4422_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4444_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4435_ = lean_io_error_to_string(v_a_4431_);
if (v_isShared_4434_ == 0)
{
lean_ctor_set_tag(v___x_4433_, 3);
lean_ctor_set(v___x_4433_, 0, v___x_4435_);
v___x_4437_ = v___x_4433_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4441_; 
v___x_4438_ = l_Lean_MessageData_ofFormat(v___x_4437_);
lean_inc(v___y_4394_);
v___x_4439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4439_, 0, v___y_4394_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4439_);
v___x_4441_ = v___x_4417_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4439_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
v___y_4301_ = v___y_4384_;
v___y_4302_ = v___y_4385_;
v___y_4303_ = v___y_4387_;
v___y_4304_ = v___y_4386_;
v___y_4305_ = v___y_4389_;
v___y_4306_ = v___y_4388_;
v___y_4307_ = v___y_4390_;
v___y_4308_ = v___y_4391_;
v___y_4309_ = v___x_4421_;
v___y_4310_ = v___y_4392_;
v___y_4311_ = v___y_4393_;
v___y_4312_ = v___y_4395_;
v___y_4313_ = v___y_4396_;
v___y_4314_ = v___y_4397_;
v___y_4315_ = v___y_4398_;
v___y_4316_ = v_a_4415_;
v___y_4317_ = v___y_4399_;
v___y_4318_ = v___y_4402_;
v___y_4319_ = v___y_4401_;
v___y_4320_ = v___y_4405_;
v___y_4321_ = v___y_4404_;
v___y_4322_ = v___y_4403_;
v___y_4323_ = v___y_4407_;
v___y_4324_ = v___y_4406_;
v___y_4325_ = v___y_4408_;
v___y_4326_ = v___y_4409_;
v___y_4327_ = v___y_4410_;
v___y_4328_ = v___y_4411_;
v___y_4329_ = v___y_4412_;
v___y_4330_ = v___y_4413_;
v_a_4331_ = v___x_4441_;
goto v___jp_4300_;
}
}
}
}
}
else
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = lean_io_get_num_heartbeats();
v___x_4446_ = l_IO_lazyPure___redArg(v___y_4400_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_del_object(v___x_4417_);
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set_tag(v___x_4449_, 1);
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
v___y_4344_ = v___y_4384_;
v___y_4345_ = v___y_4385_;
v___y_4346_ = v___y_4387_;
v___y_4347_ = v___y_4386_;
v___y_4348_ = v___y_4389_;
v___y_4349_ = v___y_4388_;
v___y_4350_ = v___y_4390_;
v___y_4351_ = v___y_4391_;
v___y_4352_ = v___y_4392_;
v___y_4353_ = v___y_4393_;
v___y_4354_ = v___y_4395_;
v___y_4355_ = v___y_4396_;
v___y_4356_ = v___y_4397_;
v___y_4357_ = v___x_4445_;
v___y_4358_ = v___y_4398_;
v___y_4359_ = v_a_4415_;
v___y_4360_ = v___y_4399_;
v___y_4361_ = v___y_4402_;
v___y_4362_ = v___y_4401_;
v___y_4363_ = v___y_4405_;
v___y_4364_ = v___y_4404_;
v___y_4365_ = v___y_4403_;
v___y_4366_ = v___y_4407_;
v___y_4367_ = v___y_4406_;
v___y_4368_ = v___y_4408_;
v___y_4369_ = v___y_4409_;
v___y_4370_ = v___y_4410_;
v___y_4371_ = v___y_4411_;
v___y_4372_ = v___y_4412_;
v___y_4373_ = v___y_4413_;
v_a_4374_ = v___x_4452_;
goto v___jp_4343_;
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4468_; 
v_a_4455_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4457_ = v___x_4446_;
v_isShared_4458_ = v_isSharedCheck_4468_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4446_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4468_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4459_; lean_object* v___x_4461_; 
v___x_4459_ = lean_io_error_to_string(v_a_4455_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set_tag(v___x_4457_, 3);
lean_ctor_set(v___x_4457_, 0, v___x_4459_);
v___x_4461_ = v___x_4457_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4459_);
v___x_4461_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4462_ = l_Lean_MessageData_ofFormat(v___x_4461_);
lean_inc(v___y_4394_);
v___x_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___y_4394_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4463_);
v___x_4465_ = v___x_4417_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
v___y_4344_ = v___y_4384_;
v___y_4345_ = v___y_4385_;
v___y_4346_ = v___y_4387_;
v___y_4347_ = v___y_4386_;
v___y_4348_ = v___y_4389_;
v___y_4349_ = v___y_4388_;
v___y_4350_ = v___y_4390_;
v___y_4351_ = v___y_4391_;
v___y_4352_ = v___y_4392_;
v___y_4353_ = v___y_4393_;
v___y_4354_ = v___y_4395_;
v___y_4355_ = v___y_4396_;
v___y_4356_ = v___y_4397_;
v___y_4357_ = v___x_4445_;
v___y_4358_ = v___y_4398_;
v___y_4359_ = v_a_4415_;
v___y_4360_ = v___y_4399_;
v___y_4361_ = v___y_4402_;
v___y_4362_ = v___y_4401_;
v___y_4363_ = v___y_4405_;
v___y_4364_ = v___y_4404_;
v___y_4365_ = v___y_4403_;
v___y_4366_ = v___y_4407_;
v___y_4367_ = v___y_4406_;
v___y_4368_ = v___y_4408_;
v___y_4369_ = v___y_4409_;
v___y_4370_ = v___y_4410_;
v___y_4371_ = v___y_4411_;
v___y_4372_ = v___y_4412_;
v___y_4373_ = v___y_4413_;
v_a_4374_ = v___x_4465_;
goto v___jp_4343_;
}
}
}
}
}
}
}
v___jp_4470_:
{
lean_object* v_toCold_4497_; lean_object* v_options_4498_; lean_object* v_cnf_4499_; lean_object* v_ref_4500_; lean_object* v_inheritedTraceOptions_4501_; uint8_t v_hasTrace_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___f_4506_; lean_object* v___x_4507_; 
v_toCold_4497_ = lean_ctor_get(v___y_4495_, 0);
v_options_4498_ = lean_ctor_get(v_toCold_4497_, 2);
v_cnf_4499_ = lean_ctor_get(v___y_4478_, 0);
v_ref_4500_ = lean_ctor_get(v___y_4495_, 2);
v_inheritedTraceOptions_4501_ = lean_ctor_get(v_toCold_4497_, 11);
v_hasTrace_4502_ = lean_ctor_get_uint8(v_options_4498_, sizeof(void*)*1);
v___x_4503_ = lean_array_get_size(v_cnf_4499_);
v___x_4504_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_4505_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v___y_4477_, v___y_4478_);
v___f_4506_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_4506_, 0, v___x_4229_);
lean_closure_set(v___f_4506_, 1, v___x_4504_);
lean_closure_set(v___f_4506_, 2, v___y_4471_);
lean_closure_set(v___f_4506_, 3, v___x_4505_);
v___x_4507_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9));
if (v_hasTrace_4502_ == 0)
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_4506_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
v___y_4234_ = v___y_4484_;
v___y_4235_ = v___y_4485_;
v___y_4236_ = v___y_4495_;
v___y_4237_ = v___y_4483_;
v___y_4238_ = v___y_4490_;
v___y_4239_ = v___y_4494_;
v___y_4240_ = v___y_4480_;
v___y_4241_ = v___y_4481_;
v___y_4242_ = v___y_4473_;
v___y_4243_ = v___y_4474_;
v___y_4244_ = v___y_4476_;
v___y_4245_ = v___y_4492_;
v___y_4246_ = v___y_4489_;
v___y_4247_ = v___y_4477_;
v___y_4248_ = v___y_4475_;
v___y_4249_ = v___y_4479_;
v___y_4250_ = v___y_4486_;
v___y_4251_ = v___x_4507_;
v___y_4252_ = v___y_4472_;
v___y_4253_ = v___y_4487_;
v___y_4254_ = v___y_4491_;
v___y_4255_ = v___x_4503_;
v___y_4256_ = v___y_4496_;
v___y_4257_ = v___y_4488_;
v___y_4258_ = v___y_4493_;
v___y_4259_ = v___y_4482_;
v___y_4260_ = v___x_4508_;
goto v___jp_4233_;
}
else
{
lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4509_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10);
v___x_4510_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4501_, v_options_4498_, v___x_4509_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4511_ = l_Lean_trace_profiler;
v___x_4512_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4498_, v___x_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_4506_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
v___y_4234_ = v___y_4484_;
v___y_4235_ = v___y_4485_;
v___y_4236_ = v___y_4495_;
v___y_4237_ = v___y_4483_;
v___y_4238_ = v___y_4490_;
v___y_4239_ = v___y_4494_;
v___y_4240_ = v___y_4480_;
v___y_4241_ = v___y_4481_;
v___y_4242_ = v___y_4473_;
v___y_4243_ = v___y_4474_;
v___y_4244_ = v___y_4476_;
v___y_4245_ = v___y_4492_;
v___y_4246_ = v___y_4489_;
v___y_4247_ = v___y_4477_;
v___y_4248_ = v___y_4475_;
v___y_4249_ = v___y_4479_;
v___y_4250_ = v___y_4486_;
v___y_4251_ = v___x_4507_;
v___y_4252_ = v___y_4472_;
v___y_4253_ = v___y_4487_;
v___y_4254_ = v___y_4491_;
v___y_4255_ = v___x_4503_;
v___y_4256_ = v___y_4496_;
v___y_4257_ = v___y_4488_;
v___y_4258_ = v___y_4493_;
v___y_4259_ = v___y_4482_;
v___y_4260_ = v___x_4513_;
goto v___jp_4233_;
}
else
{
v___y_4384_ = v___y_4484_;
v___y_4385_ = v___y_4485_;
v___y_4386_ = v___y_4495_;
v___y_4387_ = v___y_4483_;
v___y_4388_ = v___y_4494_;
v___y_4389_ = v___y_4490_;
v___y_4390_ = v___y_4480_;
v___y_4391_ = v___y_4481_;
v___y_4392_ = v___y_4473_;
v___y_4393_ = v___y_4474_;
v___y_4394_ = v_ref_4500_;
v___y_4395_ = v___y_4476_;
v___y_4396_ = v___y_4492_;
v___y_4397_ = v___y_4489_;
v___y_4398_ = v___y_4477_;
v___y_4399_ = v___y_4475_;
v___y_4400_ = v___f_4506_;
v___y_4401_ = v___y_4486_;
v___y_4402_ = v___y_4479_;
v___y_4403_ = v___x_4507_;
v___y_4404_ = v_options_4498_;
v___y_4405_ = v___y_4472_;
v___y_4406_ = v___x_4510_;
v___y_4407_ = v___y_4487_;
v___y_4408_ = v___y_4491_;
v___y_4409_ = v___x_4503_;
v___y_4410_ = v___y_4496_;
v___y_4411_ = v___y_4488_;
v___y_4412_ = v___y_4493_;
v___y_4413_ = v___y_4482_;
goto v___jp_4383_;
}
}
else
{
v___y_4384_ = v___y_4484_;
v___y_4385_ = v___y_4485_;
v___y_4386_ = v___y_4495_;
v___y_4387_ = v___y_4483_;
v___y_4388_ = v___y_4494_;
v___y_4389_ = v___y_4490_;
v___y_4390_ = v___y_4480_;
v___y_4391_ = v___y_4481_;
v___y_4392_ = v___y_4473_;
v___y_4393_ = v___y_4474_;
v___y_4394_ = v_ref_4500_;
v___y_4395_ = v___y_4476_;
v___y_4396_ = v___y_4492_;
v___y_4397_ = v___y_4489_;
v___y_4398_ = v___y_4477_;
v___y_4399_ = v___y_4475_;
v___y_4400_ = v___f_4506_;
v___y_4401_ = v___y_4486_;
v___y_4402_ = v___y_4479_;
v___y_4403_ = v___x_4507_;
v___y_4404_ = v_options_4498_;
v___y_4405_ = v___y_4472_;
v___y_4406_ = v___x_4510_;
v___y_4407_ = v___y_4487_;
v___y_4408_ = v___y_4491_;
v___y_4409_ = v___x_4503_;
v___y_4410_ = v___y_4496_;
v___y_4411_ = v___y_4488_;
v___y_4412_ = v___y_4493_;
v___y_4413_ = v___y_4482_;
goto v___jp_4383_;
}
}
}
v___jp_4514_:
{
lean_object* v_config_4542_; uint8_t v_graphviz_4543_; 
v_config_4542_ = lean_ctor_get(v___y_4518_, 5);
v_graphviz_4543_ = lean_ctor_get_uint8(v_config_4542_, sizeof(void*)*3 + 8);
if (v_graphviz_4543_ == 0)
{
lean_dec_ref(v___y_4516_);
v___y_4471_ = v___y_4515_;
v___y_4472_ = v___y_4518_;
v___y_4473_ = v___y_4517_;
v___y_4474_ = v___y_4519_;
v___y_4475_ = v___y_4522_;
v___y_4476_ = v___y_4521_;
v___y_4477_ = v___y_4520_;
v___y_4478_ = v___y_4523_;
v___y_4479_ = v___y_4524_;
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
goto v___jp_4470_;
}
else
{
lean_object* v_ref_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
v_ref_4544_ = lean_ctor_get(v___y_4540_, 2);
v___x_4545_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
v___x_4546_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v___y_4516_);
v___x_4547_ = l_IO_FS_writeFile(v___x_4545_, v___x_4546_);
lean_dec_ref(v___x_4546_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_dec_ref_known(v___x_4547_, 1);
v___y_4471_ = v___y_4515_;
v___y_4472_ = v___y_4518_;
v___y_4473_ = v___y_4517_;
v___y_4474_ = v___y_4519_;
v___y_4475_ = v___y_4522_;
v___y_4476_ = v___y_4521_;
v___y_4477_ = v___y_4520_;
v___y_4478_ = v___y_4523_;
v___y_4479_ = v___y_4524_;
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
goto v___jp_4470_;
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4559_; 
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec_ref(v___y_4523_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4515_);
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4550_ = v___x_4547_;
v_isShared_4551_ = v_isSharedCheck_4559_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4547_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4559_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4557_; 
v___x_4552_ = lean_io_error_to_string(v_a_4548_);
v___x_4553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
v___x_4554_ = l_Lean_MessageData_ofFormat(v___x_4553_);
lean_inc(v_ref_4544_);
v___x_4555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4555_, 0, v_ref_4544_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4555_);
v___x_4557_ = v___x_4550_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
v___jp_4560_:
{
if (lean_obj_tag(v___y_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v_result_4585_; lean_object* v_aig_4586_; lean_object* v_toCold_4587_; lean_object* v_options_4588_; lean_object* v_cache_4589_; lean_object* v_ref_4590_; lean_object* v_decls_4591_; lean_object* v_inheritedTraceOptions_4592_; uint8_t v_hasTrace_4593_; lean_object* v___x_4594_; 
v_a_4584_ = lean_ctor_get(v___y_4583_, 0);
lean_inc(v_a_4584_);
lean_dec_ref_known(v___y_4583_, 1);
v_result_4585_ = lean_ctor_get(v_a_4584_, 0);
lean_inc_ref(v_result_4585_);
v_aig_4586_ = lean_ctor_get(v_result_4585_, 0);
lean_inc_ref(v_aig_4586_);
v_toCold_4587_ = lean_ctor_get(v___y_4563_, 0);
v_options_4588_ = lean_ctor_get(v_toCold_4587_, 2);
v_cache_4589_ = lean_ctor_get(v_a_4584_, 1);
lean_inc_ref(v_cache_4589_);
lean_dec(v_a_4584_);
v_ref_4590_ = lean_ctor_get(v_result_4585_, 1);
lean_inc_ref(v_ref_4590_);
v_decls_4591_ = lean_ctor_get(v_aig_4586_, 0);
v_inheritedTraceOptions_4592_ = lean_ctor_get(v_toCold_4587_, 11);
v_hasTrace_4593_ = lean_ctor_get_uint8(v_options_4588_, sizeof(void*)*1);
v___x_4594_ = lean_array_get_size(v_decls_4591_);
if (v_hasTrace_4593_ == 0)
{
lean_dec(v___y_4572_);
lean_inc_ref(v_result_4585_);
v___y_4515_ = v_result_4585_;
v___y_4516_ = v_result_4585_;
v___y_4517_ = v___y_4570_;
v___y_4518_ = v___y_4569_;
v___y_4519_ = v___x_4594_;
v___y_4520_ = v_aig_4586_;
v___y_4521_ = v___y_4571_;
v___y_4522_ = v___y_4561_;
v___y_4523_ = v___y_4575_;
v___y_4524_ = v___y_4566_;
v___y_4525_ = v_ref_4590_;
v___y_4526_ = v___y_4568_;
v___y_4527_ = v_cache_4589_;
v___y_4528_ = v___y_4580_;
v___y_4529_ = v___y_4564_;
v___y_4530_ = v___y_4581_;
v___y_4531_ = v___y_4582_;
v___y_4532_ = v___y_4576_;
v___y_4533_ = v___y_4579_;
v___y_4534_ = v___y_4577_;
v___y_4535_ = v___y_4574_;
v___y_4536_ = v___y_4562_;
v___y_4537_ = v___y_4567_;
v___y_4538_ = v___y_4578_;
v___y_4539_ = v___y_4565_;
v___y_4540_ = v___y_4563_;
v___y_4541_ = v___y_4573_;
goto v___jp_4514_;
}
else
{
lean_object* v___x_4595_; uint8_t v___x_4596_; 
v___x_4595_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4596_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4592_, v_options_4588_, v___x_4595_);
if (v___x_4596_ == 0)
{
lean_dec(v___y_4572_);
lean_inc_ref(v_result_4585_);
v___y_4515_ = v_result_4585_;
v___y_4516_ = v_result_4585_;
v___y_4517_ = v___y_4570_;
v___y_4518_ = v___y_4569_;
v___y_4519_ = v___x_4594_;
v___y_4520_ = v_aig_4586_;
v___y_4521_ = v___y_4571_;
v___y_4522_ = v___y_4561_;
v___y_4523_ = v___y_4575_;
v___y_4524_ = v___y_4566_;
v___y_4525_ = v_ref_4590_;
v___y_4526_ = v___y_4568_;
v___y_4527_ = v_cache_4589_;
v___y_4528_ = v___y_4580_;
v___y_4529_ = v___y_4564_;
v___y_4530_ = v___y_4581_;
v___y_4531_ = v___y_4582_;
v___y_4532_ = v___y_4576_;
v___y_4533_ = v___y_4579_;
v___y_4534_ = v___y_4577_;
v___y_4535_ = v___y_4574_;
v___y_4536_ = v___y_4562_;
v___y_4537_ = v___y_4567_;
v___y_4538_ = v___y_4578_;
v___y_4539_ = v___y_4565_;
v___y_4540_ = v___y_4563_;
v___y_4541_ = v___y_4573_;
goto v___jp_4514_;
}
else
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4597_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_4598_ = l_Nat_reprFast(v___x_4594_);
v___x_4599_ = lean_string_append(v___x_4597_, v___x_4598_);
lean_dec_ref(v___x_4598_);
v___x_4600_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_4601_ = lean_string_append(v___x_4599_, v___x_4600_);
v___x_4602_ = lean_nat_sub(v___x_4594_, v___y_4572_);
lean_dec(v___y_4572_);
v___x_4603_ = l_Nat_reprFast(v___x_4602_);
v___x_4604_ = lean_string_append(v___x_4601_, v___x_4603_);
lean_dec_ref(v___x_4603_);
v___x_4605_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_4606_ = lean_string_append(v___x_4604_, v___x_4605_);
v___x_4607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
v___x_4608_ = l_Lean_MessageData_ofFormat(v___x_4607_);
v___x_4609_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4232_, v___x_4608_, v___y_4578_, v___y_4565_, v___y_4563_, v___y_4573_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_dec_ref_known(v___x_4609_, 1);
lean_inc_ref(v_result_4585_);
v___y_4515_ = v_result_4585_;
v___y_4516_ = v_result_4585_;
v___y_4517_ = v___y_4570_;
v___y_4518_ = v___y_4569_;
v___y_4519_ = v___x_4594_;
v___y_4520_ = v_aig_4586_;
v___y_4521_ = v___y_4571_;
v___y_4522_ = v___y_4561_;
v___y_4523_ = v___y_4575_;
v___y_4524_ = v___y_4566_;
v___y_4525_ = v_ref_4590_;
v___y_4526_ = v___y_4568_;
v___y_4527_ = v_cache_4589_;
v___y_4528_ = v___y_4580_;
v___y_4529_ = v___y_4564_;
v___y_4530_ = v___y_4581_;
v___y_4531_ = v___y_4582_;
v___y_4532_ = v___y_4576_;
v___y_4533_ = v___y_4579_;
v___y_4534_ = v___y_4577_;
v___y_4535_ = v___y_4574_;
v___y_4536_ = v___y_4562_;
v___y_4537_ = v___y_4567_;
v___y_4538_ = v___y_4578_;
v___y_4539_ = v___y_4565_;
v___y_4540_ = v___y_4563_;
v___y_4541_ = v___y_4573_;
goto v___jp_4514_;
}
else
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
lean_dec_ref(v_ref_4590_);
lean_dec_ref(v_cache_4589_);
lean_dec_ref(v_aig_4586_);
lean_dec_ref(v_result_4585_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4570_);
lean_dec(v___y_4568_);
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4572_);
lean_dec(v___y_4570_);
lean_dec(v___y_4568_);
v_a_4618_ = lean_ctor_get(v___y_4583_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___y_4583_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___y_4583_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___y_4583_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
v___jp_4626_:
{
lean_object* v___x_4654_; double v___x_4655_; double v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4654_ = lean_io_get_num_heartbeats();
v___x_4655_ = lean_float_of_nat(v___y_4648_);
v___x_4656_ = lean_float_of_nat(v___x_4654_);
v___x_4657_ = lean_box_float(v___x_4655_);
v___x_4658_ = lean_box_float(v___x_4656_);
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4657_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v_a_4653_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
lean_inc_ref(v___y_4631_);
v___x_4661_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4232_, v___y_4640_, v___y_4631_, v___y_4639_, v___y_4634_, v___y_4651_, v___f_4228_, v___x_4660_, v___y_4638_, v___y_4641_, v___y_4637_, v___y_4636_, v___y_4649_, v___y_4652_, v___y_4650_, v___y_4646_, v___y_4627_, v___y_4644_, v___y_4635_, v___y_4642_, v___y_4628_, v___y_4632_);
v___y_4561_ = v___y_4640_;
v___y_4562_ = v___y_4627_;
v___y_4563_ = v___y_4628_;
v___y_4564_ = v___y_4641_;
v___y_4565_ = v___y_4642_;
v___y_4566_ = v___y_4643_;
v___y_4567_ = v___y_4644_;
v___y_4568_ = v___y_4629_;
v___y_4569_ = v___y_4645_;
v___y_4570_ = v___y_4630_;
v___y_4571_ = v___y_4631_;
v___y_4572_ = v___y_4633_;
v___y_4573_ = v___y_4632_;
v___y_4574_ = v___y_4646_;
v___y_4575_ = v___y_4647_;
v___y_4576_ = v___y_4649_;
v___y_4577_ = v___y_4650_;
v___y_4578_ = v___y_4635_;
v___y_4579_ = v___y_4652_;
v___y_4580_ = v___y_4638_;
v___y_4581_ = v___y_4637_;
v___y_4582_ = v___y_4636_;
v___y_4583_ = v___x_4661_;
goto v___jp_4560_;
}
v___jp_4662_:
{
lean_object* v___x_4690_; double v___x_4691_; double v___x_4692_; double v___x_4693_; double v___x_4694_; double v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4690_ = lean_io_mono_nanos_now();
v___x_4691_ = lean_float_of_nat(v___y_4670_);
v___x_4692_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4693_ = lean_float_div(v___x_4691_, v___x_4692_);
v___x_4694_ = lean_float_of_nat(v___x_4690_);
v___x_4695_ = lean_float_div(v___x_4694_, v___x_4692_);
v___x_4696_ = lean_box_float(v___x_4693_);
v___x_4697_ = lean_box_float(v___x_4695_);
v___x_4698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4696_);
lean_ctor_set(v___x_4698_, 1, v___x_4697_);
v___x_4699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4699_, 0, v_a_4689_);
lean_ctor_set(v___x_4699_, 1, v___x_4698_);
lean_inc_ref(v___y_4667_);
v___x_4700_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4232_, v___y_4677_, v___y_4667_, v___y_4676_, v___y_4671_, v___y_4687_, v___f_4228_, v___x_4699_, v___y_4675_, v___y_4678_, v___y_4674_, v___y_4673_, v___y_4685_, v___y_4688_, v___y_4686_, v___y_4683_, v___y_4663_, v___y_4681_, v___y_4672_, v___y_4679_, v___y_4664_, v___y_4668_);
v___y_4561_ = v___y_4677_;
v___y_4562_ = v___y_4663_;
v___y_4563_ = v___y_4664_;
v___y_4564_ = v___y_4678_;
v___y_4565_ = v___y_4679_;
v___y_4566_ = v___y_4680_;
v___y_4567_ = v___y_4681_;
v___y_4568_ = v___y_4665_;
v___y_4569_ = v___y_4682_;
v___y_4570_ = v___y_4666_;
v___y_4571_ = v___y_4667_;
v___y_4572_ = v___y_4669_;
v___y_4573_ = v___y_4668_;
v___y_4574_ = v___y_4683_;
v___y_4575_ = v___y_4684_;
v___y_4576_ = v___y_4685_;
v___y_4577_ = v___y_4686_;
v___y_4578_ = v___y_4672_;
v___y_4579_ = v___y_4688_;
v___y_4580_ = v___y_4675_;
v___y_4581_ = v___y_4674_;
v___y_4582_ = v___y_4673_;
v___y_4583_ = v___x_4700_;
goto v___jp_4560_;
}
v___jp_4701_:
{
lean_object* v___x_4728_; lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4783_; 
v___x_4728_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4708_);
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4731_ = v___x_4728_;
v_isShared_4732_ = v_isSharedCheck_4783_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4728_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4783_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4733_; uint8_t v___x_4734_; 
v___x_4733_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4734_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4715_, v___x_4733_);
if (v___x_4734_ == 0)
{
lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4735_ = lean_io_mono_nanos_now();
v___x_4736_ = l_IO_lazyPure___redArg(v___y_4724_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
lean_del_object(v___x_4731_);
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set_tag(v___x_4739_, 1);
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
v___y_4663_ = v___y_4702_;
v___y_4664_ = v___y_4703_;
v___y_4665_ = v___y_4705_;
v___y_4666_ = v___y_4706_;
v___y_4667_ = v___y_4707_;
v___y_4668_ = v___y_4708_;
v___y_4669_ = v___y_4709_;
v___y_4670_ = v___x_4735_;
v___y_4671_ = v___y_4711_;
v___y_4672_ = v___y_4710_;
v___y_4673_ = v___y_4712_;
v___y_4674_ = v___y_4713_;
v___y_4675_ = v___y_4714_;
v___y_4676_ = v___y_4715_;
v___y_4677_ = v___y_4716_;
v___y_4678_ = v___y_4717_;
v___y_4679_ = v___y_4718_;
v___y_4680_ = v___y_4719_;
v___y_4681_ = v___y_4720_;
v___y_4682_ = v___y_4721_;
v___y_4683_ = v___y_4722_;
v___y_4684_ = v___y_4723_;
v___y_4685_ = v___y_4725_;
v___y_4686_ = v___y_4726_;
v___y_4687_ = v_a_4729_;
v___y_4688_ = v___y_4727_;
v_a_4689_ = v___x_4742_;
goto v___jp_4662_;
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4758_; 
v_a_4745_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4747_ = v___x_4736_;
v_isShared_4748_ = v_isSharedCheck_4758_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4736_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4758_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4749_; lean_object* v___x_4751_; 
v___x_4749_ = lean_io_error_to_string(v_a_4745_);
if (v_isShared_4748_ == 0)
{
lean_ctor_set_tag(v___x_4747_, 3);
lean_ctor_set(v___x_4747_, 0, v___x_4749_);
v___x_4751_ = v___x_4747_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4749_);
v___x_4751_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4755_; 
v___x_4752_ = l_Lean_MessageData_ofFormat(v___x_4751_);
lean_inc(v___y_4704_);
v___x_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4753_, 0, v___y_4704_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v___x_4753_);
v___x_4755_ = v___x_4731_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4753_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
v___y_4663_ = v___y_4702_;
v___y_4664_ = v___y_4703_;
v___y_4665_ = v___y_4705_;
v___y_4666_ = v___y_4706_;
v___y_4667_ = v___y_4707_;
v___y_4668_ = v___y_4708_;
v___y_4669_ = v___y_4709_;
v___y_4670_ = v___x_4735_;
v___y_4671_ = v___y_4711_;
v___y_4672_ = v___y_4710_;
v___y_4673_ = v___y_4712_;
v___y_4674_ = v___y_4713_;
v___y_4675_ = v___y_4714_;
v___y_4676_ = v___y_4715_;
v___y_4677_ = v___y_4716_;
v___y_4678_ = v___y_4717_;
v___y_4679_ = v___y_4718_;
v___y_4680_ = v___y_4719_;
v___y_4681_ = v___y_4720_;
v___y_4682_ = v___y_4721_;
v___y_4683_ = v___y_4722_;
v___y_4684_ = v___y_4723_;
v___y_4685_ = v___y_4725_;
v___y_4686_ = v___y_4726_;
v___y_4687_ = v_a_4729_;
v___y_4688_ = v___y_4727_;
v_a_4689_ = v___x_4755_;
goto v___jp_4662_;
}
}
}
}
}
else
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4759_ = lean_io_get_num_heartbeats();
v___x_4760_ = l_IO_lazyPure___redArg(v___y_4724_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_del_object(v___x_4731_);
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4760_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4760_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
lean_ctor_set_tag(v___x_4763_, 1);
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
v___y_4627_ = v___y_4702_;
v___y_4628_ = v___y_4703_;
v___y_4629_ = v___y_4705_;
v___y_4630_ = v___y_4706_;
v___y_4631_ = v___y_4707_;
v___y_4632_ = v___y_4708_;
v___y_4633_ = v___y_4709_;
v___y_4634_ = v___y_4711_;
v___y_4635_ = v___y_4710_;
v___y_4636_ = v___y_4712_;
v___y_4637_ = v___y_4713_;
v___y_4638_ = v___y_4714_;
v___y_4639_ = v___y_4715_;
v___y_4640_ = v___y_4716_;
v___y_4641_ = v___y_4717_;
v___y_4642_ = v___y_4718_;
v___y_4643_ = v___y_4719_;
v___y_4644_ = v___y_4720_;
v___y_4645_ = v___y_4721_;
v___y_4646_ = v___y_4722_;
v___y_4647_ = v___y_4723_;
v___y_4648_ = v___x_4759_;
v___y_4649_ = v___y_4725_;
v___y_4650_ = v___y_4726_;
v___y_4651_ = v_a_4729_;
v___y_4652_ = v___y_4727_;
v_a_4653_ = v___x_4766_;
goto v___jp_4626_;
}
}
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4782_; 
v_a_4769_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4771_ = v___x_4760_;
v_isShared_4772_ = v_isSharedCheck_4782_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4760_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4782_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4773_; lean_object* v___x_4775_; 
v___x_4773_ = lean_io_error_to_string(v_a_4769_);
if (v_isShared_4772_ == 0)
{
lean_ctor_set_tag(v___x_4771_, 3);
lean_ctor_set(v___x_4771_, 0, v___x_4773_);
v___x_4775_ = v___x_4771_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4773_);
v___x_4775_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; 
v___x_4776_ = l_Lean_MessageData_ofFormat(v___x_4775_);
lean_inc(v___y_4704_);
v___x_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___y_4704_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v___x_4777_);
v___x_4779_ = v___x_4731_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
v___y_4627_ = v___y_4702_;
v___y_4628_ = v___y_4703_;
v___y_4629_ = v___y_4705_;
v___y_4630_ = v___y_4706_;
v___y_4631_ = v___y_4707_;
v___y_4632_ = v___y_4708_;
v___y_4633_ = v___y_4709_;
v___y_4634_ = v___y_4711_;
v___y_4635_ = v___y_4710_;
v___y_4636_ = v___y_4712_;
v___y_4637_ = v___y_4713_;
v___y_4638_ = v___y_4714_;
v___y_4639_ = v___y_4715_;
v___y_4640_ = v___y_4716_;
v___y_4641_ = v___y_4717_;
v___y_4642_ = v___y_4718_;
v___y_4643_ = v___y_4719_;
v___y_4644_ = v___y_4720_;
v___y_4645_ = v___y_4721_;
v___y_4646_ = v___y_4722_;
v___y_4647_ = v___y_4723_;
v___y_4648_ = v___x_4759_;
v___y_4649_ = v___y_4725_;
v___y_4650_ = v___y_4726_;
v___y_4651_ = v_a_4729_;
v___y_4652_ = v___y_4727_;
v_a_4653_ = v___x_4779_;
goto v___jp_4626_;
}
}
}
}
}
}
}
v___jp_4784_:
{
lean_object* v___x_4800_; lean_object* v_satExpr_4801_; lean_object* v_bvExpr_4802_; lean_object* v___x_4803_; lean_object* v_theoryState_4804_; lean_object* v_bitvecState_4805_; lean_object* v___x_4806_; lean_object* v_theoryState_4807_; lean_object* v_satExpr_4808_; lean_object* v_hypQueue_4809_; lean_object* v_usedHyps_4810_; uint8_t v_didChange_4811_; lean_object* v_solverTimeBudgetMs_4812_; lean_object* v_roundBudget_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4854_; 
v___x_4800_ = lean_st_ref_get(v___y_4787_);
v_satExpr_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc_ref(v_satExpr_4801_);
lean_dec(v___x_4800_);
v_bvExpr_4802_ = lean_ctor_get(v_satExpr_4801_, 0);
lean_inc_ref(v_bvExpr_4802_);
lean_dec_ref(v_satExpr_4801_);
v___x_4803_ = lean_st_ref_get(v___y_4787_);
v_theoryState_4804_ = lean_ctor_get(v___x_4803_, 3);
lean_inc_ref(v_theoryState_4804_);
lean_dec(v___x_4803_);
v_bitvecState_4805_ = lean_ctor_get(v_theoryState_4804_, 1);
lean_inc_ref(v_bitvecState_4805_);
lean_dec_ref(v_theoryState_4804_);
v___x_4806_ = lean_st_ref_take(v___y_4787_);
v_theoryState_4807_ = lean_ctor_get(v___x_4806_, 3);
v_satExpr_4808_ = lean_ctor_get(v___x_4806_, 0);
v_hypQueue_4809_ = lean_ctor_get(v___x_4806_, 1);
v_usedHyps_4810_ = lean_ctor_get(v___x_4806_, 2);
v_didChange_4811_ = lean_ctor_get_uint8(v___x_4806_, sizeof(void*)*6);
v_solverTimeBudgetMs_4812_ = lean_ctor_get(v___x_4806_, 4);
v_roundBudget_4813_ = lean_ctor_get(v___x_4806_, 5);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4815_ = v___x_4806_;
v_isShared_4816_ = v_isSharedCheck_4854_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_roundBudget_4813_);
lean_inc(v_solverTimeBudgetMs_4812_);
lean_inc(v_theoryState_4807_);
lean_inc(v_usedHyps_4810_);
lean_inc(v_hypQueue_4809_);
lean_inc(v_satExpr_4808_);
lean_dec(v___x_4806_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4854_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v_funState_4817_; lean_object* v_preprocessCaches_4818_; lean_object* v_satSolver_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4852_; 
v_funState_4817_ = lean_ctor_get(v_theoryState_4807_, 0);
v_preprocessCaches_4818_ = lean_ctor_get(v_theoryState_4807_, 2);
v_satSolver_4819_ = lean_ctor_get(v_theoryState_4807_, 3);
v_isSharedCheck_4852_ = !lean_is_exclusive(v_theoryState_4807_);
if (v_isSharedCheck_4852_ == 0)
{
lean_object* v_unused_4853_; 
v_unused_4853_ = lean_ctor_get(v_theoryState_4807_, 1);
lean_dec(v_unused_4853_);
v___x_4821_ = v_theoryState_4807_;
v_isShared_4822_ = v_isSharedCheck_4852_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_satSolver_4819_);
lean_inc(v_preprocessCaches_4818_);
lean_inc(v_funState_4817_);
lean_dec(v_theoryState_4807_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4852_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4827_; 
v___x_4823_ = lean_unsigned_to_nat(0u);
v___x_4824_ = lean_unsigned_to_nat(16u);
v___x_4825_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 1, v___x_4825_);
v___x_4827_ = v___x_4821_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_funState_4817_);
lean_ctor_set(v_reuseFailAlloc_4851_, 1, v___x_4825_);
lean_ctor_set(v_reuseFailAlloc_4851_, 2, v_preprocessCaches_4818_);
lean_ctor_set(v_reuseFailAlloc_4851_, 3, v_satSolver_4819_);
v___x_4827_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
lean_object* v___x_4829_; 
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 3, v___x_4827_);
v___x_4829_ = v___x_4815_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_satExpr_4808_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_hypQueue_4809_);
lean_ctor_set(v_reuseFailAlloc_4850_, 2, v_usedHyps_4810_);
lean_ctor_set(v_reuseFailAlloc_4850_, 3, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4850_, 4, v_solverTimeBudgetMs_4812_);
lean_ctor_set(v_reuseFailAlloc_4850_, 5, v_roundBudget_4813_);
lean_ctor_set_uint8(v_reuseFailAlloc_4850_, sizeof(void*)*6, v_didChange_4811_);
v___x_4829_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4830_; lean_object* v_aig_4831_; lean_object* v_toCold_4832_; lean_object* v_options_4833_; lean_object* v_blastCache_4834_; lean_object* v_cnfCache_4835_; lean_object* v_decls_4836_; lean_object* v_ref_4837_; lean_object* v_inheritedTraceOptions_4838_; uint8_t v_hasTrace_4839_; lean_object* v___f_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; lean_object* v___x_4843_; 
v___x_4830_ = lean_st_ref_put(v___y_4787_, v___x_4829_);
v_aig_4831_ = lean_ctor_get(v_bitvecState_4805_, 0);
lean_inc_ref(v_aig_4831_);
v_toCold_4832_ = lean_ctor_get(v___y_4798_, 0);
v_options_4833_ = lean_ctor_get(v_toCold_4832_, 2);
v_blastCache_4834_ = lean_ctor_get(v_bitvecState_4805_, 1);
lean_inc_ref(v_blastCache_4834_);
v_cnfCache_4835_ = lean_ctor_get(v_bitvecState_4805_, 2);
lean_inc_ref(v_cnfCache_4835_);
lean_dec_ref(v_bitvecState_4805_);
v_decls_4836_ = lean_ctor_get(v_aig_4831_, 0);
lean_inc_ref(v_decls_4836_);
v_ref_4837_ = lean_ctor_get(v___y_4798_, 2);
v_inheritedTraceOptions_4838_ = lean_ctor_get(v_toCold_4832_, 11);
v_hasTrace_4839_ = lean_ctor_get_uint8(v_options_4833_, sizeof(void*)*1);
v___f_4840_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_4840_, 0, v_aig_4831_);
lean_closure_set(v___f_4840_, 1, v_bvExpr_4802_);
lean_closure_set(v___f_4840_, 2, v_blastCache_4834_);
v___x_4841_ = lean_array_get_size(v_decls_4836_);
lean_dec_ref(v_decls_4836_);
v___x_4842_ = 1;
v___x_4843_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
if (v_hasTrace_4839_ == 0)
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_4840_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
v___y_4561_ = v___x_4842_;
v___y_4562_ = v___y_4794_;
v___y_4563_ = v___y_4798_;
v___y_4564_ = v___y_4787_;
v___y_4565_ = v___y_4797_;
v___y_4566_ = v___x_4825_;
v___y_4567_ = v___y_4795_;
v___y_4568_ = v___x_4823_;
v___y_4569_ = v_ctx_4785_;
v___y_4570_ = v___x_4824_;
v___y_4571_ = v___x_4843_;
v___y_4572_ = v___x_4841_;
v___y_4573_ = v___y_4799_;
v___y_4574_ = v___y_4793_;
v___y_4575_ = v_cnfCache_4835_;
v___y_4576_ = v___y_4790_;
v___y_4577_ = v___y_4792_;
v___y_4578_ = v___y_4796_;
v___y_4579_ = v___y_4791_;
v___y_4580_ = v___y_4786_;
v___y_4581_ = v___y_4788_;
v___y_4582_ = v___y_4789_;
v___y_4583_ = v___x_4844_;
goto v___jp_4560_;
}
else
{
lean_object* v___x_4845_; uint8_t v___x_4846_; 
v___x_4845_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4846_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4838_, v_options_4833_, v___x_4845_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4847_; uint8_t v___x_4848_; 
v___x_4847_ = l_Lean_trace_profiler;
v___x_4848_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4833_, v___x_4847_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; 
v___x_4849_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_4840_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
v___y_4561_ = v___x_4842_;
v___y_4562_ = v___y_4794_;
v___y_4563_ = v___y_4798_;
v___y_4564_ = v___y_4787_;
v___y_4565_ = v___y_4797_;
v___y_4566_ = v___x_4825_;
v___y_4567_ = v___y_4795_;
v___y_4568_ = v___x_4823_;
v___y_4569_ = v_ctx_4785_;
v___y_4570_ = v___x_4824_;
v___y_4571_ = v___x_4843_;
v___y_4572_ = v___x_4841_;
v___y_4573_ = v___y_4799_;
v___y_4574_ = v___y_4793_;
v___y_4575_ = v_cnfCache_4835_;
v___y_4576_ = v___y_4790_;
v___y_4577_ = v___y_4792_;
v___y_4578_ = v___y_4796_;
v___y_4579_ = v___y_4791_;
v___y_4580_ = v___y_4786_;
v___y_4581_ = v___y_4788_;
v___y_4582_ = v___y_4789_;
v___y_4583_ = v___x_4849_;
goto v___jp_4560_;
}
else
{
v___y_4702_ = v___y_4794_;
v___y_4703_ = v___y_4798_;
v___y_4704_ = v_ref_4837_;
v___y_4705_ = v___x_4823_;
v___y_4706_ = v___x_4824_;
v___y_4707_ = v___x_4843_;
v___y_4708_ = v___y_4799_;
v___y_4709_ = v___x_4841_;
v___y_4710_ = v___y_4796_;
v___y_4711_ = v___x_4846_;
v___y_4712_ = v___y_4789_;
v___y_4713_ = v___y_4788_;
v___y_4714_ = v___y_4786_;
v___y_4715_ = v_options_4833_;
v___y_4716_ = v___x_4842_;
v___y_4717_ = v___y_4787_;
v___y_4718_ = v___y_4797_;
v___y_4719_ = v___x_4825_;
v___y_4720_ = v___y_4795_;
v___y_4721_ = v_ctx_4785_;
v___y_4722_ = v___y_4793_;
v___y_4723_ = v_cnfCache_4835_;
v___y_4724_ = v___f_4840_;
v___y_4725_ = v___y_4790_;
v___y_4726_ = v___y_4792_;
v___y_4727_ = v___y_4791_;
goto v___jp_4701_;
}
}
else
{
v___y_4702_ = v___y_4794_;
v___y_4703_ = v___y_4798_;
v___y_4704_ = v_ref_4837_;
v___y_4705_ = v___x_4823_;
v___y_4706_ = v___x_4824_;
v___y_4707_ = v___x_4843_;
v___y_4708_ = v___y_4799_;
v___y_4709_ = v___x_4841_;
v___y_4710_ = v___y_4796_;
v___y_4711_ = v___x_4846_;
v___y_4712_ = v___y_4789_;
v___y_4713_ = v___y_4788_;
v___y_4714_ = v___y_4786_;
v___y_4715_ = v_options_4833_;
v___y_4716_ = v___x_4842_;
v___y_4717_ = v___y_4787_;
v___y_4718_ = v___y_4797_;
v___y_4719_ = v___x_4825_;
v___y_4720_ = v___y_4795_;
v___y_4721_ = v_ctx_4785_;
v___y_4722_ = v___y_4793_;
v___y_4723_ = v_cnfCache_4835_;
v___y_4724_ = v___f_4840_;
v___y_4725_ = v___y_4790_;
v___y_4726_ = v___y_4792_;
v___y_4727_ = v___y_4791_;
goto v___jp_4701_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___boxed(lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_);
lean_dec(v_a_5408_);
lean_dec_ref(v_a_5407_);
lean_dec(v_a_5406_);
lean_dec_ref(v_a_5405_);
lean_dec(v_a_5404_);
lean_dec_ref(v_a_5403_);
lean_dec(v_a_5402_);
lean_dec_ref(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
lean_dec(v_a_5397_);
lean_dec(v_a_5396_);
lean_dec_ref(v_a_5395_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2(lean_object* v_cls_5411_, lean_object* v_msg_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_){
_start:
{
lean_object* v___x_5428_; 
v___x_5428_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_5411_, v_msg_5412_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_);
return v___x_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___boxed(lean_object** _args){
lean_object* v_cls_5429_ = _args[0];
lean_object* v_msg_5430_ = _args[1];
lean_object* v___y_5431_ = _args[2];
lean_object* v___y_5432_ = _args[3];
lean_object* v___y_5433_ = _args[4];
lean_object* v___y_5434_ = _args[5];
lean_object* v___y_5435_ = _args[6];
lean_object* v___y_5436_ = _args[7];
lean_object* v___y_5437_ = _args[8];
lean_object* v___y_5438_ = _args[9];
lean_object* v___y_5439_ = _args[10];
lean_object* v___y_5440_ = _args[11];
lean_object* v___y_5441_ = _args[12];
lean_object* v___y_5442_ = _args[13];
lean_object* v___y_5443_ = _args[14];
lean_object* v___y_5444_ = _args[15];
lean_object* v___y_5445_ = _args[16];
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2(v_cls_5429_, v_msg_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec(v___y_5435_);
lean_dec_ref(v___y_5434_);
lean_dec(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3(lean_object* v_00_u03b1_5447_, lean_object* v_msg_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v___x_5464_; 
v___x_5464_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v_msg_5448_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03b1_5465_ = _args[0];
lean_object* v_msg_5466_ = _args[1];
lean_object* v___y_5467_ = _args[2];
lean_object* v___y_5468_ = _args[3];
lean_object* v___y_5469_ = _args[4];
lean_object* v___y_5470_ = _args[5];
lean_object* v___y_5471_ = _args[6];
lean_object* v___y_5472_ = _args[7];
lean_object* v___y_5473_ = _args[8];
lean_object* v___y_5474_ = _args[9];
lean_object* v___y_5475_ = _args[10];
lean_object* v___y_5476_ = _args[11];
lean_object* v___y_5477_ = _args[12];
lean_object* v___y_5478_ = _args[13];
lean_object* v___y_5479_ = _args[14];
lean_object* v___y_5480_ = _args[15];
lean_object* v___y_5481_ = _args[16];
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3(v_00_u03b1_5465_, v_msg_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
lean_dec(v___y_5478_);
lean_dec_ref(v___y_5477_);
lean_dec(v___y_5476_);
lean_dec_ref(v___y_5475_);
lean_dec(v___y_5474_);
lean_dec_ref(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec(v___y_5469_);
lean_dec(v___y_5468_);
lean_dec_ref(v___y_5467_);
return v_res_5482_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9(lean_object* v_00_u03b1_5483_, lean_object* v_x_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_){
_start:
{
lean_object* v___x_5500_; 
v___x_5500_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_x_5484_);
return v___x_5500_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_00_u03b1_5501_ = _args[0];
lean_object* v_x_5502_ = _args[1];
lean_object* v___y_5503_ = _args[2];
lean_object* v___y_5504_ = _args[3];
lean_object* v___y_5505_ = _args[4];
lean_object* v___y_5506_ = _args[5];
lean_object* v___y_5507_ = _args[6];
lean_object* v___y_5508_ = _args[7];
lean_object* v___y_5509_ = _args[8];
lean_object* v___y_5510_ = _args[9];
lean_object* v___y_5511_ = _args[10];
lean_object* v___y_5512_ = _args[11];
lean_object* v___y_5513_ = _args[12];
lean_object* v___y_5514_ = _args[13];
lean_object* v___y_5515_ = _args[14];
lean_object* v___y_5516_ = _args[15];
lean_object* v___y_5517_ = _args[16];
_start:
{
lean_object* v_res_5518_; 
v_res_5518_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9(v_00_u03b1_5501_, v_x_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
lean_dec(v___y_5514_);
lean_dec_ref(v___y_5513_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
lean_dec(v___y_5508_);
lean_dec(v___y_5507_);
lean_dec_ref(v___y_5506_);
lean_dec(v___y_5505_);
lean_dec(v___y_5504_);
lean_dec_ref(v___y_5503_);
return v_res_5518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8(lean_object* v_oldTraces_5519_, lean_object* v_data_5520_, lean_object* v_ref_5521_, lean_object* v_msg_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_){
_start:
{
lean_object* v___x_5538_; 
v___x_5538_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_5519_, v_data_5520_, v_ref_5521_, v_msg_5522_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_);
return v___x_5538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_5539_ = _args[0];
lean_object* v_data_5540_ = _args[1];
lean_object* v_ref_5541_ = _args[2];
lean_object* v_msg_5542_ = _args[3];
lean_object* v___y_5543_ = _args[4];
lean_object* v___y_5544_ = _args[5];
lean_object* v___y_5545_ = _args[6];
lean_object* v___y_5546_ = _args[7];
lean_object* v___y_5547_ = _args[8];
lean_object* v___y_5548_ = _args[9];
lean_object* v___y_5549_ = _args[10];
lean_object* v___y_5550_ = _args[11];
lean_object* v___y_5551_ = _args[12];
lean_object* v___y_5552_ = _args[13];
lean_object* v___y_5553_ = _args[14];
lean_object* v___y_5554_ = _args[15];
lean_object* v___y_5555_ = _args[16];
lean_object* v___y_5556_ = _args[17];
lean_object* v___y_5557_ = _args[18];
_start:
{
lean_object* v_res_5558_; 
v_res_5558_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8(v_oldTraces_5539_, v_data_5540_, v_ref_5541_, v_msg_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_);
lean_dec(v___y_5556_);
lean_dec_ref(v___y_5555_);
lean_dec(v___y_5554_);
lean_dec_ref(v___y_5553_);
lean_dec(v___y_5552_);
lean_dec_ref(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec_ref(v___y_5549_);
lean_dec(v___y_5548_);
lean_dec(v___y_5547_);
lean_dec_ref(v___y_5546_);
lean_dec(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16(lean_object* v_acc_5559_, lean_object* v_decls_5560_, lean_object* v_hinv_5561_, lean_object* v_idx_5562_, lean_object* v_hidx_5563_, lean_object* v_a_5564_){
_start:
{
lean_object* v___x_5565_; 
v___x_5565_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v_acc_5559_, v_decls_5560_, v_idx_5562_, v_a_5564_);
return v___x_5565_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___boxed(lean_object* v_acc_5566_, lean_object* v_decls_5567_, lean_object* v_hinv_5568_, lean_object* v_idx_5569_, lean_object* v_hidx_5570_, lean_object* v_a_5571_){
_start:
{
lean_object* v_res_5572_; 
v_res_5572_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16(v_acc_5566_, v_decls_5567_, v_hinv_5568_, v_idx_5569_, v_hidx_5570_, v_a_5571_);
lean_dec_ref(v_decls_5567_);
return v_res_5572_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18(lean_object* v___x_5573_, lean_object* v_00_u03b2_5574_, lean_object* v_m_5575_, lean_object* v_a_5576_){
_start:
{
uint8_t v___x_5577_; 
v___x_5577_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_5573_, v_m_5575_, v_a_5576_);
return v___x_5577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___boxed(lean_object* v___x_5578_, lean_object* v_00_u03b2_5579_, lean_object* v_m_5580_, lean_object* v_a_5581_){
_start:
{
uint8_t v_res_5582_; lean_object* v_r_5583_; 
v_res_5582_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18(v___x_5578_, v_00_u03b2_5579_, v_m_5580_, v_a_5581_);
lean_dec(v_a_5581_);
lean_dec_ref(v_m_5580_);
lean_dec(v___x_5578_);
v_r_5583_ = lean_box(v_res_5582_);
return v_r_5583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19(lean_object* v___x_5584_, lean_object* v_00_u03b2_5585_, lean_object* v_m_5586_, lean_object* v_a_5587_, lean_object* v_b_5588_){
_start:
{
lean_object* v___x_5589_; 
v___x_5589_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_5584_, v_m_5586_, v_a_5587_, v_b_5588_);
return v___x_5589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___boxed(lean_object* v___x_5590_, lean_object* v_00_u03b2_5591_, lean_object* v_m_5592_, lean_object* v_a_5593_, lean_object* v_b_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19(v___x_5590_, v_00_u03b2_5591_, v_m_5592_, v_a_5593_, v_b_5594_);
lean_dec(v___x_5590_);
return v_res_5595_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23(lean_object* v___x_5596_, lean_object* v_00_u03b2_5597_, lean_object* v_a_5598_, lean_object* v_x_5599_){
_start:
{
uint8_t v___x_5600_; 
v___x_5600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_5598_, v_x_5599_);
return v___x_5600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___boxed(lean_object* v___x_5601_, lean_object* v_00_u03b2_5602_, lean_object* v_a_5603_, lean_object* v_x_5604_){
_start:
{
uint8_t v_res_5605_; lean_object* v_r_5606_; 
v_res_5605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23(v___x_5601_, v_00_u03b2_5602_, v_a_5603_, v_x_5604_);
lean_dec(v_x_5604_);
lean_dec(v_a_5603_);
lean_dec(v___x_5601_);
v_r_5606_ = lean_box(v_res_5605_);
return v_r_5606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25(lean_object* v___x_5607_, lean_object* v_00_u03b2_5608_, lean_object* v_data_5609_){
_start:
{
lean_object* v___x_5610_; 
v___x_5610_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_5607_, v_data_5609_);
return v___x_5610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___boxed(lean_object* v___x_5611_, lean_object* v_00_u03b2_5612_, lean_object* v_data_5613_){
_start:
{
lean_object* v_res_5614_; 
v_res_5614_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25(v___x_5611_, v_00_u03b2_5612_, v_data_5613_);
lean_dec(v___x_5611_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28(lean_object* v___x_5615_, lean_object* v_00_u03b2_5616_, lean_object* v_i_5617_, lean_object* v_source_5618_, lean_object* v_target_5619_){
_start:
{
lean_object* v___x_5620_; 
v___x_5620_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(v_i_5617_, v_source_5618_, v_target_5619_);
return v___x_5620_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___boxed(lean_object* v___x_5621_, lean_object* v_00_u03b2_5622_, lean_object* v_i_5623_, lean_object* v_source_5624_, lean_object* v_target_5625_){
_start:
{
lean_object* v_res_5626_; 
v_res_5626_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28(v___x_5621_, v_00_u03b2_5622_, v_i_5623_, v_source_5624_, v_target_5625_);
lean_dec(v___x_5621_);
return v_res_5626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29(lean_object* v_00_u03b2_5627_, lean_object* v_x_5628_, lean_object* v_x_5629_){
_start:
{
lean_object* v___x_5630_; 
v___x_5630_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(v_x_5628_, v_x_5629_);
return v___x_5630_;
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
