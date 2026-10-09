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
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg(lean_object* v_a_14_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_14_ = stack[0].m_obj;
lean_object* v_res_48_;
v_res_48_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg(v_a_14_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___boxed(lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg(v_a_49_);
lean_dec(v_a_49_);
return v_res_51_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState(lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; lean_object* v_theoryState_68_; lean_object* v_bitvecState_69_; lean_object* v___x_70_; lean_object* v_theoryState_71_; lean_object* v_satExpr_72_; lean_object* v_hypQueue_73_; lean_object* v_usedHyps_74_; uint8_t v_didChange_75_; lean_object* v_solverTimeBudgetMs_76_; lean_object* v_roundBudget_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_98_; 
v___x_67_ = lean_st_ref_get(v_a_53_);
v_theoryState_68_ = lean_ctor_get(v___x_67_, 3);
lean_inc_ref(v_theoryState_68_);
lean_dec(v___x_67_);
v_bitvecState_69_ = lean_ctor_get(v_theoryState_68_, 1);
lean_inc_ref(v_bitvecState_69_);
lean_dec_ref(v_theoryState_68_);
v___x_70_ = lean_st_ref_take(v_a_53_);
v_theoryState_71_ = lean_ctor_get(v___x_70_, 3);
v_satExpr_72_ = lean_ctor_get(v___x_70_, 0);
v_hypQueue_73_ = lean_ctor_get(v___x_70_, 1);
v_usedHyps_74_ = lean_ctor_get(v___x_70_, 2);
v_didChange_75_ = lean_ctor_get_uint8(v___x_70_, sizeof(void*)*6);
v_solverTimeBudgetMs_76_ = lean_ctor_get(v___x_70_, 4);
v_roundBudget_77_ = lean_ctor_get(v___x_70_, 5);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_98_ == 0)
{
v___x_79_ = v___x_70_;
v_isShared_80_ = v_isSharedCheck_98_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_roundBudget_77_);
lean_inc(v_solverTimeBudgetMs_76_);
lean_inc(v_theoryState_71_);
lean_inc(v_usedHyps_74_);
lean_inc(v_hypQueue_73_);
lean_inc(v_satExpr_72_);
lean_dec(v___x_70_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_98_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v_funState_81_; lean_object* v_preprocessCaches_82_; lean_object* v_satSolver_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_96_; 
v_funState_81_ = lean_ctor_get(v_theoryState_71_, 0);
v_preprocessCaches_82_ = lean_ctor_get(v_theoryState_71_, 2);
v_satSolver_83_ = lean_ctor_get(v_theoryState_71_, 3);
v_isSharedCheck_96_ = !lean_is_exclusive(v_theoryState_71_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v_theoryState_71_, 1);
lean_dec(v_unused_97_);
v___x_85_ = v_theoryState_71_;
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_satSolver_83_);
lean_inc(v_preprocessCaches_82_);
lean_inc(v_funState_81_);
lean_dec(v_theoryState_71_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__4);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_funState_81_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_preprocessCaches_82_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v_satSolver_83_);
v___x_89_ = v_reuseFailAlloc_95_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 3, v___x_89_);
v___x_91_ = v___x_79_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_satExpr_72_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_hypQueue_73_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_usedHyps_74_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_94_, 4, v_solverTimeBudgetMs_76_);
lean_ctor_set(v_reuseFailAlloc_94_, 5, v_roundBudget_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_94_, sizeof(void*)*6, v_didChange_75_);
v___x_91_ = v_reuseFailAlloc_94_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_st_ref_put(v_a_53_, v___x_91_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v_bitvecState_69_);
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_52_ = stack[0].m_obj;
lean_object* v_a_53_ = stack[1].m_obj;
lean_object* v_a_54_ = stack[2].m_obj;
lean_object* v_a_55_ = stack[3].m_obj;
lean_object* v_a_56_ = stack[4].m_obj;
lean_object* v_a_57_ = stack[5].m_obj;
lean_object* v_a_58_ = stack[6].m_obj;
lean_object* v_a_59_ = stack[7].m_obj;
lean_object* v_a_60_ = stack[8].m_obj;
lean_object* v_a_61_ = stack[9].m_obj;
lean_object* v_a_62_ = stack[10].m_obj;
lean_object* v_a_63_ = stack[11].m_obj;
lean_object* v_a_64_ = stack[12].m_obj;
lean_object* v_a_65_ = stack[13].m_obj;
lean_object* v_res_99_;
v_res_99_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState(v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___boxed(lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState(v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
return v_res_115_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg(lean_object* v_s_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___x_119_; lean_object* v_theoryState_120_; lean_object* v_satExpr_121_; lean_object* v_hypQueue_122_; lean_object* v_usedHyps_123_; uint8_t v_didChange_124_; lean_object* v_solverTimeBudgetMs_125_; lean_object* v_roundBudget_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_147_; 
v___x_119_ = lean_st_ref_take(v_a_117_);
v_theoryState_120_ = lean_ctor_get(v___x_119_, 3);
v_satExpr_121_ = lean_ctor_get(v___x_119_, 0);
v_hypQueue_122_ = lean_ctor_get(v___x_119_, 1);
v_usedHyps_123_ = lean_ctor_get(v___x_119_, 2);
v_didChange_124_ = lean_ctor_get_uint8(v___x_119_, sizeof(void*)*6);
v_solverTimeBudgetMs_125_ = lean_ctor_get(v___x_119_, 4);
v_roundBudget_126_ = lean_ctor_get(v___x_119_, 5);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_147_ == 0)
{
v___x_128_ = v___x_119_;
v_isShared_129_ = v_isSharedCheck_147_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_roundBudget_126_);
lean_inc(v_solverTimeBudgetMs_125_);
lean_inc(v_theoryState_120_);
lean_inc(v_usedHyps_123_);
lean_inc(v_hypQueue_122_);
lean_inc(v_satExpr_121_);
lean_dec(v___x_119_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_147_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v_funState_130_; lean_object* v_preprocessCaches_131_; lean_object* v_satSolver_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_145_; 
v_funState_130_ = lean_ctor_get(v_theoryState_120_, 0);
v_preprocessCaches_131_ = lean_ctor_get(v_theoryState_120_, 2);
v_satSolver_132_ = lean_ctor_get(v_theoryState_120_, 3);
v_isSharedCheck_145_ = !lean_is_exclusive(v_theoryState_120_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v_theoryState_120_, 1);
lean_dec(v_unused_146_);
v___x_134_ = v_theoryState_120_;
v_isShared_135_ = v_isSharedCheck_145_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_satSolver_132_);
lean_inc(v_preprocessCaches_131_);
lean_inc(v_funState_130_);
lean_dec(v_theoryState_120_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_145_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_s_116_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_funState_130_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_s_116_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_preprocessCaches_131_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_satSolver_132_);
v___x_138_ = v_reuseFailAlloc_144_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 3, v___x_138_);
v___x_140_ = v___x_128_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_satExpr_121_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_hypQueue_122_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_usedHyps_123_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_solverTimeBudgetMs_125_);
lean_ctor_set(v_reuseFailAlloc_143_, 5, v_roundBudget_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, sizeof(void*)*6, v_didChange_124_);
v___x_140_ = v_reuseFailAlloc_143_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_st_ref_put(v_a_117_, v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_136_);
return v___x_142_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_116_ = stack[0].m_obj;
lean_object* v_a_117_ = stack[1].m_obj;
lean_object* v_res_148_;
v_res_148_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg(v_s_116_, v_a_117_);
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg___boxed(lean_object* v_s_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___redArg(v_s_149_, v_a_150_);
lean_dec(v_a_150_);
return v_res_152_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState(lean_object* v_s_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; lean_object* v_theoryState_170_; lean_object* v_satExpr_171_; lean_object* v_hypQueue_172_; lean_object* v_usedHyps_173_; uint8_t v_didChange_174_; lean_object* v_solverTimeBudgetMs_175_; lean_object* v_roundBudget_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_197_; 
v___x_169_ = lean_st_ref_take(v_a_155_);
v_theoryState_170_ = lean_ctor_get(v___x_169_, 3);
v_satExpr_171_ = lean_ctor_get(v___x_169_, 0);
v_hypQueue_172_ = lean_ctor_get(v___x_169_, 1);
v_usedHyps_173_ = lean_ctor_get(v___x_169_, 2);
v_didChange_174_ = lean_ctor_get_uint8(v___x_169_, sizeof(void*)*6);
v_solverTimeBudgetMs_175_ = lean_ctor_get(v___x_169_, 4);
v_roundBudget_176_ = lean_ctor_get(v___x_169_, 5);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_197_ == 0)
{
v___x_178_ = v___x_169_;
v_isShared_179_ = v_isSharedCheck_197_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_roundBudget_176_);
lean_inc(v_solverTimeBudgetMs_175_);
lean_inc(v_theoryState_170_);
lean_inc(v_usedHyps_173_);
lean_inc(v_hypQueue_172_);
lean_inc(v_satExpr_171_);
lean_dec(v___x_169_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_197_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_funState_180_; lean_object* v_preprocessCaches_181_; lean_object* v_satSolver_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_195_; 
v_funState_180_ = lean_ctor_get(v_theoryState_170_, 0);
v_preprocessCaches_181_ = lean_ctor_get(v_theoryState_170_, 2);
v_satSolver_182_ = lean_ctor_get(v_theoryState_170_, 3);
v_isSharedCheck_195_ = !lean_is_exclusive(v_theoryState_170_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_theoryState_170_, 1);
lean_dec(v_unused_196_);
v___x_184_ = v_theoryState_170_;
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_satSolver_182_);
lean_inc(v_preprocessCaches_181_);
lean_inc(v_funState_180_);
lean_dec(v_theoryState_170_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_box(0);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v_s_153_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_funState_180_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_s_153_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_preprocessCaches_181_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_satSolver_182_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 3, v___x_188_);
v___x_190_ = v___x_178_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_satExpr_171_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_hypQueue_172_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_usedHyps_173_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v_solverTimeBudgetMs_175_);
lean_ctor_set(v_reuseFailAlloc_193_, 5, v_roundBudget_176_);
lean_ctor_set_uint8(v_reuseFailAlloc_193_, sizeof(void*)*6, v_didChange_174_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_st_ref_put(v_a_155_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_186_);
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_153_ = stack[0].m_obj;
lean_object* v_a_154_ = stack[1].m_obj;
lean_object* v_a_155_ = stack[2].m_obj;
lean_object* v_a_156_ = stack[3].m_obj;
lean_object* v_a_157_ = stack[4].m_obj;
lean_object* v_a_158_ = stack[5].m_obj;
lean_object* v_a_159_ = stack[6].m_obj;
lean_object* v_a_160_ = stack[7].m_obj;
lean_object* v_a_161_ = stack[8].m_obj;
lean_object* v_a_162_ = stack[9].m_obj;
lean_object* v_a_163_ = stack[10].m_obj;
lean_object* v_a_164_ = stack[11].m_obj;
lean_object* v_a_165_ = stack[12].m_obj;
lean_object* v_a_166_ = stack[13].m_obj;
lean_object* v_a_167_ = stack[14].m_obj;
lean_object* v_res_198_;
v_res_198_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState(v_s_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState___boxed(lean_object* v_s_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_setBVState(v_s_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_215_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_b_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_array_221_; lean_object* v_start_222_; lean_object* v_stop_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_251_; 
v_array_221_ = lean_ctor_get(v_a_217_, 0);
v_start_222_ = lean_ctor_get(v_a_217_, 1);
v_stop_223_ = lean_ctor_get(v_a_217_, 2);
v_isSharedCheck_251_ = !lean_is_exclusive(v_a_217_);
if (v_isSharedCheck_251_ == 0)
{
v___x_225_ = v_a_217_;
v_isShared_226_ = v_isSharedCheck_251_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_stop_223_);
lean_inc(v_start_222_);
lean_inc(v_array_221_);
lean_dec(v_a_217_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_251_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_lt(v_start_222_, v_stop_223_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_del_object(v___x_225_);
lean_dec(v_stop_223_);
lean_dec(v_start_222_);
lean_dec_ref(v_array_221_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v_b_218_);
return v___x_228_;
}
else
{
lean_object* v_ref_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v_ref_229_ = lean_ctor_get(v___y_219_, 2);
v___x_230_ = lean_box(0);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_start_222_, v___x_231_);
lean_inc_ref(v_array_221_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_232_);
v___x_234_ = v___x_225_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_array_221_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_stop_223_);
v___x_234_ = v_reuseFailAlloc_250_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_array_fget(v_array_221_, v_start_222_);
lean_dec(v_start_222_);
lean_dec_ref(v_array_221_);
v___x_236_ = l_Lean_Cadical_Solver_clause(v_a_216_, v___x_235_);
lean_dec(v___x_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_dec_ref_known(v___x_236_, 1);
v_a_217_ = v___x_234_;
v_b_218_ = v___x_230_;
goto _start;
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v___x_234_);
v_a_238_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_249_ == 0)
{
v___x_240_ = v___x_236_;
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_242_ = lean_io_error_to_string(v_a_238_);
v___x_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___x_244_ = l_Lean_MessageData_ofFormat(v___x_243_);
lean_inc(v_ref_229_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_ref_229_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_245_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_216_ = stack[0].m_obj;
lean_object* v_a_217_ = stack[1].m_obj;
lean_object* v_b_218_ = stack[2].m_obj;
lean_object* v___y_219_ = stack[3].m_obj;
lean_object* v_res_252_;
v_res_252_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(v_a_216_, v_a_217_, v_b_218_, v___y_219_);
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg___boxed(lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(v_a_253_, v_a_254_, v_b_255_, v___y_256_);
lean_dec_ref(v___y_256_);
lean_dec_ref(v_a_253_);
return v_res_258_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(lean_object* v_prevCnfSize_259_, lean_object* v_current_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_262_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v_lower_279_; lean_object* v_upper_280_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v_current_260_);
v___x_294_ = lean_nat_dec_le(v_prevCnfSize_259_, v___x_292_);
if (v___x_294_ == 0)
{
v_lower_279_ = v_prevCnfSize_259_;
v_upper_280_ = v___x_293_;
goto v___jp_278_;
}
else
{
lean_dec(v_prevCnfSize_259_);
v_lower_279_ = v___x_292_;
v_upper_280_ = v___x_293_;
goto v___jp_278_;
}
v___jp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = l_Array_toSubarray___redArg(v_current_260_, v_lower_279_, v_upper_280_);
v___x_282_ = lean_box(0);
v___x_283_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(v_a_277_, v___x_281_, v___x_282_, v_a_273_);
lean_dec(v_a_277_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; 
v_unused_291_ = lean_ctor_get(v___x_283_, 0);
lean_dec(v_unused_291_);
v___x_285_ = v___x_283_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_dec(v___x_283_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_282_);
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_282_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
return v___x_283_;
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v_current_260_);
lean_dec(v_prevCnfSize_259_);
v_a_295_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_276_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_276_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_0interp(lean_interpreter_value* stack)
{
lean_object* v_prevCnfSize_259_ = stack[0].m_obj;
lean_object* v_current_260_ = stack[1].m_obj;
lean_object* v_a_261_ = stack[2].m_obj;
lean_object* v_a_262_ = stack[3].m_obj;
lean_object* v_a_263_ = stack[4].m_obj;
lean_object* v_a_264_ = stack[5].m_obj;
lean_object* v_a_265_ = stack[6].m_obj;
lean_object* v_a_266_ = stack[7].m_obj;
lean_object* v_a_267_ = stack[8].m_obj;
lean_object* v_a_268_ = stack[9].m_obj;
lean_object* v_a_269_ = stack[10].m_obj;
lean_object* v_a_270_ = stack[11].m_obj;
lean_object* v_a_271_ = stack[12].m_obj;
lean_object* v_a_272_ = stack[13].m_obj;
lean_object* v_a_273_ = stack[14].m_obj;
lean_object* v_a_274_ = stack[15].m_obj;
lean_object* v_res_303_;
v_res_303_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v_prevCnfSize_259_, v_current_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf___boxed(lean_object** _args){
lean_object* v_prevCnfSize_304_ = _args[0];
lean_object* v_current_305_ = _args[1];
lean_object* v_a_306_ = _args[2];
lean_object* v_a_307_ = _args[3];
lean_object* v_a_308_ = _args[4];
lean_object* v_a_309_ = _args[5];
lean_object* v_a_310_ = _args[6];
lean_object* v_a_311_ = _args[7];
lean_object* v_a_312_ = _args[8];
lean_object* v_a_313_ = _args[9];
lean_object* v_a_314_ = _args[10];
lean_object* v_a_315_ = _args[11];
lean_object* v_a_316_ = _args[12];
lean_object* v_a_317_ = _args[13];
lean_object* v_a_318_ = _args[14];
lean_object* v_a_319_ = _args[15];
lean_object* v_a_320_ = _args[16];
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v_prevCnfSize_304_, v_current_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
return v_res_321_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0(lean_object* v_a_322_, lean_object* v_inst_323_, lean_object* v_R_324_, lean_object* v_a_325_, lean_object* v_b_326_, lean_object* v_c_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___redArg(v_a_322_, v_a_325_, v_b_326_, v___y_340_);
return v___x_343_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_322_ = stack[0].m_obj;
lean_object* v_a_325_ = stack[3].m_obj;
lean_object* v_b_326_ = stack[4].m_obj;
lean_object* v___y_328_ = stack[6].m_obj;
lean_object* v___y_329_ = stack[7].m_obj;
lean_object* v___y_330_ = stack[8].m_obj;
lean_object* v___y_331_ = stack[9].m_obj;
lean_object* v___y_332_ = stack[10].m_obj;
lean_object* v___y_333_ = stack[11].m_obj;
lean_object* v___y_334_ = stack[12].m_obj;
lean_object* v___y_335_ = stack[13].m_obj;
lean_object* v___y_336_ = stack[14].m_obj;
lean_object* v___y_337_ = stack[15].m_obj;
lean_object* v___y_338_ = stack[16].m_obj;
lean_object* v___y_339_ = stack[17].m_obj;
lean_object* v___y_340_ = stack[18].m_obj;
lean_object* v___y_341_ = stack[19].m_obj;
lean_object* v_res_344_;
v_res_344_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0(v_a_322_, lean_box(0), lean_box(0), v_a_325_, v_b_326_, lean_box(0), v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0___boxed(lean_object** _args){
lean_object* v_a_345_ = _args[0];
lean_object* v_inst_346_ = _args[1];
lean_object* v_R_347_ = _args[2];
lean_object* v_a_348_ = _args[3];
lean_object* v_b_349_ = _args[4];
lean_object* v_c_350_ = _args[5];
lean_object* v___y_351_ = _args[6];
lean_object* v___y_352_ = _args[7];
lean_object* v___y_353_ = _args[8];
lean_object* v___y_354_ = _args[9];
lean_object* v___y_355_ = _args[10];
lean_object* v___y_356_ = _args[11];
lean_object* v___y_357_ = _args[12];
lean_object* v___y_358_ = _args[13];
lean_object* v___y_359_ = _args[14];
lean_object* v___y_360_ = _args[15];
lean_object* v___y_361_ = _args[16];
lean_object* v___y_362_ = _args[17];
lean_object* v___y_363_ = _args[18];
lean_object* v___y_364_ = _args[19];
lean_object* v___y_365_ = _args[20];
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf_spec__0(v_a_345_, v_inst_346_, v_R_347_, v_a_348_, v_b_349_, v_c_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec_ref(v_a_345_);
return v_res_366_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(lean_object* v_upperBound_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_b_370_, lean_object* v___y_371_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_nat_dec_lt(v_a_369_, v_upperBound_367_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_b_370_);
return v___x_374_;
}
else
{
lean_object* v_ref_375_; lean_object* v___x_376_; 
v_ref_375_ = lean_ctor_get(v___y_371_, 2);
lean_inc_ref(v_a_368_);
v___x_376_ = l_Lean_Cadical_Solver_val(v_a_368_, v_a_369_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
lean_inc(v_a_369_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_a_377_);
lean_ctor_set(v___x_378_, 1, v_a_369_);
v___x_379_ = lean_array_push(v_b_370_, v___x_378_);
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_nat_add(v_a_369_, v___x_380_);
lean_dec(v_a_369_);
v_a_369_ = v___x_381_;
v_b_370_ = v___x_379_;
goto _start;
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v_b_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
v_a_383_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_394_ == 0)
{
v___x_385_ = v___x_376_;
v_isShared_386_ = v_isSharedCheck_394_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_376_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_394_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_387_ = lean_io_error_to_string(v_a_383_);
v___x_388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = l_Lean_MessageData_ofFormat(v___x_388_);
lean_inc(v_ref_375_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_ref_375_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_390_);
v___x_392_ = v___x_385_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_367_ = stack[0].m_obj;
lean_object* v_a_368_ = stack[1].m_obj;
lean_object* v_a_369_ = stack[2].m_obj;
lean_object* v_b_370_ = stack[3].m_obj;
lean_object* v___y_371_ = stack[4].m_obj;
lean_object* v_res_395_;
v_res_395_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(v_upperBound_367_, v_a_368_, v_a_369_, v_b_370_, v___y_371_);
stack->m_obj
 = v_res_395_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg___boxed(lean_object* v_upperBound_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(v_upperBound_396_, v_a_397_, v_a_398_, v_b_399_, v___y_400_);
lean_dec_ref(v___y_400_);
lean_dec(v_upperBound_396_);
return v_res_402_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(lean_object* v_aigSize_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v_a_405_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v___x_421_ = lean_mk_empty_array_with_capacity(v_aigSize_403_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(v_aigSize_403_, v_a_420_, v___x_422_, v___x_421_, v_a_416_);
return v___x_423_;
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_424_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_419_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_419_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_0interp(lean_interpreter_value* stack)
{
lean_object* v_aigSize_403_ = stack[0].m_obj;
lean_object* v_a_404_ = stack[1].m_obj;
lean_object* v_a_405_ = stack[2].m_obj;
lean_object* v_a_406_ = stack[3].m_obj;
lean_object* v_a_407_ = stack[4].m_obj;
lean_object* v_a_408_ = stack[5].m_obj;
lean_object* v_a_409_ = stack[6].m_obj;
lean_object* v_a_410_ = stack[7].m_obj;
lean_object* v_a_411_ = stack[8].m_obj;
lean_object* v_a_412_ = stack[9].m_obj;
lean_object* v_a_413_ = stack[10].m_obj;
lean_object* v_a_414_ = stack[11].m_obj;
lean_object* v_a_415_ = stack[12].m_obj;
lean_object* v_a_416_ = stack[13].m_obj;
lean_object* v_a_417_ = stack[14].m_obj;
lean_object* v_res_432_;
v_res_432_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v_aigSize_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment___boxed(lean_object* v_aigSize_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v_aigSize_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_aigSize_433_);
return v_res_449_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0(lean_object* v_upperBound_450_, lean_object* v_a_451_, lean_object* v_inst_452_, lean_object* v_R_453_, lean_object* v_a_454_, lean_object* v_b_455_, lean_object* v_c_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___redArg(v_upperBound_450_, v_a_451_, v_a_454_, v_b_455_, v___y_469_);
return v___x_472_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_450_ = stack[0].m_obj;
lean_object* v_a_451_ = stack[1].m_obj;
lean_object* v_a_454_ = stack[4].m_obj;
lean_object* v_b_455_ = stack[5].m_obj;
lean_object* v___y_457_ = stack[7].m_obj;
lean_object* v___y_458_ = stack[8].m_obj;
lean_object* v___y_459_ = stack[9].m_obj;
lean_object* v___y_460_ = stack[10].m_obj;
lean_object* v___y_461_ = stack[11].m_obj;
lean_object* v___y_462_ = stack[12].m_obj;
lean_object* v___y_463_ = stack[13].m_obj;
lean_object* v___y_464_ = stack[14].m_obj;
lean_object* v___y_465_ = stack[15].m_obj;
lean_object* v___y_466_ = stack[16].m_obj;
lean_object* v___y_467_ = stack[17].m_obj;
lean_object* v___y_468_ = stack[18].m_obj;
lean_object* v___y_469_ = stack[19].m_obj;
lean_object* v___y_470_ = stack[20].m_obj;
lean_object* v_res_473_;
v_res_473_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0(v_upperBound_450_, v_a_451_, lean_box(0), lean_box(0), v_a_454_, v_b_455_, lean_box(0), v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_474_ = _args[0];
lean_object* v_a_475_ = _args[1];
lean_object* v_inst_476_ = _args[2];
lean_object* v_R_477_ = _args[3];
lean_object* v_a_478_ = _args[4];
lean_object* v_b_479_ = _args[5];
lean_object* v_c_480_ = _args[6];
lean_object* v___y_481_ = _args[7];
lean_object* v___y_482_ = _args[8];
lean_object* v___y_483_ = _args[9];
lean_object* v___y_484_ = _args[10];
lean_object* v___y_485_ = _args[11];
lean_object* v___y_486_ = _args[12];
lean_object* v___y_487_ = _args[13];
lean_object* v___y_488_ = _args[14];
lean_object* v___y_489_ = _args[15];
lean_object* v___y_490_ = _args[16];
lean_object* v___y_491_ = _args[17];
lean_object* v___y_492_ = _args[18];
lean_object* v___y_493_ = _args[19];
lean_object* v___y_494_ = _args[20];
lean_object* v___y_495_ = _args[21];
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment_spec__0(v_upperBound_474_, v_a_475_, v_inst_476_, v_R_477_, v_a_478_, v_b_479_, v_c_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
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
lean_dec(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v_upperBound_474_);
return v_res_496_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_box(0);
v___x_498_ = l_Lean_interruptExceptionId;
v___x_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
return v___x_499_;
}
}
lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg(){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0, &l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___closed__0);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_503_;
v_res_503_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
stack->m_obj
 = v_res_503_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg___boxed(lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
return v_res_505_;
}
}
lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0(lean_object* v_00_u03b1_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
return v___x_522_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_507_ = stack[1].m_obj;
lean_object* v___y_508_ = stack[2].m_obj;
lean_object* v___y_509_ = stack[3].m_obj;
lean_object* v___y_510_ = stack[4].m_obj;
lean_object* v___y_511_ = stack[5].m_obj;
lean_object* v___y_512_ = stack[6].m_obj;
lean_object* v___y_513_ = stack[7].m_obj;
lean_object* v___y_514_ = stack[8].m_obj;
lean_object* v___y_515_ = stack[9].m_obj;
lean_object* v___y_516_ = stack[10].m_obj;
lean_object* v___y_517_ = stack[11].m_obj;
lean_object* v___y_518_ = stack[12].m_obj;
lean_object* v___y_519_ = stack[13].m_obj;
lean_object* v___y_520_ = stack[14].m_obj;
lean_object* v_res_523_;
v_res_523_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0(lean_box(0), v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___boxed(lean_object* v_00_u03b1_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0(v_00_u03b1_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_540_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(lean_object* v_a_541_, lean_object* v___x_542_, lean_object* v_____r_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint32_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_satExpr_562_; lean_object* v_hypQueue_563_; lean_object* v_usedHyps_564_; uint8_t v_didChange_565_; lean_object* v_theoryState_566_; lean_object* v_solverTimeBudgetMs_567_; lean_object* v_roundBudget_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_584_; 
v___x_559_ = lean_uint32_of_nat(v_a_541_);
v___x_560_ = l_IO_sleep(v___x_559_);
v___x_561_ = lean_st_ref_take(v___y_545_);
v_satExpr_562_ = lean_ctor_get(v___x_561_, 0);
v_hypQueue_563_ = lean_ctor_get(v___x_561_, 1);
v_usedHyps_564_ = lean_ctor_get(v___x_561_, 2);
v_didChange_565_ = lean_ctor_get_uint8(v___x_561_, sizeof(void*)*6);
v_theoryState_566_ = lean_ctor_get(v___x_561_, 3);
v_solverTimeBudgetMs_567_ = lean_ctor_get(v___x_561_, 4);
v_roundBudget_568_ = lean_ctor_get(v___x_561_, 5);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_584_ == 0)
{
v___x_570_ = v___x_561_;
v_isShared_571_ = v_isSharedCheck_584_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_roundBudget_568_);
lean_inc(v_solverTimeBudgetMs_567_);
lean_inc(v_theoryState_566_);
lean_inc(v_usedHyps_564_);
lean_inc(v_hypQueue_563_);
lean_inc(v_satExpr_562_);
lean_dec(v___x_561_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_584_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = lean_nat_sub(v_solverTimeBudgetMs_567_, v_a_541_);
lean_dec(v_solverTimeBudgetMs_567_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 4, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_satExpr_562_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_hypQueue_563_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_usedHyps_564_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_theoryState_566_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_583_, 5, v_roundBudget_568_);
lean_ctor_set_uint8(v_reuseFailAlloc_583_, sizeof(void*)*6, v_didChange_565_);
v___x_574_ = v_reuseFailAlloc_583_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___y_577_; uint8_t v___x_580_; 
v___x_575_ = lean_st_ref_put(v___y_545_, v___x_574_);
v___x_580_ = lean_nat_dec_le(v___x_542_, v_a_541_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(2u);
v___x_582_ = lean_nat_mul(v_a_541_, v___x_581_);
lean_dec(v_a_541_);
v___y_577_ = v___x_582_;
goto v___jp_576_;
}
else
{
v___y_577_ = v_a_541_;
goto v___jp_576_;
}
v___jp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___y_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_541_ = stack[0].m_obj;
lean_object* v___x_542_ = stack[1].m_obj;
lean_object* v_____r_543_ = stack[2].m_obj;
lean_object* v___y_544_ = stack[3].m_obj;
lean_object* v___y_545_ = stack[4].m_obj;
lean_object* v___y_546_ = stack[5].m_obj;
lean_object* v___y_547_ = stack[6].m_obj;
lean_object* v___y_548_ = stack[7].m_obj;
lean_object* v___y_549_ = stack[8].m_obj;
lean_object* v___y_550_ = stack[9].m_obj;
lean_object* v___y_551_ = stack[10].m_obj;
lean_object* v___y_552_ = stack[11].m_obj;
lean_object* v___y_553_ = stack[12].m_obj;
lean_object* v___y_554_ = stack[13].m_obj;
lean_object* v___y_555_ = stack[14].m_obj;
lean_object* v___y_556_ = stack[15].m_obj;
lean_object* v___y_557_ = stack[16].m_obj;
lean_object* v_res_585_;
v_res_585_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_541_, v___x_542_, v_____r_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_586_ = _args[0];
lean_object* v___x_587_ = _args[1];
lean_object* v_____r_588_ = _args[2];
lean_object* v___y_589_ = _args[3];
lean_object* v___y_590_ = _args[4];
lean_object* v___y_591_ = _args[5];
lean_object* v___y_592_ = _args[6];
lean_object* v___y_593_ = _args[7];
lean_object* v___y_594_ = _args[8];
lean_object* v___y_595_ = _args[9];
lean_object* v___y_596_ = _args[10];
lean_object* v___y_597_ = _args[11];
lean_object* v___y_598_ = _args[12];
lean_object* v___y_599_ = _args[13];
lean_object* v___y_600_ = _args[14];
lean_object* v___y_601_ = _args[15];
lean_object* v___y_602_ = _args[16];
lean_object* v___y_603_ = _args[17];
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_586_, v___x_587_, v_____r_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___x_587_);
return v_res_604_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(lean_object* v_val_605_, lean_object* v_solver_606_, lean_object* v_a_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___y_624_; lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_644_ = lean_unsigned_to_nat(64u);
v___x_645_ = lean_io_get_task_state(v_val_605_);
v___x_646_ = lean_box(v___x_645_);
v___x_647_ = lean_obj_tag_nat(v___x_646_);
lean_dec(v___x_646_);
v___x_648_ = lean_unsigned_to_nat(2u);
v___x_649_ = lean_nat_dec_eq(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v_solverTimeBudgetMs_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_650_ = lean_st_ref_get(v___y_609_);
v_solverTimeBudgetMs_651_ = lean_ctor_get(v___x_650_, 4);
lean_inc(v_solverTimeBudgetMs_651_);
lean_dec(v___x_650_);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = lean_nat_dec_eq(v_solverTimeBudgetMs_651_, v___x_652_);
lean_dec(v_solverTimeBudgetMs_651_);
if (v___x_653_ == 0)
{
lean_object* v_toCold_654_; lean_object* v_cancelTk_x3f_655_; 
v_toCold_654_ = lean_ctor_get(v___y_620_, 0);
v_cancelTk_x3f_655_ = lean_ctor_get(v_toCold_654_, 10);
if (lean_obj_tag(v_cancelTk_x3f_655_) == 1)
{
lean_object* v_val_656_; uint8_t v___x_657_; 
v_val_656_ = lean_ctor_get(v_cancelTk_x3f_655_, 0);
v___x_657_ = l_IO_CancelToken_isSet(v_val_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_box(0);
v___x_659_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_607_, v___x_644_, v___x_658_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
v___y_624_ = v___x_659_;
goto v___jp_623_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = l_Lean_Cadical_Solver_terminate(v_solver_606_);
v___x_661_ = l_Lean_throwInterruptException___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__0___redArg();
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_607_, v___x_644_, v_a_662_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
v___y_624_ = v___x_663_;
goto v___jp_623_;
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_a_607_);
v_a_664_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_661_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_661_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(0);
v___x_673_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___lam__0(v_a_607_, v___x_644_, v___x_672_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
v___y_624_ = v___x_673_;
goto v___jp_623_;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = l_Lean_Cadical_Solver_terminate(v_solver_606_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v_a_607_);
return v___x_675_;
}
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_a_607_);
return v___x_676_;
}
v___jp_623_:
{
if (lean_obj_tag(v___y_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_635_; 
v_a_625_ = lean_ctor_get(v___y_624_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___y_624_);
if (v_isSharedCheck_635_ == 0)
{
v___x_627_ = v___y_624_;
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___y_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
if (lean_obj_tag(v_a_625_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; 
v_a_629_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v_a_625_, 1);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v_a_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v_a_633_; 
lean_del_object(v___x_627_);
v_a_633_ = lean_ctor_get(v_a_625_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v_a_625_, 1);
v_a_607_ = v_a_633_;
goto _start;
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
v_a_636_ = lean_ctor_get(v___y_624_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___y_624_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___y_624_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___y_624_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_605_ = stack[0].m_obj;
lean_object* v_solver_606_ = stack[1].m_obj;
lean_object* v_a_607_ = stack[2].m_obj;
lean_object* v___y_608_ = stack[3].m_obj;
lean_object* v___y_609_ = stack[4].m_obj;
lean_object* v___y_610_ = stack[5].m_obj;
lean_object* v___y_611_ = stack[6].m_obj;
lean_object* v___y_612_ = stack[7].m_obj;
lean_object* v___y_613_ = stack[8].m_obj;
lean_object* v___y_614_ = stack[9].m_obj;
lean_object* v___y_615_ = stack[10].m_obj;
lean_object* v___y_616_ = stack[11].m_obj;
lean_object* v___y_617_ = stack[12].m_obj;
lean_object* v___y_618_ = stack[13].m_obj;
lean_object* v___y_619_ = stack[14].m_obj;
lean_object* v___y_620_ = stack[15].m_obj;
lean_object* v___y_621_ = stack[16].m_obj;
lean_object* v_res_677_;
v_res_677_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v_val_605_, v_solver_606_, v_a_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_val_678_ = _args[0];
lean_object* v_solver_679_ = _args[1];
lean_object* v_a_680_ = _args[2];
lean_object* v___y_681_ = _args[3];
lean_object* v___y_682_ = _args[4];
lean_object* v___y_683_ = _args[5];
lean_object* v___y_684_ = _args[6];
lean_object* v___y_685_ = _args[7];
lean_object* v___y_686_ = _args[8];
lean_object* v___y_687_ = _args[9];
lean_object* v___y_688_ = _args[10];
lean_object* v___y_689_ = _args[11];
lean_object* v___y_690_ = _args[12];
lean_object* v___y_691_ = _args[13];
lean_object* v___y_692_ = _args[14];
lean_object* v___y_693_ = _args[15];
lean_object* v___y_694_ = _args[16];
lean_object* v___y_695_ = _args[17];
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v_val_678_, v_solver_679_, v_a_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v_solver_679_);
lean_dec_ref(v_val_678_);
return v_res_696_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(lean_object* v_solver_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_inc_ref(v_solver_697_);
v___x_713_ = lean_alloc_closure((void*)(l_Lean_Cadical_Solver_solve___boxed), 2, 1);
lean_closure_set(v___x_713_, 0, v_solver_697_);
v___x_714_ = lean_unsigned_to_nat(9u);
v___x_715_ = lean_io_as_task(v___x_713_, v___x_714_);
v___x_716_ = lean_unsigned_to_nat(1u);
v___x_717_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v___x_715_, v_solver_697_, v___x_716_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec_ref(v_solver_697_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_725_; 
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_726_);
v___x_719_ = v___x_717_;
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_717_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = lean_task_get_own(v___x_715_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_721_);
v___x_723_ = v___x_719_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v___x_715_);
v_a_727_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_717_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_717_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_0interp(lean_interpreter_value* stack)
{
lean_object* v_solver_697_ = stack[0].m_obj;
lean_object* v_a_698_ = stack[1].m_obj;
lean_object* v_a_699_ = stack[2].m_obj;
lean_object* v_a_700_ = stack[3].m_obj;
lean_object* v_a_701_ = stack[4].m_obj;
lean_object* v_a_702_ = stack[5].m_obj;
lean_object* v_a_703_ = stack[6].m_obj;
lean_object* v_a_704_ = stack[7].m_obj;
lean_object* v_a_705_ = stack[8].m_obj;
lean_object* v_a_706_ = stack[9].m_obj;
lean_object* v_a_707_ = stack[10].m_obj;
lean_object* v_a_708_ = stack[11].m_obj;
lean_object* v_a_709_ = stack[12].m_obj;
lean_object* v_a_710_ = stack[13].m_obj;
lean_object* v_a_711_ = stack[14].m_obj;
lean_object* v_res_735_;
v_res_735_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v_solver_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver___boxed(lean_object* v_solver_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v_solver_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_752_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1(lean_object* v_val_753_, lean_object* v_solver_754_, lean_object* v_inst_755_, lean_object* v_a_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___redArg(v_val_753_, v_solver_754_, v_a_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
return v___x_772_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_753_ = stack[0].m_obj;
lean_object* v_solver_754_ = stack[1].m_obj;
lean_object* v_a_756_ = stack[3].m_obj;
lean_object* v___y_757_ = stack[4].m_obj;
lean_object* v___y_758_ = stack[5].m_obj;
lean_object* v___y_759_ = stack[6].m_obj;
lean_object* v___y_760_ = stack[7].m_obj;
lean_object* v___y_761_ = stack[8].m_obj;
lean_object* v___y_762_ = stack[9].m_obj;
lean_object* v___y_763_ = stack[10].m_obj;
lean_object* v___y_764_ = stack[11].m_obj;
lean_object* v___y_765_ = stack[12].m_obj;
lean_object* v___y_766_ = stack[13].m_obj;
lean_object* v___y_767_ = stack[14].m_obj;
lean_object* v___y_768_ = stack[15].m_obj;
lean_object* v___y_769_ = stack[16].m_obj;
lean_object* v___y_770_ = stack[17].m_obj;
lean_object* v_res_773_;
v_res_773_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1(v_val_753_, v_solver_754_, lean_box(0), v_a_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1___boxed(lean_object** _args){
lean_object* v_val_774_ = _args[0];
lean_object* v_solver_775_ = _args[1];
lean_object* v_inst_776_ = _args[2];
lean_object* v_a_777_ = _args[3];
lean_object* v___y_778_ = _args[4];
lean_object* v___y_779_ = _args[5];
lean_object* v___y_780_ = _args[6];
lean_object* v___y_781_ = _args[7];
lean_object* v___y_782_ = _args[8];
lean_object* v___y_783_ = _args[9];
lean_object* v___y_784_ = _args[10];
lean_object* v___y_785_ = _args[11];
lean_object* v___y_786_ = _args[12];
lean_object* v___y_787_ = _args[13];
lean_object* v___y_788_ = _args[14];
lean_object* v___y_789_ = _args[15];
lean_object* v___y_790_ = _args[16];
lean_object* v___y_791_ = _args[17];
lean_object* v___y_792_ = _args[18];
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver_spec__1(v_val_774_, v_solver_775_, v_inst_776_, v_a_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec_ref(v_solver_775_);
lean_dec_ref(v_val_774_);
return v_res_793_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_box(0);
v___x_799_ = lean_unsigned_to_nat(16u);
v___x_800_ = lean_mk_array(v___x_799_, v___x_798_);
return v___x_800_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__1);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__2);
v___x_805_ = ((lean_object*)(l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__0));
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0(void){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = lean_obj_once(&l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3, &l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3_once, _init_l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0___closed__3);
return v___x_807_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_unsigned_to_nat(32u);
v___x_809_ = lean_mk_empty_array_with_capacity(v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_811_ = ((size_t)5ULL);
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_unsigned_to_nat(32u);
v___x_814_ = lean_mk_empty_array_with_capacity(v___x_813_);
v___x_815_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__0);
v___x_816_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
lean_ctor_set(v___x_816_, 2, v___x_812_);
lean_ctor_set(v___x_816_, 3, v___x_812_);
lean_ctor_set_usize(v___x_816_, 4, v___x_811_);
return v___x_816_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; lean_object* v_traceState_820_; lean_object* v_traces_821_; lean_object* v___x_822_; lean_object* v_traceState_823_; lean_object* v_env_824_; lean_object* v_nextMacroScope_825_; lean_object* v_ngen_826_; lean_object* v_auxDeclNGen_827_; lean_object* v_cache_828_; lean_object* v_recordedDeps_829_; lean_object* v_messages_830_; lean_object* v_infoState_831_; lean_object* v_snapshotTasks_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_851_; 
v___x_819_ = lean_st_ref_get(v___y_817_);
v_traceState_820_ = lean_ctor_get(v___x_819_, 4);
lean_inc_ref(v_traceState_820_);
lean_dec(v___x_819_);
v_traces_821_ = lean_ctor_get(v_traceState_820_, 0);
lean_inc_ref(v_traces_821_);
lean_dec_ref(v_traceState_820_);
v___x_822_ = lean_st_ref_take(v___y_817_);
v_traceState_823_ = lean_ctor_get(v___x_822_, 4);
v_env_824_ = lean_ctor_get(v___x_822_, 0);
v_nextMacroScope_825_ = lean_ctor_get(v___x_822_, 1);
v_ngen_826_ = lean_ctor_get(v___x_822_, 2);
v_auxDeclNGen_827_ = lean_ctor_get(v___x_822_, 3);
v_cache_828_ = lean_ctor_get(v___x_822_, 5);
v_recordedDeps_829_ = lean_ctor_get(v___x_822_, 6);
v_messages_830_ = lean_ctor_get(v___x_822_, 7);
v_infoState_831_ = lean_ctor_get(v___x_822_, 8);
v_snapshotTasks_832_ = lean_ctor_get(v___x_822_, 9);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_851_ == 0)
{
v___x_834_ = v___x_822_;
v_isShared_835_ = v_isSharedCheck_851_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snapshotTasks_832_);
lean_inc(v_infoState_831_);
lean_inc(v_messages_830_);
lean_inc(v_recordedDeps_829_);
lean_inc(v_cache_828_);
lean_inc(v_traceState_823_);
lean_inc(v_auxDeclNGen_827_);
lean_inc(v_ngen_826_);
lean_inc(v_nextMacroScope_825_);
lean_inc(v_env_824_);
lean_dec(v___x_822_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_851_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
uint64_t v_tid_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_849_; 
v_tid_836_ = lean_ctor_get_uint64(v_traceState_823_, sizeof(void*)*1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_traceState_823_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_traceState_823_, 0);
lean_dec(v_unused_850_);
v___x_838_ = v_traceState_823_;
v_isShared_839_ = v_isSharedCheck_849_;
goto v_resetjp_837_;
}
else
{
lean_dec(v_traceState_823_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_849_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___closed__1);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_840_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_840_);
lean_ctor_set_uint64(v_reuseFailAlloc_848_, sizeof(void*)*1, v_tid_836_);
v___x_842_ = v_reuseFailAlloc_848_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v___x_842_);
v___x_844_ = v___x_834_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_env_824_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_nextMacroScope_825_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_ngen_826_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v_auxDeclNGen_827_);
lean_ctor_set(v_reuseFailAlloc_847_, 4, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_847_, 5, v_cache_828_);
lean_ctor_set(v_reuseFailAlloc_847_, 6, v_recordedDeps_829_);
lean_ctor_set(v_reuseFailAlloc_847_, 7, v_messages_830_);
lean_ctor_set(v_reuseFailAlloc_847_, 8, v_infoState_831_);
lean_ctor_set(v_reuseFailAlloc_847_, 9, v_snapshotTasks_832_);
v___x_844_ = v_reuseFailAlloc_847_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_st_ref_put(v___y_817_, v___x_844_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_traces_821_);
return v___x_846_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_817_ = stack[0].m_obj;
lean_object* v_res_852_;
v_res_852_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_817_);
stack->m_obj
 = v_res_852_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg___boxed(lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_853_);
lean_dec(v___y_853_);
return v_res_855_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4(lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_869_);
return v___x_871_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_856_ = stack[0].m_obj;
lean_object* v___y_857_ = stack[1].m_obj;
lean_object* v___y_858_ = stack[2].m_obj;
lean_object* v___y_859_ = stack[3].m_obj;
lean_object* v___y_860_ = stack[4].m_obj;
lean_object* v___y_861_ = stack[5].m_obj;
lean_object* v___y_862_ = stack[6].m_obj;
lean_object* v___y_863_ = stack[7].m_obj;
lean_object* v___y_864_ = stack[8].m_obj;
lean_object* v___y_865_ = stack[9].m_obj;
lean_object* v___y_866_ = stack[10].m_obj;
lean_object* v___y_867_ = stack[11].m_obj;
lean_object* v___y_868_ = stack[12].m_obj;
lean_object* v___y_869_ = stack[13].m_obj;
lean_object* v_res_872_;
v_res_872_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4(v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___boxed(lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4(v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_888_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(lean_object* v_opts_889_, lean_object* v_opt_890_){
_start:
{
lean_object* v_name_891_; lean_object* v_defValue_892_; lean_object* v_map_893_; lean_object* v___x_894_; 
v_name_891_ = lean_ctor_get(v_opt_890_, 0);
v_defValue_892_ = lean_ctor_get(v_opt_890_, 1);
v_map_893_ = lean_ctor_get(v_opts_889_, 0);
v___x_894_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_893_, v_name_891_);
if (lean_obj_tag(v___x_894_) == 0)
{
uint8_t v___x_895_; 
v___x_895_ = lean_unbox(v_defValue_892_);
return v___x_895_;
}
else
{
lean_object* v_val_896_; 
v_val_896_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_894_, 1);
if (lean_obj_tag(v_val_896_) == 1)
{
uint8_t v_v_897_; 
v_v_897_ = lean_ctor_get_uint8(v_val_896_, 0);
lean_dec_ref_known(v_val_896_, 0);
return v_v_897_;
}
else
{
uint8_t v___x_898_; 
lean_dec(v_val_896_);
v___x_898_ = lean_unbox(v_defValue_892_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_889_ = stack[0].m_obj;
lean_object* v_opt_890_ = stack[1].m_obj;
uint8_t v_res_899_;
v_res_899_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_889_, v_opt_890_);
stack->m_num = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5___boxed(lean_object* v_opts_900_, lean_object* v_opt_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_900_, v_opt_901_);
lean_dec_ref(v_opt_901_);
lean_dec_ref(v_opts_900_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__1));
v___x_908_ = l_Lean_MessageData_ofFormat(v___x_907_);
return v___x_908_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0(lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___closed__2);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_909_ = stack[0].m_obj;
lean_object* v___y_910_ = stack[1].m_obj;
lean_object* v___y_911_ = stack[2].m_obj;
lean_object* v___y_912_ = stack[3].m_obj;
lean_object* v___y_913_ = stack[4].m_obj;
lean_object* v___y_914_ = stack[5].m_obj;
lean_object* v___y_915_ = stack[6].m_obj;
lean_object* v___y_916_ = stack[7].m_obj;
lean_object* v___y_917_ = stack[8].m_obj;
lean_object* v___y_918_ = stack[9].m_obj;
lean_object* v___y_919_ = stack[10].m_obj;
lean_object* v___y_920_ = stack[11].m_obj;
lean_object* v___y_921_ = stack[12].m_obj;
lean_object* v___y_922_ = stack[13].m_obj;
lean_object* v___y_923_ = stack[14].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0(v_x_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0___boxed(lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__0(v_x_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec_ref(v_x_928_);
return v_res_944_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__0));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1(lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___closed__1);
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_948_ = stack[0].m_obj;
lean_object* v___y_949_ = stack[1].m_obj;
lean_object* v___y_950_ = stack[2].m_obj;
lean_object* v___y_951_ = stack[3].m_obj;
lean_object* v___y_952_ = stack[4].m_obj;
lean_object* v___y_953_ = stack[5].m_obj;
lean_object* v___y_954_ = stack[6].m_obj;
lean_object* v___y_955_ = stack[7].m_obj;
lean_object* v___y_956_ = stack[8].m_obj;
lean_object* v___y_957_ = stack[9].m_obj;
lean_object* v___y_958_ = stack[10].m_obj;
lean_object* v___y_959_ = stack[11].m_obj;
lean_object* v___y_960_ = stack[12].m_obj;
lean_object* v___y_961_ = stack[13].m_obj;
lean_object* v___y_962_ = stack[14].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1(v_x_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1___boxed(lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__1(v_x_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v_x_967_);
return v_res_983_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__1));
v___x_988_ = l_Lean_MessageData_ofFormat(v___x_987_);
return v___x_988_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2(lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___closed__2);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_989_ = stack[0].m_obj;
lean_object* v___y_990_ = stack[1].m_obj;
lean_object* v___y_991_ = stack[2].m_obj;
lean_object* v___y_992_ = stack[3].m_obj;
lean_object* v___y_993_ = stack[4].m_obj;
lean_object* v___y_994_ = stack[5].m_obj;
lean_object* v___y_995_ = stack[6].m_obj;
lean_object* v___y_996_ = stack[7].m_obj;
lean_object* v___y_997_ = stack[8].m_obj;
lean_object* v___y_998_ = stack[9].m_obj;
lean_object* v___y_999_ = stack[10].m_obj;
lean_object* v___y_1000_ = stack[11].m_obj;
lean_object* v___y_1001_ = stack[12].m_obj;
lean_object* v___y_1002_ = stack[13].m_obj;
lean_object* v___y_1003_ = stack[14].m_obj;
lean_object* v_res_1007_;
v_res_1007_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2(v_x_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
stack->m_obj
 = v_res_1007_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2___boxed(lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__2(v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec_ref(v_x_1008_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3(lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v_result_1027_, lean_object* v___x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1025_, v___x_1026_, v_result_1027_, v___x_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed(lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v_result_1033_, lean_object* v___x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3(v___x_1031_, v___x_1032_, v_result_1033_, v___x_1034_, v_x_1035_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___x_1031_);
return v_res_1036_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(lean_object* v___f_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_ref_1050_; lean_object* v___x_1051_; 
v_ref_1050_ = lean_ctor_get(v___y_1047_, 2);
v___x_1051_ = l_IO_lazyPure___redArg(v___f_1037_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1071_; 
v_a_1060_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1062_ = v___x_1051_;
v_isShared_1063_ = v_isSharedCheck_1071_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1051_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1071_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1064_ = lean_io_error_to_string(v_a_1060_);
v___x_1065_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
v___x_1066_ = l_Lean_MessageData_ofFormat(v___x_1065_);
lean_inc(v_ref_1050_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_ref_1050_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1067_);
v___x_1069_ = v___x_1062_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1037_ = stack[0].m_obj;
lean_object* v___y_1038_ = stack[1].m_obj;
lean_object* v___y_1039_ = stack[2].m_obj;
lean_object* v___y_1040_ = stack[3].m_obj;
lean_object* v___y_1041_ = stack[4].m_obj;
lean_object* v___y_1042_ = stack[5].m_obj;
lean_object* v___y_1043_ = stack[6].m_obj;
lean_object* v___y_1044_ = stack[7].m_obj;
lean_object* v___y_1045_ = stack[8].m_obj;
lean_object* v___y_1046_ = stack[9].m_obj;
lean_object* v___y_1047_ = stack[10].m_obj;
lean_object* v___y_1048_ = stack[11].m_obj;
lean_object* v_res_1072_;
v_res_1072_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
stack->m_obj
 = v_res_1072_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4___boxed(lean_object* v___f_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5(lean_object* v_aig_1087_, lean_object* v_bvExpr_1088_, lean_object* v_blastCache_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblastWithCache_go(v_aig_1087_, v_bvExpr_1088_, v_blastCache_1089_);
return v___x_1091_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(lean_object* v___f_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_ref_1105_; lean_object* v___x_1106_; 
v_ref_1105_ = lean_ctor_get(v___y_1102_, 2);
v___x_1106_ = l_IO_lazyPure___redArg(v___f_1092_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
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
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1126_; 
v_a_1115_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1117_ = v___x_1106_;
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1106_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1119_ = lean_io_error_to_string(v_a_1115_);
v___x_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
v___x_1121_ = l_Lean_MessageData_ofFormat(v___x_1120_);
lean_inc(v_ref_1105_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_ref_1105_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1122_);
v___x_1124_ = v___x_1117_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1092_ = stack[0].m_obj;
lean_object* v___y_1093_ = stack[1].m_obj;
lean_object* v___y_1094_ = stack[2].m_obj;
lean_object* v___y_1095_ = stack[3].m_obj;
lean_object* v___y_1096_ = stack[4].m_obj;
lean_object* v___y_1097_ = stack[5].m_obj;
lean_object* v___y_1098_ = stack[6].m_obj;
lean_object* v___y_1099_ = stack[7].m_obj;
lean_object* v___y_1100_ = stack[8].m_obj;
lean_object* v___y_1101_ = stack[9].m_obj;
lean_object* v___y_1102_ = stack[10].m_obj;
lean_object* v___y_1103_ = stack[11].m_obj;
lean_object* v_res_1127_;
v_res_1127_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
stack->m_obj
 = v_res_1127_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6___boxed(lean_object* v___f_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__0));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7(lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___closed__1);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1145_ = stack[0].m_obj;
lean_object* v___y_1146_ = stack[1].m_obj;
lean_object* v___y_1147_ = stack[2].m_obj;
lean_object* v___y_1148_ = stack[3].m_obj;
lean_object* v___y_1149_ = stack[4].m_obj;
lean_object* v___y_1150_ = stack[5].m_obj;
lean_object* v___y_1151_ = stack[6].m_obj;
lean_object* v___y_1152_ = stack[7].m_obj;
lean_object* v___y_1153_ = stack[8].m_obj;
lean_object* v___y_1154_ = stack[9].m_obj;
lean_object* v___y_1155_ = stack[10].m_obj;
lean_object* v___y_1156_ = stack[11].m_obj;
lean_object* v___y_1157_ = stack[12].m_obj;
lean_object* v___y_1158_ = stack[13].m_obj;
lean_object* v___y_1159_ = stack[14].m_obj;
lean_object* v_res_1163_;
v_res_1163_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7(v_x_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
stack->m_obj
 = v_res_1163_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7___boxed(lean_object* v_x_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__7(v_x_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec_ref(v_x_1164_);
return v_res_1180_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(lean_object* v_x_1181_){
_start:
{
if (lean_obj_tag(v_x_1181_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v_x_1181_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v_x_1181_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v_x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 1);
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v_x_1181_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v_x_1181_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v_x_1181_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 0);
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1181_ = stack[0].m_obj;
lean_object* v_res_1199_;
v_res_1199_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_x_1181_);
stack->m_obj
 = v_res_1199_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg___boxed(lean_object* v_x_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_x_1200_);
return v_res_1202_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(lean_object* v_e_1203_){
_start:
{
if (lean_obj_tag(v_e_1203_) == 0)
{
uint8_t v___x_1204_; 
v___x_1204_ = 2;
return v___x_1204_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = 0;
return v___x_1205_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1203_ = stack[0].m_obj;
uint8_t v_res_1206_;
v_res_1206_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(v_e_1203_);
stack->m_num = v_res_1206_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10___boxed(lean_object* v_e_1207_){
_start:
{
uint8_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(v_e_1207_);
lean_dec_ref(v_e_1207_);
v_r_1209_ = lean_box(v_res_1208_);
return v_r_1209_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(lean_object* v_msgData_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v_env_1217_; uint8_t v___x_1218_; lean_object* v_env_1219_; lean_object* v___x_1220_; lean_object* v_toCold_1221_; lean_object* v_mctx_1222_; lean_object* v_lctx_1223_; lean_object* v_options_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1216_ = lean_st_ref_get(v___y_1214_);
v_env_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_env_1217_);
lean_dec(v___x_1216_);
v___x_1218_ = 0;
v_env_1219_ = l_Lean_Environment_setRecordingDeps(v_env_1217_, v___x_1218_);
v___x_1220_ = lean_st_ref_get(v___y_1212_);
v_toCold_1221_ = lean_ctor_get(v___y_1213_, 0);
v_mctx_1222_ = lean_ctor_get(v___x_1220_, 0);
lean_inc_ref(v_mctx_1222_);
lean_dec(v___x_1220_);
v_lctx_1223_ = lean_ctor_get(v___y_1211_, 2);
v_options_1224_ = lean_ctor_get(v_toCold_1221_, 2);
lean_inc_ref(v_options_1224_);
lean_inc_ref(v_lctx_1223_);
v___x_1225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1225_, 0, v_env_1219_);
lean_ctor_set(v___x_1225_, 1, v_mctx_1222_);
lean_ctor_set(v___x_1225_, 2, v_lctx_1223_);
lean_ctor_set(v___x_1225_, 3, v_options_1224_);
v___x_1226_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_msgData_1210_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1210_ = stack[0].m_obj;
lean_object* v___y_1211_ = stack[1].m_obj;
lean_object* v___y_1212_ = stack[2].m_obj;
lean_object* v___y_1213_ = stack[3].m_obj;
lean_object* v___y_1214_ = stack[4].m_obj;
lean_object* v_res_1228_;
v_res_1228_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msgData_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3___boxed(lean_object* v_msgData_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msgData_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
return v_res_1235_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(size_t v_sz_1236_, size_t v_i_1237_, lean_object* v_bs_1238_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
if (v___x_1239_ == 0)
{
return v_bs_1238_;
}
else
{
lean_object* v_v_1240_; lean_object* v_msg_1241_; lean_object* v___x_1242_; lean_object* v_bs_x27_1243_; size_t v___x_1244_; size_t v___x_1245_; lean_object* v___x_1246_; 
v_v_1240_ = lean_array_uget_borrowed(v_bs_1238_, v_i_1237_);
v_msg_1241_ = lean_ctor_get(v_v_1240_, 1);
lean_inc_ref(v_msg_1241_);
v___x_1242_ = lean_unsigned_to_nat(0u);
v_bs_x27_1243_ = lean_array_uset(v_bs_1238_, v_i_1237_, v___x_1242_);
v___x_1244_ = ((size_t)1ULL);
v___x_1245_ = lean_usize_add(v_i_1237_, v___x_1244_);
v___x_1246_ = lean_array_uset(v_bs_x27_1243_, v_i_1237_, v_msg_1241_);
v_i_1237_ = v___x_1245_;
v_bs_1238_ = v___x_1246_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1236_ = stack[0].m_num;
size_t v_i_1237_ = stack[1].m_num;
lean_object* v_bs_1238_ = stack[2].m_obj;
lean_object* v_res_1248_;
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(v_sz_1236_, v_i_1237_, v_bs_1238_);
stack->m_obj
 = v_res_1248_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9___boxed(lean_object* v_sz_1249_, lean_object* v_i_1250_, lean_object* v_bs_1251_){
_start:
{
size_t v_sz_boxed_1252_; size_t v_i_boxed_1253_; lean_object* v_res_1254_; 
v_sz_boxed_1252_ = lean_unbox_usize(v_sz_1249_);
lean_dec(v_sz_1249_);
v_i_boxed_1253_ = lean_unbox_usize(v_i_1250_);
lean_dec(v_i_1250_);
v_res_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(v_sz_boxed_1252_, v_i_boxed_1253_, v_bs_1251_);
return v_res_1254_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(lean_object* v_oldTraces_1255_, lean_object* v_data_1256_, lean_object* v_ref_1257_, lean_object* v_msg_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_toCold_1264_; lean_object* v_currRecDepth_1265_; lean_object* v_ref_1266_; uint16_t v_optionFlags_1267_; uint8_t v_suppressElabErrors_1268_; uint8_t v_isRecordingDeps_1269_; lean_object* v_ref_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_traceState_1273_; lean_object* v_traces_1274_; lean_object* v___x_1275_; size_t v_sz_1276_; size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v_msg_1279_; lean_object* v___x_1280_; lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1319_; 
v_toCold_1264_ = lean_ctor_get(v___y_1261_, 0);
v_currRecDepth_1265_ = lean_ctor_get(v___y_1261_, 1);
v_ref_1266_ = lean_ctor_get(v___y_1261_, 2);
v_optionFlags_1267_ = lean_ctor_get_uint16(v___y_1261_, sizeof(void*)*3);
v_suppressElabErrors_1268_ = lean_ctor_get_uint8(v___y_1261_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1269_ = lean_ctor_get_uint8(v___y_1261_, sizeof(void*)*3 + 3);
v_ref_1270_ = l_Lean_replaceRef(v_ref_1257_, v_ref_1266_);
lean_inc(v_currRecDepth_1265_);
lean_inc_ref(v_toCold_1264_);
v___x_1271_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1271_, 0, v_toCold_1264_);
lean_ctor_set(v___x_1271_, 1, v_currRecDepth_1265_);
lean_ctor_set(v___x_1271_, 2, v_ref_1270_);
lean_ctor_set_uint16(v___x_1271_, sizeof(void*)*3, v_optionFlags_1267_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*3 + 2, v_suppressElabErrors_1268_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*3 + 3, v_isRecordingDeps_1269_);
v___x_1272_ = lean_st_ref_get(v___y_1262_);
v_traceState_1273_ = lean_ctor_get(v___x_1272_, 4);
lean_inc_ref(v_traceState_1273_);
lean_dec(v___x_1272_);
v_traces_1274_ = lean_ctor_get(v_traceState_1273_, 0);
lean_inc_ref(v_traces_1274_);
lean_dec_ref(v_traceState_1273_);
v___x_1275_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1274_);
lean_dec_ref(v_traces_1274_);
v_sz_1276_ = lean_array_size(v___x_1275_);
v___x_1277_ = ((size_t)0ULL);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_spec__9(v_sz_1276_, v___x_1277_, v___x_1275_);
v_msg_1279_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1279_, 0, v_data_1256_);
lean_ctor_set(v_msg_1279_, 1, v_msg_1258_);
lean_ctor_set(v_msg_1279_, 2, v___x_1278_);
v___x_1280_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1279_, v___y_1259_, v___y_1260_, v___x_1271_, v___y_1262_);
lean_dec_ref_known(v___x_1271_, 3);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1319_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1319_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v_traceState_1286_; lean_object* v_env_1287_; lean_object* v_nextMacroScope_1288_; lean_object* v_ngen_1289_; lean_object* v_auxDeclNGen_1290_; lean_object* v_cache_1291_; lean_object* v_recordedDeps_1292_; lean_object* v_messages_1293_; lean_object* v_infoState_1294_; lean_object* v_snapshotTasks_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1318_; 
v___x_1285_ = lean_st_ref_take(v___y_1262_);
v_traceState_1286_ = lean_ctor_get(v___x_1285_, 4);
v_env_1287_ = lean_ctor_get(v___x_1285_, 0);
v_nextMacroScope_1288_ = lean_ctor_get(v___x_1285_, 1);
v_ngen_1289_ = lean_ctor_get(v___x_1285_, 2);
v_auxDeclNGen_1290_ = lean_ctor_get(v___x_1285_, 3);
v_cache_1291_ = lean_ctor_get(v___x_1285_, 5);
v_recordedDeps_1292_ = lean_ctor_get(v___x_1285_, 6);
v_messages_1293_ = lean_ctor_get(v___x_1285_, 7);
v_infoState_1294_ = lean_ctor_get(v___x_1285_, 8);
v_snapshotTasks_1295_ = lean_ctor_get(v___x_1285_, 9);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1297_ = v___x_1285_;
v_isShared_1298_ = v_isSharedCheck_1318_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snapshotTasks_1295_);
lean_inc(v_infoState_1294_);
lean_inc(v_messages_1293_);
lean_inc(v_recordedDeps_1292_);
lean_inc(v_cache_1291_);
lean_inc(v_traceState_1286_);
lean_inc(v_auxDeclNGen_1290_);
lean_inc(v_ngen_1289_);
lean_inc(v_nextMacroScope_1288_);
lean_inc(v_env_1287_);
lean_dec(v___x_1285_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1318_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
uint64_t v_tid_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1316_; 
v_tid_1299_ = lean_ctor_get_uint64(v_traceState_1286_, sizeof(void*)*1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_traceState_1286_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v_traceState_1286_, 0);
lean_dec(v_unused_1317_);
v___x_1301_ = v_traceState_1286_;
v_isShared_1302_ = v_isSharedCheck_1316_;
goto v_resetjp_1300_;
}
else
{
lean_dec(v_traceState_1286_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1316_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_ref_1257_);
lean_ctor_set(v___x_1304_, 1, v_a_1281_);
v___x_1305_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1255_, v___x_1304_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1305_);
v___x_1307_ = v___x_1301_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1305_);
lean_ctor_set_uint64(v_reuseFailAlloc_1315_, sizeof(void*)*1, v_tid_1299_);
v___x_1307_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 4, v___x_1307_);
v___x_1309_ = v___x_1297_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_env_1287_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_nextMacroScope_1288_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_ngen_1289_);
lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_auxDeclNGen_1290_);
lean_ctor_set(v_reuseFailAlloc_1314_, 4, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1314_, 5, v_cache_1291_);
lean_ctor_set(v_reuseFailAlloc_1314_, 6, v_recordedDeps_1292_);
lean_ctor_set(v_reuseFailAlloc_1314_, 7, v_messages_1293_);
lean_ctor_set(v_reuseFailAlloc_1314_, 8, v_infoState_1294_);
lean_ctor_set(v_reuseFailAlloc_1314_, 9, v_snapshotTasks_1295_);
v___x_1309_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_st_ref_put(v___y_1262_, v___x_1309_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1303_);
v___x_1312_ = v___x_1283_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1303_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1255_ = stack[0].m_obj;
lean_object* v_data_1256_ = stack[1].m_obj;
lean_object* v_ref_1257_ = stack[2].m_obj;
lean_object* v_msg_1258_ = stack[3].m_obj;
lean_object* v___y_1259_ = stack[4].m_obj;
lean_object* v___y_1260_ = stack[5].m_obj;
lean_object* v___y_1261_ = stack[6].m_obj;
lean_object* v___y_1262_ = stack[7].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1255_, v_data_1256_, v_ref_1257_, v_msg_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg___boxed(lean_object* v_oldTraces_1321_, lean_object* v_data_1322_, lean_object* v_ref_1323_, lean_object* v_msg_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1321_, v_data_1322_, v_ref_1323_, v_msg_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(lean_object* v_opts_1331_, lean_object* v_opt_1332_){
_start:
{
lean_object* v_name_1333_; lean_object* v_defValue_1334_; lean_object* v_map_1335_; lean_object* v___x_1336_; 
v_name_1333_ = lean_ctor_get(v_opt_1332_, 0);
v_defValue_1334_ = lean_ctor_get(v_opt_1332_, 1);
v_map_1335_ = lean_ctor_get(v_opts_1331_, 0);
v___x_1336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1335_, v_name_1333_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_inc(v_defValue_1334_);
return v_defValue_1334_;
}
else
{
lean_object* v_val_1337_; 
v_val_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v___x_1336_, 1);
if (lean_obj_tag(v_val_1337_) == 3)
{
lean_object* v_v_1338_; 
v_v_1338_ = lean_ctor_get(v_val_1337_, 0);
lean_inc(v_v_1338_);
lean_dec_ref_known(v_val_1337_, 1);
return v_v_1338_;
}
else
{
lean_dec(v_val_1337_);
lean_inc(v_defValue_1334_);
return v_defValue_1334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11___boxed(lean_object* v_opts_1339_, lean_object* v_opt_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1339_, v_opt_1340_);
lean_dec_ref(v_opt_1340_);
lean_dec_ref(v_opts_1339_);
return v_res_1341_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1342_; double v___x_1343_; 
v___x_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_float_of_nat(v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__1));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1347_; double v___x_1348_; 
v___x_1347_ = lean_unsigned_to_nat(1000u);
v___x_1348_ = lean_float_of_nat(v___x_1347_);
return v___x_1348_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(lean_object* v_cls_1349_, uint8_t v_collapsed_1350_, lean_object* v_tag_1351_, lean_object* v_opts_1352_, uint8_t v_clsEnabled_1353_, lean_object* v_oldTraces_1354_, lean_object* v_msg_1355_, lean_object* v_resStartStop_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_fst_1372_; lean_object* v_snd_1373_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v_data_1377_; lean_object* v_fst_1388_; lean_object* v_snd_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; lean_object* v___y_1393_; lean_object* v_a_1394_; uint8_t v___y_1409_; double v___y_1441_; 
v_fst_1372_ = lean_ctor_get(v_resStartStop_1356_, 0);
lean_inc(v_fst_1372_);
v_snd_1373_ = lean_ctor_get(v_resStartStop_1356_, 1);
lean_inc(v_snd_1373_);
lean_dec_ref(v_resStartStop_1356_);
v_fst_1388_ = lean_ctor_get(v_snd_1373_, 0);
lean_inc(v_fst_1388_);
v_snd_1389_ = lean_ctor_get(v_snd_1373_, 1);
lean_inc(v_snd_1389_);
lean_dec(v_snd_1373_);
v___x_1390_ = l_Lean_trace_profiler;
v___x_1391_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1352_, v___x_1390_);
if (v___x_1391_ == 0)
{
v___y_1409_ = v___x_1391_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1447_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1352_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; double v___x_1450_; double v___x_1451_; double v___x_1452_; 
v___x_1448_ = l_Lean_trace_profiler_threshold;
v___x_1449_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1352_, v___x_1448_);
v___x_1450_ = lean_float_of_nat(v___x_1449_);
v___x_1451_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_1452_ = lean_float_div(v___x_1450_, v___x_1451_);
v___y_1441_ = v___x_1452_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; double v___x_1455_; 
v___x_1453_ = l_Lean_trace_profiler_threshold;
v___x_1454_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1352_, v___x_1453_);
v___x_1455_ = lean_float_of_nat(v___x_1454_);
v___y_1441_ = v___x_1455_;
goto v___jp_1440_;
}
}
v___jp_1374_:
{
lean_object* v___x_1378_; 
lean_inc(v___y_1376_);
v___x_1378_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1354_, v_data_1377_, v___y_1376_, v___y_1375_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref_known(v___x_1378_, 1);
v___x_1379_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1372_);
return v___x_1379_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_fst_1372_);
v_a_1380_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1378_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
v___jp_1392_:
{
uint8_t v_result_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; double v___x_1398_; lean_object* v_data_1399_; 
v_result_1395_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__10(v_fst_1372_);
v___x_1396_ = lean_box(v_result_1395_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
v___x_1398_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_1351_);
lean_inc_ref(v___x_1397_);
lean_inc(v_cls_1349_);
v_data_1399_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1399_, 0, v_cls_1349_);
lean_ctor_set(v_data_1399_, 1, v___x_1397_);
lean_ctor_set(v_data_1399_, 2, v_tag_1351_);
lean_ctor_set_float(v_data_1399_, sizeof(void*)*3, v___x_1398_);
lean_ctor_set_float(v_data_1399_, sizeof(void*)*3 + 8, v___x_1398_);
lean_ctor_set_uint8(v_data_1399_, sizeof(void*)*3 + 16, v_collapsed_1350_);
if (v___x_1391_ == 0)
{
lean_dec_ref_known(v___x_1397_, 1);
lean_dec(v_snd_1389_);
lean_dec(v_fst_1388_);
lean_dec_ref(v_tag_1351_);
lean_dec(v_cls_1349_);
v___y_1375_ = v_a_1394_;
v___y_1376_ = v___y_1393_;
v_data_1377_ = v_data_1399_;
goto v___jp_1374_;
}
else
{
lean_object* v_data_1400_; double v___x_1401_; double v___x_1402_; 
lean_dec_ref_known(v_data_1399_, 3);
v_data_1400_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1400_, 0, v_cls_1349_);
lean_ctor_set(v_data_1400_, 1, v___x_1397_);
lean_ctor_set(v_data_1400_, 2, v_tag_1351_);
v___x_1401_ = lean_unbox_float(v_fst_1388_);
lean_dec(v_fst_1388_);
lean_ctor_set_float(v_data_1400_, sizeof(void*)*3, v___x_1401_);
v___x_1402_ = lean_unbox_float(v_snd_1389_);
lean_dec(v_snd_1389_);
lean_ctor_set_float(v_data_1400_, sizeof(void*)*3 + 8, v___x_1402_);
lean_ctor_set_uint8(v_data_1400_, sizeof(void*)*3 + 16, v_collapsed_1350_);
v___y_1375_ = v_a_1394_;
v___y_1376_ = v___y_1393_;
v_data_1377_ = v_data_1400_;
goto v___jp_1374_;
}
}
v___jp_1403_:
{
lean_object* v_ref_1404_; lean_object* v___x_1405_; 
v_ref_1404_ = lean_ctor_get(v___y_1369_, 2);
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v_fst_1372_);
v___x_1405_ = lean_apply_16(v_msg_1355_, v_fst_1372_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, lean_box(0));
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___y_1393_ = v_ref_1404_;
v_a_1394_ = v_a_1406_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1407_; 
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_1393_ = v_ref_1404_;
v_a_1394_ = v___x_1407_;
goto v___jp_1392_;
}
}
v___jp_1408_:
{
if (v_clsEnabled_1353_ == 0)
{
if (v___y_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v_traceState_1411_; lean_object* v_env_1412_; lean_object* v_nextMacroScope_1413_; lean_object* v_ngen_1414_; lean_object* v_auxDeclNGen_1415_; lean_object* v_cache_1416_; lean_object* v_recordedDeps_1417_; lean_object* v_messages_1418_; lean_object* v_infoState_1419_; lean_object* v_snapshotTasks_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_snd_1389_);
lean_dec(v_fst_1388_);
lean_dec_ref(v_msg_1355_);
lean_dec_ref(v_tag_1351_);
lean_dec(v_cls_1349_);
v___x_1410_ = lean_st_ref_take(v___y_1370_);
v_traceState_1411_ = lean_ctor_get(v___x_1410_, 4);
v_env_1412_ = lean_ctor_get(v___x_1410_, 0);
v_nextMacroScope_1413_ = lean_ctor_get(v___x_1410_, 1);
v_ngen_1414_ = lean_ctor_get(v___x_1410_, 2);
v_auxDeclNGen_1415_ = lean_ctor_get(v___x_1410_, 3);
v_cache_1416_ = lean_ctor_get(v___x_1410_, 5);
v_recordedDeps_1417_ = lean_ctor_get(v___x_1410_, 6);
v_messages_1418_ = lean_ctor_get(v___x_1410_, 7);
v_infoState_1419_ = lean_ctor_get(v___x_1410_, 8);
v_snapshotTasks_1420_ = lean_ctor_get(v___x_1410_, 9);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1422_ = v___x_1410_;
v_isShared_1423_ = v_isSharedCheck_1439_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_snapshotTasks_1420_);
lean_inc(v_infoState_1419_);
lean_inc(v_messages_1418_);
lean_inc(v_recordedDeps_1417_);
lean_inc(v_cache_1416_);
lean_inc(v_traceState_1411_);
lean_inc(v_auxDeclNGen_1415_);
lean_inc(v_ngen_1414_);
lean_inc(v_nextMacroScope_1413_);
lean_inc(v_env_1412_);
lean_dec(v___x_1410_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1439_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
uint64_t v_tid_1424_; lean_object* v_traces_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1438_; 
v_tid_1424_ = lean_ctor_get_uint64(v_traceState_1411_, sizeof(void*)*1);
v_traces_1425_ = lean_ctor_get(v_traceState_1411_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_traceState_1411_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1427_ = v_traceState_1411_;
v_isShared_1428_ = v_isSharedCheck_1438_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_traces_1425_);
lean_dec(v_traceState_1411_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1438_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1354_, v_traces_1425_);
lean_dec_ref(v_traces_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1429_);
lean_ctor_set_uint64(v_reuseFailAlloc_1437_, sizeof(void*)*1, v_tid_1424_);
v___x_1431_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 4, v___x_1431_);
v___x_1433_ = v___x_1422_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_env_1412_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_nextMacroScope_1413_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_ngen_1414_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_auxDeclNGen_1415_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1436_, 5, v_cache_1416_);
lean_ctor_set(v_reuseFailAlloc_1436_, 6, v_recordedDeps_1417_);
lean_ctor_set(v_reuseFailAlloc_1436_, 7, v_messages_1418_);
lean_ctor_set(v_reuseFailAlloc_1436_, 8, v_infoState_1419_);
lean_ctor_set(v_reuseFailAlloc_1436_, 9, v_snapshotTasks_1420_);
v___x_1433_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_st_ref_put(v___y_1370_, v___x_1433_);
v___x_1435_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1372_);
return v___x_1435_;
}
}
}
}
}
else
{
goto v___jp_1403_;
}
}
else
{
goto v___jp_1403_;
}
}
v___jp_1440_:
{
double v___x_1442_; double v___x_1443_; double v___x_1444_; uint8_t v___x_1445_; 
v___x_1442_ = lean_unbox_float(v_snd_1389_);
v___x_1443_ = lean_unbox_float(v_fst_1388_);
v___x_1444_ = lean_float_sub(v___x_1442_, v___x_1443_);
v___x_1445_ = lean_float_decLt(v___y_1441_, v___x_1444_);
v___y_1409_ = v___x_1445_;
goto v___jp_1408_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1349_ = stack[0].m_obj;
uint8_t v_collapsed_1350_ = stack[1].m_num;
lean_object* v_tag_1351_ = stack[2].m_obj;
lean_object* v_opts_1352_ = stack[3].m_obj;
uint8_t v_clsEnabled_1353_ = stack[4].m_num;
lean_object* v_oldTraces_1354_ = stack[5].m_obj;
lean_object* v_msg_1355_ = stack[6].m_obj;
lean_object* v_resStartStop_1356_ = stack[7].m_obj;
lean_object* v___y_1357_ = stack[8].m_obj;
lean_object* v___y_1358_ = stack[9].m_obj;
lean_object* v___y_1359_ = stack[10].m_obj;
lean_object* v___y_1360_ = stack[11].m_obj;
lean_object* v___y_1361_ = stack[12].m_obj;
lean_object* v___y_1362_ = stack[13].m_obj;
lean_object* v___y_1363_ = stack[14].m_obj;
lean_object* v___y_1364_ = stack[15].m_obj;
lean_object* v___y_1365_ = stack[16].m_obj;
lean_object* v___y_1366_ = stack[17].m_obj;
lean_object* v___y_1367_ = stack[18].m_obj;
lean_object* v___y_1368_ = stack[19].m_obj;
lean_object* v___y_1369_ = stack[20].m_obj;
lean_object* v___y_1370_ = stack[21].m_obj;
lean_object* v_res_1456_;
v_res_1456_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v_cls_1349_, v_collapsed_1350_, v_tag_1351_, v_opts_1352_, v_clsEnabled_1353_, v_oldTraces_1354_, v_msg_1355_, v_resStartStop_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
stack->m_obj
 = v_res_1456_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___boxed(lean_object** _args){
lean_object* v_cls_1457_ = _args[0];
lean_object* v_collapsed_1458_ = _args[1];
lean_object* v_tag_1459_ = _args[2];
lean_object* v_opts_1460_ = _args[3];
lean_object* v_clsEnabled_1461_ = _args[4];
lean_object* v_oldTraces_1462_ = _args[5];
lean_object* v_msg_1463_ = _args[6];
lean_object* v_resStartStop_1464_ = _args[7];
lean_object* v___y_1465_ = _args[8];
lean_object* v___y_1466_ = _args[9];
lean_object* v___y_1467_ = _args[10];
lean_object* v___y_1468_ = _args[11];
lean_object* v___y_1469_ = _args[12];
lean_object* v___y_1470_ = _args[13];
lean_object* v___y_1471_ = _args[14];
lean_object* v___y_1472_ = _args[15];
lean_object* v___y_1473_ = _args[16];
lean_object* v___y_1474_ = _args[17];
lean_object* v___y_1475_ = _args[18];
lean_object* v___y_1476_ = _args[19];
lean_object* v___y_1477_ = _args[20];
lean_object* v___y_1478_ = _args[21];
lean_object* v___y_1479_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_1480_; uint8_t v_clsEnabled_boxed_1481_; lean_object* v_res_1482_; 
v_collapsed_boxed_1480_ = lean_unbox(v_collapsed_1458_);
v_clsEnabled_boxed_1481_ = lean_unbox(v_clsEnabled_1461_);
v_res_1482_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v_cls_1457_, v_collapsed_boxed_1480_, v_tag_1459_, v_opts_1460_, v_clsEnabled_boxed_1481_, v_oldTraces_1462_, v_msg_1463_, v_resStartStop_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec_ref(v_opts_1460_);
return v_res_1482_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(lean_object* v_a_1483_, lean_object* v_x_1484_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = 0;
return v___x_1485_;
}
else
{
lean_object* v_key_1486_; lean_object* v_tail_1487_; uint8_t v___x_1488_; 
v_key_1486_ = lean_ctor_get(v_x_1484_, 0);
v_tail_1487_ = lean_ctor_get(v_x_1484_, 2);
v___x_1488_ = lean_nat_dec_eq(v_key_1486_, v_a_1483_);
if (v___x_1488_ == 0)
{
v_x_1484_ = v_tail_1487_;
goto _start;
}
else
{
return v___x_1488_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1483_ = stack[0].m_obj;
lean_object* v_x_1484_ = stack[1].m_obj;
uint8_t v_res_1490_;
v_res_1490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1483_, v_x_1484_);
stack->m_num = v_res_1490_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg___boxed(lean_object* v_a_1491_, lean_object* v_x_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1491_, v_x_1492_);
lean_dec(v_x_1492_);
lean_dec(v_a_1491_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(lean_object* v___x_1495_, lean_object* v_m_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_buckets_1498_; lean_object* v___x_1499_; uint64_t v___x_1500_; uint64_t v___x_1501_; uint64_t v___x_1502_; uint64_t v_fold_1503_; uint64_t v___x_1504_; uint64_t v___x_1505_; uint64_t v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v_buckets_1498_ = lean_ctor_get(v_m_1496_, 1);
v___x_1499_ = lean_array_get_size(v_buckets_1498_);
v___x_1500_ = lean_uint64_of_nat(v_a_1497_);
v___x_1501_ = 32ULL;
v___x_1502_ = lean_uint64_shift_right(v___x_1500_, v___x_1501_);
v_fold_1503_ = lean_uint64_xor(v___x_1500_, v___x_1502_);
v___x_1504_ = 16ULL;
v___x_1505_ = lean_uint64_shift_right(v_fold_1503_, v___x_1504_);
v___x_1506_ = lean_uint64_xor(v_fold_1503_, v___x_1505_);
v___x_1507_ = lean_uint64_to_usize(v___x_1506_);
v___x_1508_ = lean_usize_of_nat(v___x_1499_);
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = lean_usize_sub(v___x_1508_, v___x_1509_);
v___x_1511_ = lean_usize_land(v___x_1507_, v___x_1510_);
v___x_1512_ = lean_array_uget_borrowed(v_buckets_1498_, v___x_1511_);
v___x_1513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1497_, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1495_ = stack[0].m_obj;
lean_object* v_m_1496_ = stack[1].m_obj;
lean_object* v_a_1497_ = stack[2].m_obj;
uint8_t v_res_1514_;
v_res_1514_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_1495_, v_m_1496_, v_a_1497_);
stack->m_num = v_res_1514_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg___boxed(lean_object* v___x_1515_, lean_object* v_m_1516_, lean_object* v_a_1517_){
_start:
{
uint8_t v_res_1518_; lean_object* v_r_1519_; 
v_res_1518_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_1515_, v_m_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_m_1516_);
lean_dec(v___x_1515_);
v_r_1519_ = lean_box(v_res_1518_);
return v_r_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
return v_x_1520_;
}
else
{
lean_object* v_key_1522_; lean_object* v_value_1523_; lean_object* v_tail_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1547_; 
v_key_1522_ = lean_ctor_get(v_x_1521_, 0);
v_value_1523_ = lean_ctor_get(v_x_1521_, 1);
v_tail_1524_ = lean_ctor_get(v_x_1521_, 2);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1526_ = v_x_1521_;
v_isShared_1527_ = v_isSharedCheck_1547_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_tail_1524_);
lean_inc(v_value_1523_);
lean_inc(v_key_1522_);
lean_dec(v_x_1521_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1547_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; uint64_t v___x_1529_; uint64_t v___x_1530_; uint64_t v___x_1531_; uint64_t v_fold_1532_; uint64_t v___x_1533_; uint64_t v___x_1534_; uint64_t v___x_1535_; size_t v___x_1536_; size_t v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1528_ = lean_array_get_size(v_x_1520_);
v___x_1529_ = lean_uint64_of_nat(v_key_1522_);
v___x_1530_ = 32ULL;
v___x_1531_ = lean_uint64_shift_right(v___x_1529_, v___x_1530_);
v_fold_1532_ = lean_uint64_xor(v___x_1529_, v___x_1531_);
v___x_1533_ = 16ULL;
v___x_1534_ = lean_uint64_shift_right(v_fold_1532_, v___x_1533_);
v___x_1535_ = lean_uint64_xor(v_fold_1532_, v___x_1534_);
v___x_1536_ = lean_uint64_to_usize(v___x_1535_);
v___x_1537_ = lean_usize_of_nat(v___x_1528_);
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_sub(v___x_1537_, v___x_1538_);
v___x_1540_ = lean_usize_land(v___x_1536_, v___x_1539_);
v___x_1541_ = lean_array_uget_borrowed(v_x_1520_, v___x_1540_);
lean_inc(v___x_1541_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 2, v___x_1541_);
v___x_1543_ = v___x_1526_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_key_1522_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_value_1523_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_array_uset(v_x_1520_, v___x_1540_, v___x_1543_);
v_x_1520_ = v___x_1544_;
v_x_1521_ = v_tail_1524_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(lean_object* v_i_1548_, lean_object* v_source_1549_, lean_object* v_target_1550_){
_start:
{
lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = lean_array_get_size(v_source_1549_);
v___x_1552_ = lean_nat_dec_lt(v_i_1548_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_dec_ref(v_source_1549_);
lean_dec(v_i_1548_);
return v_target_1550_;
}
else
{
lean_object* v_es_1553_; lean_object* v___x_1554_; lean_object* v_source_1555_; lean_object* v_target_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_es_1553_ = lean_array_fget(v_source_1549_, v_i_1548_);
v___x_1554_ = lean_box(0);
v_source_1555_ = lean_array_fset(v_source_1549_, v_i_1548_, v___x_1554_);
v_target_1556_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(v_target_1550_, v_es_1553_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_add(v_i_1548_, v___x_1557_);
lean_dec(v_i_1548_);
v_i_1548_ = v___x_1558_;
v_source_1549_ = v_source_1555_;
v_target_1550_ = v_target_1556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(lean_object* v___x_1560_, lean_object* v_data_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_nbuckets_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1562_ = lean_array_get_size(v_data_1561_);
v___x_1563_ = lean_unsigned_to_nat(2u);
v_nbuckets_1564_ = lean_nat_mul(v___x_1562_, v___x_1563_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_mk_array(v_nbuckets_1564_, v___x_1566_);
v___x_1568_ = lean_array_propagate_mark(v_data_1561_, v___x_1567_);
v___x_1569_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(v___x_1565_, v_data_1561_, v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg___boxed(lean_object* v___x_1570_, lean_object* v_data_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_1570_, v_data_1571_);
lean_dec(v___x_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(lean_object* v___x_1573_, lean_object* v_m_1574_, lean_object* v_a_1575_, lean_object* v_b_1576_){
_start:
{
lean_object* v_size_1577_; lean_object* v_buckets_1578_; lean_object* v___x_1579_; uint64_t v___x_1580_; uint64_t v___x_1581_; uint64_t v___x_1582_; uint64_t v_fold_1583_; uint64_t v___x_1584_; uint64_t v___x_1585_; uint64_t v___x_1586_; size_t v___x_1587_; size_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; lean_object* v_bkt_1592_; uint8_t v___x_1593_; 
v_size_1577_ = lean_ctor_get(v_m_1574_, 0);
v_buckets_1578_ = lean_ctor_get(v_m_1574_, 1);
v___x_1579_ = lean_array_get_size(v_buckets_1578_);
v___x_1580_ = lean_uint64_of_nat(v_a_1575_);
v___x_1581_ = 32ULL;
v___x_1582_ = lean_uint64_shift_right(v___x_1580_, v___x_1581_);
v_fold_1583_ = lean_uint64_xor(v___x_1580_, v___x_1582_);
v___x_1584_ = 16ULL;
v___x_1585_ = lean_uint64_shift_right(v_fold_1583_, v___x_1584_);
v___x_1586_ = lean_uint64_xor(v_fold_1583_, v___x_1585_);
v___x_1587_ = lean_uint64_to_usize(v___x_1586_);
v___x_1588_ = lean_usize_of_nat(v___x_1579_);
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_sub(v___x_1588_, v___x_1589_);
v___x_1591_ = lean_usize_land(v___x_1587_, v___x_1590_);
v_bkt_1592_ = lean_array_uget_borrowed(v_buckets_1578_, v___x_1591_);
v___x_1593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_1575_, v_bkt_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1614_; 
lean_inc_ref(v_buckets_1578_);
lean_inc(v_size_1577_);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_m_1574_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; lean_object* v_unused_1616_; 
v_unused_1615_ = lean_ctor_get(v_m_1574_, 1);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_m_1574_, 0);
lean_dec(v_unused_1616_);
v___x_1595_ = v_m_1574_;
v_isShared_1596_ = v_isSharedCheck_1614_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_m_1574_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1614_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v_size_x27_1598_; lean_object* v___x_1599_; lean_object* v_buckets_x27_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1597_ = lean_unsigned_to_nat(1u);
v_size_x27_1598_ = lean_nat_add(v_size_1577_, v___x_1597_);
lean_dec(v_size_1577_);
lean_inc(v_bkt_1592_);
v___x_1599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1599_, 0, v_a_1575_);
lean_ctor_set(v___x_1599_, 1, v_b_1576_);
lean_ctor_set(v___x_1599_, 2, v_bkt_1592_);
v_buckets_x27_1600_ = lean_array_uset(v_buckets_1578_, v___x_1591_, v___x_1599_);
v___x_1601_ = lean_unsigned_to_nat(4u);
v___x_1602_ = lean_nat_mul(v_size_x27_1598_, v___x_1601_);
v___x_1603_ = lean_unsigned_to_nat(3u);
v___x_1604_ = lean_nat_div(v___x_1602_, v___x_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_array_get_size(v_buckets_x27_1600_);
v___x_1606_ = lean_nat_dec_le(v___x_1604_, v___x_1605_);
lean_dec(v___x_1604_);
if (v___x_1606_ == 0)
{
lean_object* v_val_1607_; lean_object* v___x_1609_; 
v_val_1607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_1573_, v_buckets_x27_1600_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 1, v_val_1607_);
lean_ctor_set(v___x_1595_, 0, v_size_x27_1598_);
v___x_1609_ = v___x_1595_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_size_x27_1598_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_val_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
else
{
lean_object* v___x_1612_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 1, v_buckets_x27_1600_);
lean_ctor_set(v___x_1595_, 0, v_size_x27_1598_);
v___x_1612_ = v___x_1595_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_size_x27_1598_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_buckets_x27_1600_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_dec(v_b_1576_);
lean_dec(v_a_1575_);
return v_m_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg___boxed(lean_object* v___x_1617_, lean_object* v_m_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_1617_, v_m_1618_, v_a_1619_, v_b_1620_);
lean_dec(v___x_1617_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(lean_object* v_acc_1625_, lean_object* v_decls_1626_, lean_object* v_idx_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = lean_array_get_size(v_decls_1626_);
v___x_1630_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_1629_, v_a_1628_, v_idx_1627_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = lean_box(0);
lean_inc(v_idx_1627_);
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_1629_, v_a_1628_, v_idx_1627_, v___x_1631_);
v___x_1633_ = lean_array_fget_borrowed(v_decls_1626_, v_idx_1627_);
if (lean_obj_tag(v___x_1633_) == 2)
{
lean_object* v_l_1634_; lean_object* v_r_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___y_1639_; lean_object* v___y_1640_; uint8_t v___y_1641_; uint8_t v___y_1665_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_l_1634_ = lean_ctor_get(v___x_1633_, 0);
v_r_1635_ = lean_ctor_get(v___x_1633_, 1);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_shiftr(v_l_1634_, v___x_1636_);
v___x_1671_ = lean_nat_land(v___x_1636_, v_l_1634_);
v___x_1672_ = lean_unsigned_to_nat(0u);
v___x_1673_ = lean_nat_dec_eq(v___x_1671_, v___x_1672_);
lean_dec(v___x_1671_);
if (v___x_1673_ == 0)
{
uint8_t v___x_1674_; 
v___x_1674_ = 1;
v___y_1665_ = v___x_1674_;
goto v___jp_1664_;
}
else
{
v___y_1665_ = v___x_1630_;
goto v___jp_1664_;
}
v___jp_1638_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; 
v___x_1642_ = l_Nat_reprFast(v_idx_1627_);
v___x_1643_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__0));
lean_inc_ref(v___x_1642_);
v___x_1644_ = lean_string_append(v___x_1642_, v___x_1643_);
lean_inc(v___x_1637_);
v___x_1645_ = l_Nat_reprFast(v___x_1637_);
v___x_1646_ = lean_string_append(v___x_1644_, v___x_1645_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1639_);
v___x_1648_ = lean_string_append(v___x_1646_, v___x_1647_);
lean_dec_ref(v___x_1647_);
v___x_1649_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__1));
v___x_1650_ = lean_string_append(v___x_1648_, v___x_1649_);
v___x_1651_ = lean_string_append(v___x_1650_, v___x_1642_);
lean_dec_ref(v___x_1642_);
v___x_1652_ = lean_string_append(v___x_1651_, v___x_1643_);
lean_inc(v___y_1640_);
v___x_1653_ = l_Nat_reprFast(v___y_1640_);
v___x_1654_ = lean_string_append(v___x_1652_, v___x_1653_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_1641_);
v___x_1656_ = lean_string_append(v___x_1654_, v___x_1655_);
lean_dec_ref(v___x_1655_);
v___x_1657_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___closed__2));
v___x_1658_ = lean_string_append(v___x_1656_, v___x_1657_);
v___x_1659_ = lean_string_append(v_acc_1625_, v___x_1658_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v___x_1659_, v_decls_1626_, v___x_1637_, v___x_1632_);
v_fst_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_fst_1661_);
v_snd_1662_ = lean_ctor_get(v___x_1660_, 1);
lean_inc(v_snd_1662_);
lean_dec_ref(v___x_1660_);
v_acc_1625_ = v_fst_1661_;
v_idx_1627_ = v___y_1640_;
v_a_1628_ = v_snd_1662_;
goto _start;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1666_ = lean_nat_shiftr(v_r_1635_, v___x_1636_);
v___x_1667_ = lean_nat_land(v___x_1636_, v_r_1635_);
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = lean_nat_dec_eq(v___x_1667_, v___x_1668_);
lean_dec(v___x_1667_);
if (v___x_1669_ == 0)
{
uint8_t v___x_1670_; 
v___x_1670_ = 1;
v___y_1639_ = v___y_1665_;
v___y_1640_ = v___x_1666_;
v___y_1641_ = v___x_1670_;
goto v___jp_1638_;
}
else
{
v___y_1639_ = v___y_1665_;
v___y_1640_ = v___x_1666_;
v___y_1641_ = v___x_1630_;
goto v___jp_1638_;
}
}
}
else
{
lean_object* v___x_1675_; 
lean_dec(v_idx_1627_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_acc_1625_);
lean_ctor_set(v___x_1675_, 1, v___x_1632_);
return v___x_1675_;
}
}
else
{
lean_object* v___x_1676_; 
lean_dec(v_idx_1627_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_acc_1625_);
lean_ctor_set(v___x_1676_, 1, v_a_1628_);
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg___boxed(lean_object* v_acc_1677_, lean_object* v_decls_1678_, lean_object* v_idx_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v_acc_1677_, v_decls_1678_, v_idx_1679_, v_a_1680_);
lean_dec_ref(v_decls_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(lean_object* v_decls_1690_, lean_object* v_idx_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_array_fget_borrowed(v_decls_1690_, v_idx_1691_);
switch(lean_obj_tag(v___x_1692_))
{
case 0:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1693_ = l_Nat_reprFast(v_idx_1691_);
v___x_1694_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
v___x_1695_ = lean_string_append(v___x_1693_, v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__1));
v___x_1697_ = lean_string_append(v___x_1695_, v___x_1696_);
v___x_1698_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__2));
v___x_1699_ = lean_string_append(v___x_1697_, v___x_1698_);
return v___x_1699_;
}
case 1:
{
lean_object* v_idx_1700_; lean_object* v_var_1701_; lean_object* v_idx_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_idx_1700_ = lean_ctor_get(v___x_1692_, 0);
v_var_1701_ = lean_ctor_get(v_idx_1700_, 0);
v_idx_1702_ = lean_ctor_get(v_idx_1700_, 2);
v___x_1703_ = l_Nat_reprFast(v_idx_1691_);
v___x_1704_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
v___x_1705_ = lean_string_append(v___x_1703_, v___x_1704_);
v___x_1706_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__3));
lean_inc(v_var_1701_);
v___x_1707_ = l_Nat_reprFast(v_var_1701_);
v___x_1708_ = lean_string_append(v___x_1706_, v___x_1707_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__4));
v___x_1710_ = lean_string_append(v___x_1708_, v___x_1709_);
lean_inc(v_idx_1702_);
v___x_1711_ = l_Nat_reprFast(v_idx_1702_);
v___x_1712_ = lean_string_append(v___x_1710_, v___x_1711_);
lean_dec_ref(v___x_1711_);
v___x_1713_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__5));
v___x_1714_ = lean_string_append(v___x_1712_, v___x_1713_);
v___x_1715_ = lean_string_append(v___x_1705_, v___x_1714_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__6));
v___x_1717_ = lean_string_append(v___x_1715_, v___x_1716_);
return v___x_1717_;
}
default: 
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1718_ = l_Nat_reprFast(v_idx_1691_);
v___x_1719_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__0));
lean_inc_ref(v___x_1718_);
v___x_1720_ = lean_string_append(v___x_1718_, v___x_1719_);
v___x_1721_ = lean_string_append(v___x_1720_, v___x_1718_);
lean_dec_ref(v___x_1718_);
v___x_1722_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___closed__7));
v___x_1723_ = lean_string_append(v___x_1721_, v___x_1722_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15___boxed(lean_object* v_decls_1724_, lean_object* v_idx_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(v_decls_1724_, v_idx_1725_);
lean_dec_ref(v_decls_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(lean_object* v_decls_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
return v_x_1728_;
}
else
{
lean_object* v_key_1730_; lean_object* v_tail_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_key_1730_ = lean_ctor_get(v_x_1729_, 0);
lean_inc(v_key_1730_);
v_tail_1731_ = lean_ctor_get(v_x_1729_, 2);
lean_inc(v_tail_1731_);
lean_dec_ref_known(v_x_1729_, 3);
v___x_1732_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__15(v_decls_1727_, v_key_1730_);
v___x_1733_ = lean_string_append(v_x_1728_, v___x_1732_);
lean_dec_ref(v___x_1732_);
v_x_1728_ = v___x_1733_;
v_x_1729_ = v_tail_1731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17___boxed(lean_object* v_decls_1735_, lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(v_decls_1735_, v_x_1736_, v_x_1737_);
lean_dec_ref(v_decls_1735_);
return v_res_1738_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(lean_object* v_decls_1739_, lean_object* v_as_1740_, size_t v_i_1741_, size_t v_stop_1742_, lean_object* v_b_1743_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_eq(v_i_1741_, v_stop_1742_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; 
v___x_1745_ = lean_array_uget_borrowed(v_as_1740_, v_i_1741_);
lean_inc(v___x_1745_);
v___x_1746_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__17(v_decls_1739_, v_b_1743_, v___x_1745_);
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1741_, v___x_1747_);
v_i_1741_ = v___x_1748_;
v_b_1743_ = v___x_1746_;
goto _start;
}
else
{
return v_b_1743_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_1739_ = stack[0].m_obj;
lean_object* v_as_1740_ = stack[1].m_obj;
size_t v_i_1741_ = stack[2].m_num;
size_t v_stop_1742_ = stack[3].m_num;
lean_object* v_b_1743_ = stack[4].m_obj;
lean_object* v_res_1750_;
v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(v_decls_1739_, v_as_1740_, v_i_1741_, v_stop_1742_, v_b_1743_);
stack->m_obj
 = v_res_1750_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18___boxed(lean_object* v_decls_1751_, lean_object* v_as_1752_, lean_object* v_i_1753_, lean_object* v_stop_1754_, lean_object* v_b_1755_){
_start:
{
size_t v_i_boxed_1756_; size_t v_stop_boxed_1757_; lean_object* v_res_1758_; 
v_i_boxed_1756_ = lean_unbox_usize(v_i_1753_);
lean_dec(v_i_1753_);
v_stop_boxed_1757_ = lean_unbox_usize(v_stop_1754_);
lean_dec(v_stop_1754_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(v_decls_1751_, v_as_1752_, v_i_boxed_1756_, v_stop_boxed_1757_, v_b_1755_);
lean_dec_ref(v_as_1752_);
lean_dec_ref(v_decls_1751_);
return v_res_1758_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_unsigned_to_nat(16u);
v___x_1762_ = lean_mk_array(v___x_1761_, v___x_1760_);
return v___x_1762_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__1);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v___x_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(lean_object* v_entry_1768_){
_start:
{
lean_object* v_aig_1769_; lean_object* v_ref_1770_; lean_object* v_decls_1771_; lean_object* v_gate_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v_fst_1777_; lean_object* v_snd_1778_; lean_object* v___y_1780_; lean_object* v_buckets_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_aig_1769_ = lean_ctor_get(v_entry_1768_, 0);
lean_inc_ref(v_aig_1769_);
v_ref_1770_ = lean_ctor_get(v_entry_1768_, 1);
lean_inc_ref(v_ref_1770_);
lean_dec_ref(v_entry_1768_);
v_decls_1771_ = lean_ctor_get(v_aig_1769_, 0);
lean_inc_ref(v_decls_1771_);
lean_dec_ref(v_aig_1769_);
v_gate_1772_ = lean_ctor_get(v_ref_1770_, 0);
lean_inc(v_gate_1772_);
lean_dec_ref(v_ref_1770_);
v___x_1773_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__2);
v___x_1776_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v___x_1773_, v_decls_1771_, v_gate_1772_, v___x_1775_);
v_fst_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_fst_1777_);
v_snd_1778_ = lean_ctor_get(v___x_1776_, 1);
lean_inc(v_snd_1778_);
lean_dec_ref(v___x_1776_);
v_buckets_1786_ = lean_ctor_get(v_snd_1778_, 1);
lean_inc_ref(v_buckets_1786_);
lean_dec(v_snd_1778_);
v___x_1787_ = lean_array_get_size(v_buckets_1786_);
v___x_1788_ = lean_nat_dec_lt(v___x_1774_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_dec_ref(v_buckets_1786_);
lean_dec_ref(v_decls_1771_);
v___y_1780_ = v___x_1773_;
goto v___jp_1779_;
}
else
{
size_t v___x_1789_; size_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((size_t)0ULL);
v___x_1790_ = lean_usize_of_nat(v___x_1787_);
v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__18(v_decls_1771_, v_buckets_1786_, v___x_1789_, v___x_1790_, v___x_1773_);
lean_dec_ref(v_buckets_1786_);
lean_dec_ref(v_decls_1771_);
v___y_1780_ = v___x_1791_;
goto v___jp_1779_;
}
v___jp_1779_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1781_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__3));
v___x_1782_ = lean_string_append(v___x_1781_, v___y_1780_);
lean_dec_ref(v___y_1780_);
v___x_1783_ = lean_string_append(v___x_1782_, v_fst_1777_);
lean_dec(v_fst_1777_);
v___x_1784_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__4));
v___x_1785_ = lean_string_append(v___x_1783_, v___x_1784_);
return v___x_1785_;
}
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(lean_object* v_cls_1794_, lean_object* v_msg_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_ref_1801_; lean_object* v___x_1802_; lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1848_; 
v_ref_1801_ = lean_ctor_get(v___y_1798_, 2);
v___x_1802_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1848_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1848_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v_traceState_1808_; lean_object* v_env_1809_; lean_object* v_nextMacroScope_1810_; lean_object* v_ngen_1811_; lean_object* v_auxDeclNGen_1812_; lean_object* v_cache_1813_; lean_object* v_recordedDeps_1814_; lean_object* v_messages_1815_; lean_object* v_infoState_1816_; lean_object* v_snapshotTasks_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1847_; 
v___x_1807_ = lean_st_ref_take(v___y_1799_);
v_traceState_1808_ = lean_ctor_get(v___x_1807_, 4);
v_env_1809_ = lean_ctor_get(v___x_1807_, 0);
v_nextMacroScope_1810_ = lean_ctor_get(v___x_1807_, 1);
v_ngen_1811_ = lean_ctor_get(v___x_1807_, 2);
v_auxDeclNGen_1812_ = lean_ctor_get(v___x_1807_, 3);
v_cache_1813_ = lean_ctor_get(v___x_1807_, 5);
v_recordedDeps_1814_ = lean_ctor_get(v___x_1807_, 6);
v_messages_1815_ = lean_ctor_get(v___x_1807_, 7);
v_infoState_1816_ = lean_ctor_get(v___x_1807_, 8);
v_snapshotTasks_1817_ = lean_ctor_get(v___x_1807_, 9);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1819_ = v___x_1807_;
v_isShared_1820_ = v_isSharedCheck_1847_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snapshotTasks_1817_);
lean_inc(v_infoState_1816_);
lean_inc(v_messages_1815_);
lean_inc(v_recordedDeps_1814_);
lean_inc(v_cache_1813_);
lean_inc(v_traceState_1808_);
lean_inc(v_auxDeclNGen_1812_);
lean_inc(v_ngen_1811_);
lean_inc(v_nextMacroScope_1810_);
lean_inc(v_env_1809_);
lean_dec(v___x_1807_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1847_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
uint64_t v_tid_1821_; lean_object* v_traces_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1846_; 
v_tid_1821_ = lean_ctor_get_uint64(v_traceState_1808_, sizeof(void*)*1);
v_traces_1822_ = lean_ctor_get(v_traceState_1808_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_traceState_1808_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1824_ = v_traceState_1808_;
v_isShared_1825_ = v_isSharedCheck_1846_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_traces_1822_);
lean_dec(v_traceState_1808_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1846_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; double v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1826_ = lean_box(0);
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
v___x_1829_ = 0;
v___x_1830_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_1831_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1831_, 0, v_cls_1794_);
lean_ctor_set(v___x_1831_, 1, v___x_1827_);
lean_ctor_set(v___x_1831_, 2, v___x_1830_);
lean_ctor_set_float(v___x_1831_, sizeof(void*)*3, v___x_1828_);
lean_ctor_set_float(v___x_1831_, sizeof(void*)*3 + 8, v___x_1828_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 16, v___x_1829_);
v___x_1832_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___closed__0));
v___x_1833_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v_a_1803_);
lean_ctor_set(v___x_1833_, 2, v___x_1832_);
lean_inc(v_ref_1801_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_ref_1801_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_PersistentArray_push___redArg(v_traces_1822_, v___x_1834_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1835_);
v___x_1837_ = v___x_1824_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1835_);
lean_ctor_set_uint64(v_reuseFailAlloc_1845_, sizeof(void*)*1, v_tid_1821_);
v___x_1837_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v___x_1837_);
v___x_1839_ = v___x_1819_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_env_1809_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_nextMacroScope_1810_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_ngen_1811_);
lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_auxDeclNGen_1812_);
lean_ctor_set(v_reuseFailAlloc_1844_, 4, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1844_, 5, v_cache_1813_);
lean_ctor_set(v_reuseFailAlloc_1844_, 6, v_recordedDeps_1814_);
lean_ctor_set(v_reuseFailAlloc_1844_, 7, v_messages_1815_);
lean_ctor_set(v_reuseFailAlloc_1844_, 8, v_infoState_1816_);
lean_ctor_set(v_reuseFailAlloc_1844_, 9, v_snapshotTasks_1817_);
v___x_1839_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_st_ref_put(v___y_1799_, v___x_1839_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1826_);
v___x_1842_ = v___x_1805_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1826_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1794_ = stack[0].m_obj;
lean_object* v_msg_1795_ = stack[1].m_obj;
lean_object* v___y_1796_ = stack[2].m_obj;
lean_object* v___y_1797_ = stack[3].m_obj;
lean_object* v___y_1798_ = stack[4].m_obj;
lean_object* v___y_1799_ = stack[5].m_obj;
lean_object* v_res_1849_;
v_res_1849_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_1794_, v_msg_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
stack->m_obj
 = v_res_1849_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg___boxed(lean_object* v_cls_1850_, lean_object* v_msg_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_1850_, v_msg_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1857_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(lean_object* v_msg_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_ref_1864_; lean_object* v___x_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1874_; 
v_ref_1864_ = lean_ctor_get(v___y_1861_, 2);
v___x_1865_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_spec__3(v_msg_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1874_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_inc(v_ref_1864_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_ref_1864_);
lean_ctor_set(v___x_1870_, 1, v_a_1866_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 1);
lean_ctor_set(v___x_1868_, 0, v___x_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1858_ = stack[0].m_obj;
lean_object* v___y_1859_ = stack[1].m_obj;
lean_object* v___y_1860_ = stack[2].m_obj;
lean_object* v___y_1861_ = stack[3].m_obj;
lean_object* v___y_1862_ = stack[4].m_obj;
lean_object* v_res_1875_;
v_res_1875_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v_msg_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
stack->m_obj
 = v_res_1875_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg___boxed(lean_object* v_msg_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v_msg_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1882_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(lean_object* v_e_1883_){
_start:
{
if (lean_obj_tag(v_e_1883_) == 0)
{
uint8_t v___x_1884_; 
v___x_1884_ = 2;
return v___x_1884_;
}
else
{
uint8_t v___x_1885_; 
v___x_1885_ = 0;
return v___x_1885_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1883_ = stack[0].m_obj;
uint8_t v_res_1886_;
v_res_1886_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(v_e_1883_);
stack->m_num = v_res_1886_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13___boxed(lean_object* v_e_1887_){
_start:
{
uint8_t v_res_1888_; lean_object* v_r_1889_; 
v_res_1888_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(v_e_1887_);
lean_dec_ref(v_e_1887_);
v_r_1889_ = lean_box(v_res_1888_);
return v_r_1889_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(lean_object* v_cls_1890_, uint8_t v_collapsed_1891_, lean_object* v_tag_1892_, lean_object* v_opts_1893_, uint8_t v_clsEnabled_1894_, lean_object* v_oldTraces_1895_, lean_object* v_msg_1896_, lean_object* v_resStartStop_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_fst_1913_; lean_object* v_snd_1914_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v_data_1918_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; lean_object* v___y_1934_; lean_object* v_a_1935_; uint8_t v___y_1950_; double v___y_1982_; 
v_fst_1913_ = lean_ctor_get(v_resStartStop_1897_, 0);
lean_inc(v_fst_1913_);
v_snd_1914_ = lean_ctor_get(v_resStartStop_1897_, 1);
lean_inc(v_snd_1914_);
lean_dec_ref(v_resStartStop_1897_);
v_fst_1929_ = lean_ctor_get(v_snd_1914_, 0);
lean_inc(v_fst_1929_);
v_snd_1930_ = lean_ctor_get(v_snd_1914_, 1);
lean_inc(v_snd_1930_);
lean_dec(v_snd_1914_);
v___x_1931_ = l_Lean_trace_profiler;
v___x_1932_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1893_, v___x_1931_);
if (v___x_1932_ == 0)
{
v___y_1950_ = v___x_1932_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1988_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_1893_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; double v___x_1991_; double v___x_1992_; double v___x_1993_; 
v___x_1989_ = l_Lean_trace_profiler_threshold;
v___x_1990_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1893_, v___x_1989_);
v___x_1991_ = lean_float_of_nat(v___x_1990_);
v___x_1992_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_1993_ = lean_float_div(v___x_1991_, v___x_1992_);
v___y_1982_ = v___x_1993_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; double v___x_1996_; 
v___x_1994_ = l_Lean_trace_profiler_threshold;
v___x_1995_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_1893_, v___x_1994_);
v___x_1996_ = lean_float_of_nat(v___x_1995_);
v___y_1982_ = v___x_1996_;
goto v___jp_1981_;
}
}
v___jp_1915_:
{
lean_object* v___x_1919_; 
lean_inc(v___y_1916_);
v___x_1919_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_1895_, v_data_1918_, v___y_1916_, v___y_1917_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v___x_1920_; 
lean_dec_ref_known(v___x_1919_, 1);
v___x_1920_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1913_);
return v___x_1920_;
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_fst_1913_);
v_a_1921_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1919_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1919_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
v___jp_1933_:
{
uint8_t v_result_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; double v___x_1939_; lean_object* v_data_1940_; 
v_result_1936_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_spec__13(v_fst_1913_);
v___x_1937_ = lean_box(v_result_1936_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
v___x_1939_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_1892_);
lean_inc_ref(v___x_1938_);
lean_inc(v_cls_1890_);
v_data_1940_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1940_, 0, v_cls_1890_);
lean_ctor_set(v_data_1940_, 1, v___x_1938_);
lean_ctor_set(v_data_1940_, 2, v_tag_1892_);
lean_ctor_set_float(v_data_1940_, sizeof(void*)*3, v___x_1939_);
lean_ctor_set_float(v_data_1940_, sizeof(void*)*3 + 8, v___x_1939_);
lean_ctor_set_uint8(v_data_1940_, sizeof(void*)*3 + 16, v_collapsed_1891_);
if (v___x_1932_ == 0)
{
lean_dec_ref_known(v___x_1938_, 1);
lean_dec(v_snd_1930_);
lean_dec(v_fst_1929_);
lean_dec_ref(v_tag_1892_);
lean_dec(v_cls_1890_);
v___y_1916_ = v___y_1934_;
v___y_1917_ = v_a_1935_;
v_data_1918_ = v_data_1940_;
goto v___jp_1915_;
}
else
{
lean_object* v_data_1941_; double v___x_1942_; double v___x_1943_; 
lean_dec_ref_known(v_data_1940_, 3);
v_data_1941_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1941_, 0, v_cls_1890_);
lean_ctor_set(v_data_1941_, 1, v___x_1938_);
lean_ctor_set(v_data_1941_, 2, v_tag_1892_);
v___x_1942_ = lean_unbox_float(v_fst_1929_);
lean_dec(v_fst_1929_);
lean_ctor_set_float(v_data_1941_, sizeof(void*)*3, v___x_1942_);
v___x_1943_ = lean_unbox_float(v_snd_1930_);
lean_dec(v_snd_1930_);
lean_ctor_set_float(v_data_1941_, sizeof(void*)*3 + 8, v___x_1943_);
lean_ctor_set_uint8(v_data_1941_, sizeof(void*)*3 + 16, v_collapsed_1891_);
v___y_1916_ = v___y_1934_;
v___y_1917_ = v_a_1935_;
v_data_1918_ = v_data_1941_;
goto v___jp_1915_;
}
}
v___jp_1944_:
{
lean_object* v_ref_1945_; lean_object* v___x_1946_; 
v_ref_1945_ = lean_ctor_get(v___y_1910_, 2);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc(v___y_1902_);
lean_inc_ref(v___y_1901_);
lean_inc(v___y_1900_);
lean_inc(v___y_1899_);
lean_inc_ref(v___y_1898_);
lean_inc(v_fst_1913_);
v___x_1946_ = lean_apply_16(v_msg_1896_, v_fst_1913_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, lean_box(0));
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v___y_1934_ = v_ref_1945_;
v_a_1935_ = v_a_1947_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1948_; 
lean_dec_ref_known(v___x_1946_, 1);
v___x_1948_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_1934_ = v_ref_1945_;
v_a_1935_ = v___x_1948_;
goto v___jp_1933_;
}
}
v___jp_1949_:
{
if (v_clsEnabled_1894_ == 0)
{
if (v___y_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v_traceState_1952_; lean_object* v_env_1953_; lean_object* v_nextMacroScope_1954_; lean_object* v_ngen_1955_; lean_object* v_auxDeclNGen_1956_; lean_object* v_cache_1957_; lean_object* v_recordedDeps_1958_; lean_object* v_messages_1959_; lean_object* v_infoState_1960_; lean_object* v_snapshotTasks_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_snd_1930_);
lean_dec(v_fst_1929_);
lean_dec_ref(v_msg_1896_);
lean_dec_ref(v_tag_1892_);
lean_dec(v_cls_1890_);
v___x_1951_ = lean_st_ref_take(v___y_1911_);
v_traceState_1952_ = lean_ctor_get(v___x_1951_, 4);
v_env_1953_ = lean_ctor_get(v___x_1951_, 0);
v_nextMacroScope_1954_ = lean_ctor_get(v___x_1951_, 1);
v_ngen_1955_ = lean_ctor_get(v___x_1951_, 2);
v_auxDeclNGen_1956_ = lean_ctor_get(v___x_1951_, 3);
v_cache_1957_ = lean_ctor_get(v___x_1951_, 5);
v_recordedDeps_1958_ = lean_ctor_get(v___x_1951_, 6);
v_messages_1959_ = lean_ctor_get(v___x_1951_, 7);
v_infoState_1960_ = lean_ctor_get(v___x_1951_, 8);
v_snapshotTasks_1961_ = lean_ctor_get(v___x_1951_, 9);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1963_ = v___x_1951_;
v_isShared_1964_ = v_isSharedCheck_1980_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_snapshotTasks_1961_);
lean_inc(v_infoState_1960_);
lean_inc(v_messages_1959_);
lean_inc(v_recordedDeps_1958_);
lean_inc(v_cache_1957_);
lean_inc(v_traceState_1952_);
lean_inc(v_auxDeclNGen_1956_);
lean_inc(v_ngen_1955_);
lean_inc(v_nextMacroScope_1954_);
lean_inc(v_env_1953_);
lean_dec(v___x_1951_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1980_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
uint64_t v_tid_1965_; lean_object* v_traces_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1979_; 
v_tid_1965_ = lean_ctor_get_uint64(v_traceState_1952_, sizeof(void*)*1);
v_traces_1966_ = lean_ctor_get(v_traceState_1952_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_traceState_1952_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1968_ = v_traceState_1952_;
v_isShared_1969_ = v_isSharedCheck_1979_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_traces_1966_);
lean_dec(v_traceState_1952_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1979_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1895_, v_traces_1966_);
lean_dec_ref(v_traces_1966_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1970_);
lean_ctor_set_uint64(v_reuseFailAlloc_1978_, sizeof(void*)*1, v_tid_1965_);
v___x_1972_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 4, v___x_1972_);
v___x_1974_ = v___x_1963_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_env_1953_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_nextMacroScope_1954_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_ngen_1955_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_auxDeclNGen_1956_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1977_, 5, v_cache_1957_);
lean_ctor_set(v_reuseFailAlloc_1977_, 6, v_recordedDeps_1958_);
lean_ctor_set(v_reuseFailAlloc_1977_, 7, v_messages_1959_);
lean_ctor_set(v_reuseFailAlloc_1977_, 8, v_infoState_1960_);
lean_ctor_set(v_reuseFailAlloc_1977_, 9, v_snapshotTasks_1961_);
v___x_1974_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_st_ref_put(v___y_1911_, v___x_1974_);
v___x_1976_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_1913_);
return v___x_1976_;
}
}
}
}
}
else
{
goto v___jp_1944_;
}
}
else
{
goto v___jp_1944_;
}
}
v___jp_1981_:
{
double v___x_1983_; double v___x_1984_; double v___x_1985_; uint8_t v___x_1986_; 
v___x_1983_ = lean_unbox_float(v_snd_1930_);
v___x_1984_ = lean_unbox_float(v_fst_1929_);
v___x_1985_ = lean_float_sub(v___x_1983_, v___x_1984_);
v___x_1986_ = lean_float_decLt(v___y_1982_, v___x_1985_);
v___y_1950_ = v___x_1986_;
goto v___jp_1949_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1890_ = stack[0].m_obj;
uint8_t v_collapsed_1891_ = stack[1].m_num;
lean_object* v_tag_1892_ = stack[2].m_obj;
lean_object* v_opts_1893_ = stack[3].m_obj;
uint8_t v_clsEnabled_1894_ = stack[4].m_num;
lean_object* v_oldTraces_1895_ = stack[5].m_obj;
lean_object* v_msg_1896_ = stack[6].m_obj;
lean_object* v_resStartStop_1897_ = stack[7].m_obj;
lean_object* v___y_1898_ = stack[8].m_obj;
lean_object* v___y_1899_ = stack[9].m_obj;
lean_object* v___y_1900_ = stack[10].m_obj;
lean_object* v___y_1901_ = stack[11].m_obj;
lean_object* v___y_1902_ = stack[12].m_obj;
lean_object* v___y_1903_ = stack[13].m_obj;
lean_object* v___y_1904_ = stack[14].m_obj;
lean_object* v___y_1905_ = stack[15].m_obj;
lean_object* v___y_1906_ = stack[16].m_obj;
lean_object* v___y_1907_ = stack[17].m_obj;
lean_object* v___y_1908_ = stack[18].m_obj;
lean_object* v___y_1909_ = stack[19].m_obj;
lean_object* v___y_1910_ = stack[20].m_obj;
lean_object* v___y_1911_ = stack[21].m_obj;
lean_object* v_res_1997_;
v_res_1997_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v_cls_1890_, v_collapsed_1891_, v_tag_1892_, v_opts_1893_, v_clsEnabled_1894_, v_oldTraces_1895_, v_msg_1896_, v_resStartStop_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
stack->m_obj
 = v_res_1997_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7___boxed(lean_object** _args){
lean_object* v_cls_1998_ = _args[0];
lean_object* v_collapsed_1999_ = _args[1];
lean_object* v_tag_2000_ = _args[2];
lean_object* v_opts_2001_ = _args[3];
lean_object* v_clsEnabled_2002_ = _args[4];
lean_object* v_oldTraces_2003_ = _args[5];
lean_object* v_msg_2004_ = _args[6];
lean_object* v_resStartStop_2005_ = _args[7];
lean_object* v___y_2006_ = _args[8];
lean_object* v___y_2007_ = _args[9];
lean_object* v___y_2008_ = _args[10];
lean_object* v___y_2009_ = _args[11];
lean_object* v___y_2010_ = _args[12];
lean_object* v___y_2011_ = _args[13];
lean_object* v___y_2012_ = _args[14];
lean_object* v___y_2013_ = _args[15];
lean_object* v___y_2014_ = _args[16];
lean_object* v___y_2015_ = _args[17];
lean_object* v___y_2016_ = _args[18];
lean_object* v___y_2017_ = _args[19];
lean_object* v___y_2018_ = _args[20];
lean_object* v___y_2019_ = _args[21];
lean_object* v___y_2020_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_2021_; uint8_t v_clsEnabled_boxed_2022_; lean_object* v_res_2023_; 
v_collapsed_boxed_2021_ = lean_unbox(v_collapsed_1999_);
v_clsEnabled_boxed_2022_ = lean_unbox(v_clsEnabled_2002_);
v_res_2023_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v_cls_1998_, v_collapsed_boxed_2021_, v_tag_2000_, v_opts_2001_, v_clsEnabled_boxed_2022_, v_oldTraces_2003_, v_msg_2004_, v_resStartStop_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec_ref(v_opts_2001_);
return v_res_2023_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__2));
v___x_2029_ = l_Lean_stringToMessageData(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4(void){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__4);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__5);
v___x_2034_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
lean_ctor_set(v___x_2034_, 2, v___x_2033_);
lean_ctor_set(v___x_2034_, 3, v___x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__7));
v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
return v___x_2037_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9(void){
_start:
{
lean_object* v___x_2038_; double v___x_2039_; 
v___x_2038_ = lean_unsigned_to_nat(1000000000u);
v___x_2039_ = lean_float_of_nat(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__15));
v___x_2047_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__14));
v___x_2048_ = l_System_FilePath_join(v___x_2047_, v___x_2046_);
return v___x_2048_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(lean_object* v_tacticContext_2049_, lean_object* v___x_2050_, lean_object* v_aig_2051_, lean_object* v___x_2052_, lean_object* v___x_2053_, lean_object* v___x_2054_, uint8_t v_hasTrace_2055_, lean_object* v___x_2056_, lean_object* v___f_2057_, lean_object* v___x_2058_, lean_object* v_cache_2059_, lean_object* v_ref_2060_, uint8_t v___x_2061_, lean_object* v_cls_2062_, lean_object* v___f_2063_, lean_object* v_cnfCache_2064_, lean_object* v___x_2065_, lean_object* v_result_2066_, lean_object* v___x_2067_, lean_object* v___x_2068_, lean_object* v_____r_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; uint8_t v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v_a_2263_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; uint8_t v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v_a_2295_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; uint8_t v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; uint8_t v___y_2380_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; uint8_t v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v_a_2555_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; uint8_t v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v_a_2588_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; uint8_t v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v_config_2707_; uint8_t v_graphviz_2708_; 
v_config_2707_ = lean_ctor_get(v_tacticContext_2049_, 5);
v_graphviz_2708_ = lean_ctor_get_uint8(v_config_2707_, sizeof(void*)*3 + 8);
if (v_graphviz_2708_ == 0)
{
v___y_2674_ = v___y_2070_;
v___y_2675_ = v___y_2071_;
v___y_2676_ = v___y_2072_;
v___y_2677_ = v___y_2073_;
v___y_2678_ = v___y_2074_;
v___y_2679_ = v___y_2075_;
v___y_2680_ = v___y_2076_;
v___y_2681_ = v___y_2077_;
v___y_2682_ = v___y_2078_;
v___y_2683_ = v___y_2079_;
v___y_2684_ = v___y_2080_;
v___y_2685_ = v___y_2081_;
v___y_2686_ = v___y_2082_;
v___y_2687_ = v___y_2083_;
goto v___jp_2673_;
}
else
{
lean_object* v_ref_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_ref_2709_ = lean_ctor_get(v___y_2082_, 2);
v___x_2710_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
lean_inc_ref(v_result_2066_);
v___x_2711_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v_result_2066_);
v___x_2712_ = l_IO_FS_writeFile(v___x_2710_, v___x_2711_);
lean_dec_ref(v___x_2711_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_dec_ref_known(v___x_2712_, 1);
v___y_2674_ = v___y_2070_;
v___y_2675_ = v___y_2071_;
v___y_2676_ = v___y_2072_;
v___y_2677_ = v___y_2073_;
v___y_2678_ = v___y_2074_;
v___y_2679_ = v___y_2075_;
v___y_2680_ = v___y_2076_;
v___y_2681_ = v___y_2077_;
v___y_2682_ = v___y_2078_;
v___y_2683_ = v___y_2079_;
v___y_2684_ = v___y_2080_;
v___y_2685_ = v___y_2081_;
v___y_2686_ = v___y_2082_;
v___y_2687_ = v___y_2083_;
goto v___jp_2673_;
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v___x_2068_);
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_result_2066_);
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_cnfCache_2064_);
lean_dec_ref(v___f_2063_);
lean_dec(v_cls_2062_);
lean_dec_ref(v_cache_2059_);
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___x_2056_);
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_aig_2051_);
lean_dec_ref(v_tacticContext_2049_);
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2724_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2724_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2717_ = lean_io_error_to_string(v_a_2713_);
v___x_2718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
v___x_2719_ = l_Lean_MessageData_ofFormat(v___x_2718_);
lean_inc(v_ref_2709_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v_ref_2709_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2720_);
v___x_2722_ = v___x_2715_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
v___jp_2085_:
{
lean_object* v___x_2100_; 
v___x_2100_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___x_2050_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2090_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2112_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2112_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2112_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2107_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2051_, v_a_2101_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec(v_a_2101_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2108_);
v___x_2110_ = v___x_2105_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_a_2101_);
lean_dec_ref(v_aig_2051_);
v_a_2113_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2102_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2102_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_aig_2051_);
v_a_2121_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2100_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2100_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
v___jp_2129_:
{
if (lean_obj_tag(v___y_2145_) == 0)
{
lean_object* v_a_2146_; uint8_t v___x_2147_; 
v_a_2146_ = lean_ctor_get(v___y_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___y_2145_, 1);
v___x_2147_ = lean_unbox(v_a_2146_);
lean_dec(v_a_2146_);
switch(v___x_2147_)
{
case 0:
{
lean_object* v_toCold_2148_; lean_object* v_options_2149_; uint8_t v_hasTrace_2150_; 
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_tacticContext_2049_);
v_toCold_2148_ = lean_ctor_get(v___y_2133_, 0);
v_options_2149_ = lean_ctor_get(v_toCold_2148_, 2);
v_hasTrace_2150_ = lean_ctor_get_uint8(v_options_2149_, sizeof(void*)*1);
if (v_hasTrace_2150_ == 0)
{
lean_dec(v___y_2144_);
v___y_2086_ = v___y_2143_;
v___y_2087_ = v___y_2141_;
v___y_2088_ = v___y_2130_;
v___y_2089_ = v___y_2131_;
v___y_2090_ = v___y_2136_;
v___y_2091_ = v___y_2134_;
v___y_2092_ = v___y_2139_;
v___y_2093_ = v___y_2142_;
v___y_2094_ = v___y_2140_;
v___y_2095_ = v___y_2138_;
v___y_2096_ = v___y_2137_;
v___y_2097_ = v___y_2132_;
v___y_2098_ = v___y_2133_;
v___y_2099_ = v___y_2135_;
goto v___jp_2085_;
}
else
{
lean_object* v_inheritedTraceOptions_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v_inheritedTraceOptions_2151_ = lean_ctor_get(v_toCold_2148_, 11);
v___x_2152_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2144_);
v___x_2153_ = l_Lean_Name_append(v___x_2152_, v___y_2144_);
v___x_2154_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2151_, v_options_2149_, v___x_2153_);
lean_dec(v___x_2153_);
if (v___x_2154_ == 0)
{
lean_dec(v___y_2144_);
v___y_2086_ = v___y_2143_;
v___y_2087_ = v___y_2141_;
v___y_2088_ = v___y_2130_;
v___y_2089_ = v___y_2131_;
v___y_2090_ = v___y_2136_;
v___y_2091_ = v___y_2134_;
v___y_2092_ = v___y_2139_;
v___y_2093_ = v___y_2142_;
v___y_2094_ = v___y_2140_;
v___y_2095_ = v___y_2138_;
v___y_2096_ = v___y_2137_;
v___y_2097_ = v___y_2132_;
v___y_2098_ = v___y_2133_;
v___y_2099_ = v___y_2135_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
v___x_2156_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_2144_, v___x_2155_, v___y_2137_, v___y_2132_, v___y_2133_, v___y_2135_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_dec_ref_known(v___x_2156_, 1);
v___y_2086_ = v___y_2143_;
v___y_2087_ = v___y_2141_;
v___y_2088_ = v___y_2130_;
v___y_2089_ = v___y_2131_;
v___y_2090_ = v___y_2136_;
v___y_2091_ = v___y_2134_;
v___y_2092_ = v___y_2139_;
v___y_2093_ = v___y_2142_;
v___y_2094_ = v___y_2140_;
v___y_2095_ = v___y_2138_;
v___y_2096_ = v___y_2137_;
v___y_2097_ = v___y_2132_;
v___y_2098_ = v___y_2133_;
v___y_2099_ = v___y_2135_;
goto v___jp_2085_;
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v_aig_2051_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
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
}
}
}
case 1:
{
lean_object* v___x_2165_; lean_object* v_satExpr_2166_; lean_object* v_hypQueue_2167_; lean_object* v_usedHyps_2168_; uint8_t v_didChange_2169_; lean_object* v_theoryState_2170_; lean_object* v_solverTimeBudgetMs_2171_; lean_object* v_roundBudget_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v___y_2144_);
lean_dec_ref(v_aig_2051_);
v___x_2165_ = lean_st_ref_take(v___y_2141_);
v_satExpr_2166_ = lean_ctor_get(v___x_2165_, 0);
v_hypQueue_2167_ = lean_ctor_get(v___x_2165_, 1);
v_usedHyps_2168_ = lean_ctor_get(v___x_2165_, 2);
v_didChange_2169_ = lean_ctor_get_uint8(v___x_2165_, sizeof(void*)*6);
v_theoryState_2170_ = lean_ctor_get(v___x_2165_, 3);
v_solverTimeBudgetMs_2171_ = lean_ctor_get(v___x_2165_, 4);
v_roundBudget_2172_ = lean_ctor_get(v___x_2165_, 5);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2174_ = v___x_2165_;
v_isShared_2175_ = v_isSharedCheck_2233_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_roundBudget_2172_);
lean_inc(v_solverTimeBudgetMs_2171_);
lean_inc(v_theoryState_2170_);
lean_inc(v_usedHyps_2168_);
lean_inc(v_hypQueue_2167_);
lean_inc(v_satExpr_2166_);
lean_dec(v___x_2165_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2233_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v_satSolver_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2229_; 
v___x_2176_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_2177_ = lean_ctor_get(v_theoryState_2170_, 3);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_theoryState_2170_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2230_ = lean_ctor_get(v_theoryState_2170_, 2);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_theoryState_2170_, 1);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_theoryState_2170_, 0);
lean_dec(v_unused_2232_);
v___x_2179_ = v_theoryState_2170_;
v_isShared_2180_ = v_isSharedCheck_2229_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_satSolver_2177_);
lean_dec(v_theoryState_2170_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2229_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_mk_array(v___x_2052_, v___x_2181_);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2053_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 2, v___x_2176_);
lean_ctor_set(v___x_2179_, 1, v___x_2054_);
lean_ctor_set(v___x_2179_, 0, v___x_2183_);
v___x_2185_ = v___x_2179_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_satSolver_2177_);
v___x_2185_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2187_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 3, v___x_2185_);
v___x_2187_ = v___x_2174_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_satExpr_2166_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_hypQueue_2167_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_usedHyps_2168_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_solverTimeBudgetMs_2171_);
lean_ctor_set(v_reuseFailAlloc_2227_, 5, v_roundBudget_2172_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*6, v_didChange_2169_);
v___x_2187_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_st_ref_put(v___y_2141_, v___x_2187_);
v___x_2189_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_2143_, v___y_2141_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v_goal_2191_; lean_object* v___x_2192_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v_goal_2191_ = lean_ctor_get(v___y_2143_, 0);
lean_inc(v_goal_2191_);
v___x_2192_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_tacticContext_2049_, v_goal_2191_, v_a_2190_, v___y_2130_, v___y_2131_, v___y_2136_, v___y_2134_, v___y_2139_, v___y_2142_, v___y_2140_, v___y_2138_, v___y_2137_, v___y_2132_, v___y_2133_, v___y_2135_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2210_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2210_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2210_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
if (lean_obj_tag(v_a_2193_) == 0)
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref_known(v_a_2193_, 1);
lean_del_object(v___x_2195_);
v___x_2197_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_2198_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_2197_, v___y_2137_, v___y_2132_, v___y_2133_, v___y_2135_);
return v___x_2198_;
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2209_; 
v_a_2199_ = lean_ctor_get(v_a_2193_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_a_2193_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2201_ = v_a_2193_;
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v_a_2193_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2204_);
v___x_2206_ = v___x_2195_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
v_a_2211_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2192_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2192_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec_ref(v_tacticContext_2049_);
v_a_2219_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2189_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2189_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
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
lean_object* v___x_2234_; 
lean_dec(v___y_2144_);
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_aig_2051_);
lean_dec_ref(v_tacticContext_2049_);
v___x_2234_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_2133_, v___y_2135_);
return v___x_2234_;
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v___y_2144_);
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_aig_2051_);
lean_dec_ref(v_tacticContext_2049_);
v_a_2235_ = lean_ctor_get(v___y_2145_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___y_2145_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___y_2145_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___y_2145_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
v___jp_2243_:
{
lean_object* v___x_2264_; double v___x_2265_; double v___x_2266_; double v___x_2267_; double v___x_2268_; double v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2264_ = lean_io_mono_nanos_now();
v___x_2265_ = lean_float_of_nat(v___y_2244_);
v___x_2266_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2267_ = lean_float_div(v___x_2265_, v___x_2266_);
v___x_2268_ = lean_float_of_nat(v___x_2264_);
v___x_2269_ = lean_float_div(v___x_2268_, v___x_2266_);
v___x_2270_ = lean_box_float(v___x_2267_);
v___x_2271_ = lean_box_float(v___x_2269_);
v___x_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v_a_2263_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
lean_inc(v___y_2262_);
v___x_2274_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2262_, v_hasTrace_2055_, v___x_2056_, v___y_2255_, v___y_2258_, v___y_2248_, v___f_2057_, v___x_2273_, v___y_2261_, v___y_2259_, v___y_2245_, v___y_2247_, v___y_2252_, v___y_2250_, v___y_2256_, v___y_2260_, v___y_2257_, v___y_2254_, v___y_2253_, v___y_2246_, v___y_2249_, v___y_2251_);
v___y_2130_ = v___y_2245_;
v___y_2131_ = v___y_2247_;
v___y_2132_ = v___y_2246_;
v___y_2133_ = v___y_2249_;
v___y_2134_ = v___y_2250_;
v___y_2135_ = v___y_2251_;
v___y_2136_ = v___y_2252_;
v___y_2137_ = v___y_2253_;
v___y_2138_ = v___y_2254_;
v___y_2139_ = v___y_2256_;
v___y_2140_ = v___y_2257_;
v___y_2141_ = v___y_2259_;
v___y_2142_ = v___y_2260_;
v___y_2143_ = v___y_2261_;
v___y_2144_ = v___y_2262_;
v___y_2145_ = v___x_2274_;
goto v___jp_2129_;
}
v___jp_2275_:
{
lean_object* v___x_2296_; double v___x_2297_; double v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2296_ = lean_io_get_num_heartbeats();
v___x_2297_ = lean_float_of_nat(v___y_2284_);
v___x_2298_ = lean_float_of_nat(v___x_2296_);
v___x_2299_ = lean_box_float(v___x_2297_);
v___x_2300_ = lean_box_float(v___x_2298_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v_a_2295_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
lean_inc(v___y_2294_);
v___x_2303_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2294_, v_hasTrace_2055_, v___x_2056_, v___y_2287_, v___y_2290_, v___y_2279_, v___f_2057_, v___x_2302_, v___y_2293_, v___y_2291_, v___y_2276_, v___y_2278_, v___y_2283_, v___y_2281_, v___y_2288_, v___y_2292_, v___y_2289_, v___y_2286_, v___y_2285_, v___y_2277_, v___y_2280_, v___y_2282_);
v___y_2130_ = v___y_2276_;
v___y_2131_ = v___y_2278_;
v___y_2132_ = v___y_2277_;
v___y_2133_ = v___y_2280_;
v___y_2134_ = v___y_2281_;
v___y_2135_ = v___y_2282_;
v___y_2136_ = v___y_2283_;
v___y_2137_ = v___y_2285_;
v___y_2138_ = v___y_2286_;
v___y_2139_ = v___y_2288_;
v___y_2140_ = v___y_2289_;
v___y_2141_ = v___y_2291_;
v___y_2142_ = v___y_2292_;
v___y_2143_ = v___y_2293_;
v___y_2144_ = v___y_2294_;
v___y_2145_ = v___x_2303_;
goto v___jp_2129_;
}
v___jp_2304_:
{
lean_object* v___x_2323_; lean_object* v_a_2324_; uint8_t v___x_2325_; 
v___x_2323_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_2310_);
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_2313_, v___x_2058_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_io_mono_nanos_now();
v___x_2327_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2321_, v___y_2320_, v___y_2318_, v___y_2305_, v___y_2306_, v___y_2311_, v___y_2308_, v___y_2315_, v___y_2319_, v___y_2316_, v___y_2314_, v___y_2312_, v___y_2307_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 1);
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
v___y_2244_ = v___x_2326_;
v___y_2245_ = v___y_2305_;
v___y_2246_ = v___y_2307_;
v___y_2247_ = v___y_2306_;
v___y_2248_ = v_a_2324_;
v___y_2249_ = v___y_2309_;
v___y_2250_ = v___y_2308_;
v___y_2251_ = v___y_2310_;
v___y_2252_ = v___y_2311_;
v___y_2253_ = v___y_2312_;
v___y_2254_ = v___y_2314_;
v___y_2255_ = v___y_2313_;
v___y_2256_ = v___y_2315_;
v___y_2257_ = v___y_2316_;
v___y_2258_ = v___y_2317_;
v___y_2259_ = v___y_2318_;
v___y_2260_ = v___y_2319_;
v___y_2261_ = v___y_2320_;
v___y_2262_ = v___y_2322_;
v_a_2263_ = v___x_2333_;
goto v___jp_2243_;
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
v_a_2336_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2327_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2327_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 0);
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
v___y_2244_ = v___x_2326_;
v___y_2245_ = v___y_2305_;
v___y_2246_ = v___y_2307_;
v___y_2247_ = v___y_2306_;
v___y_2248_ = v_a_2324_;
v___y_2249_ = v___y_2309_;
v___y_2250_ = v___y_2308_;
v___y_2251_ = v___y_2310_;
v___y_2252_ = v___y_2311_;
v___y_2253_ = v___y_2312_;
v___y_2254_ = v___y_2314_;
v___y_2255_ = v___y_2313_;
v___y_2256_ = v___y_2315_;
v___y_2257_ = v___y_2316_;
v___y_2258_ = v___y_2317_;
v___y_2259_ = v___y_2318_;
v___y_2260_ = v___y_2319_;
v___y_2261_ = v___y_2320_;
v___y_2262_ = v___y_2322_;
v_a_2263_ = v___x_2341_;
goto v___jp_2243_;
}
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_io_get_num_heartbeats();
v___x_2345_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2321_, v___y_2320_, v___y_2318_, v___y_2305_, v___y_2306_, v___y_2311_, v___y_2308_, v___y_2315_, v___y_2319_, v___y_2316_, v___y_2314_, v___y_2312_, v___y_2307_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 1);
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
v___y_2276_ = v___y_2305_;
v___y_2277_ = v___y_2307_;
v___y_2278_ = v___y_2306_;
v___y_2279_ = v_a_2324_;
v___y_2280_ = v___y_2309_;
v___y_2281_ = v___y_2308_;
v___y_2282_ = v___y_2310_;
v___y_2283_ = v___y_2311_;
v___y_2284_ = v___x_2344_;
v___y_2285_ = v___y_2312_;
v___y_2286_ = v___y_2314_;
v___y_2287_ = v___y_2313_;
v___y_2288_ = v___y_2315_;
v___y_2289_ = v___y_2316_;
v___y_2290_ = v___y_2317_;
v___y_2291_ = v___y_2318_;
v___y_2292_ = v___y_2319_;
v___y_2293_ = v___y_2320_;
v___y_2294_ = v___y_2322_;
v_a_2295_ = v___x_2351_;
goto v___jp_2275_;
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2345_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2345_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 0);
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
v___y_2276_ = v___y_2305_;
v___y_2277_ = v___y_2307_;
v___y_2278_ = v___y_2306_;
v___y_2279_ = v_a_2324_;
v___y_2280_ = v___y_2309_;
v___y_2281_ = v___y_2308_;
v___y_2282_ = v___y_2310_;
v___y_2283_ = v___y_2311_;
v___y_2284_ = v___x_2344_;
v___y_2285_ = v___y_2312_;
v___y_2286_ = v___y_2314_;
v___y_2287_ = v___y_2313_;
v___y_2288_ = v___y_2315_;
v___y_2289_ = v___y_2316_;
v___y_2290_ = v___y_2317_;
v___y_2291_ = v___y_2318_;
v___y_2292_ = v___y_2319_;
v___y_2293_ = v___y_2320_;
v___y_2294_ = v___y_2322_;
v_a_2295_ = v___x_2359_;
goto v___jp_2275_;
}
}
}
}
}
v___jp_2362_:
{
lean_object* v_toCold_2381_; lean_object* v_ref_2382_; lean_object* v___x_2383_; 
v_toCold_2381_ = lean_ctor_get(v___y_2366_, 0);
v_ref_2382_ = lean_ctor_get(v___y_2366_, 2);
lean_inc_ref(v___y_2379_);
v___x_2383_ = l_Lean_Cadical_Solver_assume(v___y_2379_, v___y_2373_, v___y_2380_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_options_2384_; uint8_t v_hasTrace_2385_; 
lean_dec_ref_known(v___x_2383_, 1);
v_options_2384_ = lean_ctor_get(v_toCold_2381_, 2);
v_hasTrace_2385_ = lean_ctor_get_uint8(v_options_2384_, sizeof(void*)*1);
if (v_hasTrace_2385_ == 0)
{
lean_object* v___x_2386_; 
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___x_2056_);
v___x_2386_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2379_, v___y_2377_, v___y_2375_, v___y_2363_, v___y_2365_, v___y_2369_, v___y_2367_, v___y_2372_, v___y_2376_, v___y_2374_, v___y_2371_, v___y_2370_, v___y_2364_, v___y_2366_, v___y_2368_);
v___y_2130_ = v___y_2363_;
v___y_2131_ = v___y_2365_;
v___y_2132_ = v___y_2364_;
v___y_2133_ = v___y_2366_;
v___y_2134_ = v___y_2367_;
v___y_2135_ = v___y_2368_;
v___y_2136_ = v___y_2369_;
v___y_2137_ = v___y_2370_;
v___y_2138_ = v___y_2371_;
v___y_2139_ = v___y_2372_;
v___y_2140_ = v___y_2374_;
v___y_2141_ = v___y_2375_;
v___y_2142_ = v___y_2376_;
v___y_2143_ = v___y_2377_;
v___y_2144_ = v___y_2378_;
v___y_2145_ = v___x_2386_;
goto v___jp_2129_;
}
else
{
lean_object* v_inheritedTraceOptions_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v_inheritedTraceOptions_2387_ = lean_ctor_get(v_toCold_2381_, 11);
v___x_2388_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2378_);
v___x_2389_ = l_Lean_Name_append(v___x_2388_, v___y_2378_);
v___x_2390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2387_, v_options_2384_, v___x_2389_);
lean_dec(v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = l_Lean_trace_profiler;
v___x_2392_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_2384_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___x_2056_);
v___x_2393_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_2379_, v___y_2377_, v___y_2375_, v___y_2363_, v___y_2365_, v___y_2369_, v___y_2367_, v___y_2372_, v___y_2376_, v___y_2374_, v___y_2371_, v___y_2370_, v___y_2364_, v___y_2366_, v___y_2368_);
v___y_2130_ = v___y_2363_;
v___y_2131_ = v___y_2365_;
v___y_2132_ = v___y_2364_;
v___y_2133_ = v___y_2366_;
v___y_2134_ = v___y_2367_;
v___y_2135_ = v___y_2368_;
v___y_2136_ = v___y_2369_;
v___y_2137_ = v___y_2370_;
v___y_2138_ = v___y_2371_;
v___y_2139_ = v___y_2372_;
v___y_2140_ = v___y_2374_;
v___y_2141_ = v___y_2375_;
v___y_2142_ = v___y_2376_;
v___y_2143_ = v___y_2377_;
v___y_2144_ = v___y_2378_;
v___y_2145_ = v___x_2393_;
goto v___jp_2129_;
}
else
{
v___y_2305_ = v___y_2363_;
v___y_2306_ = v___y_2365_;
v___y_2307_ = v___y_2364_;
v___y_2308_ = v___y_2367_;
v___y_2309_ = v___y_2366_;
v___y_2310_ = v___y_2368_;
v___y_2311_ = v___y_2369_;
v___y_2312_ = v___y_2370_;
v___y_2313_ = v_options_2384_;
v___y_2314_ = v___y_2371_;
v___y_2315_ = v___y_2372_;
v___y_2316_ = v___y_2374_;
v___y_2317_ = v___x_2390_;
v___y_2318_ = v___y_2375_;
v___y_2319_ = v___y_2376_;
v___y_2320_ = v___y_2377_;
v___y_2321_ = v___y_2379_;
v___y_2322_ = v___y_2378_;
goto v___jp_2304_;
}
}
else
{
v___y_2305_ = v___y_2363_;
v___y_2306_ = v___y_2365_;
v___y_2307_ = v___y_2364_;
v___y_2308_ = v___y_2367_;
v___y_2309_ = v___y_2366_;
v___y_2310_ = v___y_2368_;
v___y_2311_ = v___y_2369_;
v___y_2312_ = v___y_2370_;
v___y_2313_ = v_options_2384_;
v___y_2314_ = v___y_2371_;
v___y_2315_ = v___y_2372_;
v___y_2316_ = v___y_2374_;
v___y_2317_ = v___x_2390_;
v___y_2318_ = v___y_2375_;
v___y_2319_ = v___y_2376_;
v___y_2320_ = v___y_2377_;
v___y_2321_ = v___y_2379_;
v___y_2322_ = v___y_2378_;
goto v___jp_2304_;
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___x_2056_);
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_aig_2051_);
lean_dec_ref(v_tacticContext_2049_);
v_a_2394_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2396_ = v___x_2383_;
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2383_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2398_ = lean_io_error_to_string(v_a_2394_);
v___x_2399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
v___x_2400_ = l_Lean_MessageData_ofFormat(v___x_2399_);
lean_inc(v_ref_2382_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v_ref_2382_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2401_);
v___x_2403_ = v___x_2396_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
v___jp_2406_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_theoryState_2427_; lean_object* v_satExpr_2428_; lean_object* v_hypQueue_2429_; lean_object* v_usedHyps_2430_; uint8_t v_didChange_2431_; lean_object* v_solverTimeBudgetMs_2432_; lean_object* v_roundBudget_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2475_; 
lean_inc_ref(v_aig_2051_);
v___x_2425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2425_, 0, v_aig_2051_);
lean_ctor_set(v___x_2425_, 1, v_cache_2059_);
lean_ctor_set(v___x_2425_, 2, v___y_2407_);
v___x_2426_ = lean_st_ref_take(v___y_2412_);
v_theoryState_2427_ = lean_ctor_get(v___x_2426_, 3);
v_satExpr_2428_ = lean_ctor_get(v___x_2426_, 0);
v_hypQueue_2429_ = lean_ctor_get(v___x_2426_, 1);
v_usedHyps_2430_ = lean_ctor_get(v___x_2426_, 2);
v_didChange_2431_ = lean_ctor_get_uint8(v___x_2426_, sizeof(void*)*6);
v_solverTimeBudgetMs_2432_ = lean_ctor_get(v___x_2426_, 4);
v_roundBudget_2433_ = lean_ctor_get(v___x_2426_, 5);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2435_ = v___x_2426_;
v_isShared_2436_ = v_isSharedCheck_2475_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_roundBudget_2433_);
lean_inc(v_solverTimeBudgetMs_2432_);
lean_inc(v_theoryState_2427_);
lean_inc(v_usedHyps_2430_);
lean_inc(v_hypQueue_2429_);
lean_inc(v_satExpr_2428_);
lean_dec(v___x_2426_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2475_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v_funState_2437_; lean_object* v_preprocessCaches_2438_; lean_object* v_satSolver_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2473_; 
v_funState_2437_ = lean_ctor_get(v_theoryState_2427_, 0);
v_preprocessCaches_2438_ = lean_ctor_get(v_theoryState_2427_, 2);
v_satSolver_2439_ = lean_ctor_get(v_theoryState_2427_, 3);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_theoryState_2427_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v_theoryState_2427_, 1);
lean_dec(v_unused_2474_);
v___x_2441_ = v_theoryState_2427_;
v_isShared_2442_ = v_isSharedCheck_2473_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_satSolver_2439_);
lean_inc(v_preprocessCaches_2438_);
lean_inc(v_funState_2437_);
lean_dec(v_theoryState_2427_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2473_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v___x_2425_);
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_funState_2437_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_preprocessCaches_2438_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_satSolver_2439_);
v___x_2444_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2446_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 3, v___x_2444_);
v___x_2446_ = v___x_2435_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_satExpr_2428_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_hypQueue_2429_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_usedHyps_2430_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_solverTimeBudgetMs_2432_);
lean_ctor_set(v_reuseFailAlloc_2471_, 5, v_roundBudget_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2471_, sizeof(void*)*6, v_didChange_2431_);
v___x_2446_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_st_ref_put(v___y_2412_, v___x_2446_);
v___x_2448_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_2409_, v___y_2408_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v___x_2449_; 
lean_dec_ref_known(v___x_2448_, 1);
v___x_2449_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_2412_);
if (lean_obj_tag(v___x_2449_) == 0)
{
uint8_t v_invert_2450_; 
v_invert_2450_ = lean_ctor_get_uint8(v_ref_2060_, sizeof(void*)*1);
if (v_invert_2450_ == 0)
{
lean_object* v_a_2451_; lean_object* v_gate_2452_; 
v_a_2451_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2449_, 1);
v_gate_2452_ = lean_ctor_get(v_ref_2060_, 0);
v___y_2363_ = v___y_2413_;
v___y_2364_ = v___y_2422_;
v___y_2365_ = v___y_2414_;
v___y_2366_ = v___y_2423_;
v___y_2367_ = v___y_2416_;
v___y_2368_ = v___y_2424_;
v___y_2369_ = v___y_2415_;
v___y_2370_ = v___y_2421_;
v___y_2371_ = v___y_2420_;
v___y_2372_ = v___y_2417_;
v___y_2373_ = v_gate_2452_;
v___y_2374_ = v___y_2419_;
v___y_2375_ = v___y_2412_;
v___y_2376_ = v___y_2418_;
v___y_2377_ = v___y_2411_;
v___y_2378_ = v___y_2410_;
v___y_2379_ = v_a_2451_;
v___y_2380_ = v_hasTrace_2055_;
goto v___jp_2362_;
}
else
{
lean_object* v_a_2453_; lean_object* v_gate_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2449_, 1);
v_gate_2454_ = lean_ctor_get(v_ref_2060_, 0);
v___y_2363_ = v___y_2413_;
v___y_2364_ = v___y_2422_;
v___y_2365_ = v___y_2414_;
v___y_2366_ = v___y_2423_;
v___y_2367_ = v___y_2416_;
v___y_2368_ = v___y_2424_;
v___y_2369_ = v___y_2415_;
v___y_2370_ = v___y_2421_;
v___y_2371_ = v___y_2420_;
v___y_2372_ = v___y_2417_;
v___y_2373_ = v_gate_2454_;
v___y_2374_ = v___y_2419_;
v___y_2375_ = v___y_2412_;
v___y_2376_ = v___y_2418_;
v___y_2377_ = v___y_2411_;
v___y_2378_ = v___y_2410_;
v___y_2379_ = v_a_2453_;
v___y_2380_ = v___x_2061_;
goto v___jp_2362_;
}
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v___y_2410_);
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___x_2056_);
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_aig_2051_);
lean_dec_ref(v_tacticContext_2049_);
v_a_2455_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2449_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2449_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v___y_2410_);
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___x_2056_);
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_aig_2051_);
lean_dec_ref(v_tacticContext_2049_);
v_a_2463_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2448_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2448_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
}
}
}
v___jp_2476_:
{
if (lean_obj_tag(v___y_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v_toCold_2495_; lean_object* v_options_2496_; uint8_t v_hasTrace_2497_; 
v_a_2494_ = lean_ctor_get(v___y_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___y_2493_, 1);
v_toCold_2495_ = lean_ctor_get(v___y_2477_, 0);
v_options_2496_ = lean_ctor_get(v_toCold_2495_, 2);
v_hasTrace_2497_ = lean_ctor_get_uint8(v_options_2496_, sizeof(void*)*1);
if (v_hasTrace_2497_ == 0)
{
lean_object* v_cnf_2498_; 
lean_dec(v_cls_2062_);
v_cnf_2498_ = lean_ctor_get(v_a_2494_, 0);
lean_inc_ref(v_cnf_2498_);
v___y_2407_ = v_a_2494_;
v___y_2408_ = v_cnf_2498_;
v___y_2409_ = v___y_2488_;
v___y_2410_ = v___y_2490_;
v___y_2411_ = v___y_2478_;
v___y_2412_ = v___y_2480_;
v___y_2413_ = v___y_2479_;
v___y_2414_ = v___y_2487_;
v___y_2415_ = v___y_2491_;
v___y_2416_ = v___y_2489_;
v___y_2417_ = v___y_2484_;
v___y_2418_ = v___y_2481_;
v___y_2419_ = v___y_2485_;
v___y_2420_ = v___y_2492_;
v___y_2421_ = v___y_2486_;
v___y_2422_ = v___y_2482_;
v___y_2423_ = v___y_2477_;
v___y_2424_ = v___y_2483_;
goto v___jp_2406_;
}
else
{
lean_object* v_cnf_2499_; lean_object* v_inheritedTraceOptions_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_cnf_2499_ = lean_ctor_get(v_a_2494_, 0);
lean_inc_ref(v_cnf_2499_);
v_inheritedTraceOptions_2500_ = lean_ctor_get(v_toCold_2495_, 11);
v___x_2501_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v_cls_2062_);
v___x_2502_ = l_Lean_Name_append(v___x_2501_, v_cls_2062_);
v___x_2503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2500_, v_options_2496_, v___x_2502_);
lean_dec(v___x_2502_);
if (v___x_2503_ == 0)
{
lean_dec(v_cls_2062_);
v___y_2407_ = v_a_2494_;
v___y_2408_ = v_cnf_2499_;
v___y_2409_ = v___y_2488_;
v___y_2410_ = v___y_2490_;
v___y_2411_ = v___y_2478_;
v___y_2412_ = v___y_2480_;
v___y_2413_ = v___y_2479_;
v___y_2414_ = v___y_2487_;
v___y_2415_ = v___y_2491_;
v___y_2416_ = v___y_2489_;
v___y_2417_ = v___y_2484_;
v___y_2418_ = v___y_2481_;
v___y_2419_ = v___y_2485_;
v___y_2420_ = v___y_2492_;
v___y_2421_ = v___y_2486_;
v___y_2422_ = v___y_2482_;
v___y_2423_ = v___y_2477_;
v___y_2424_ = v___y_2483_;
goto v___jp_2406_;
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2504_ = lean_array_get_size(v_cnf_2499_);
v___x_2505_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_2506_ = l_Nat_reprFast(v___x_2504_);
v___x_2507_ = lean_string_append(v___x_2505_, v___x_2506_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_2509_ = lean_string_append(v___x_2507_, v___x_2508_);
v___x_2510_ = lean_nat_sub(v___x_2504_, v___y_2488_);
v___x_2511_ = l_Nat_reprFast(v___x_2510_);
v___x_2512_ = lean_string_append(v___x_2509_, v___x_2511_);
lean_dec_ref(v___x_2511_);
v___x_2513_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_2514_ = lean_string_append(v___x_2512_, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
v___x_2516_ = l_Lean_MessageData_ofFormat(v___x_2515_);
v___x_2517_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_2062_, v___x_2516_, v___y_2486_, v___y_2482_, v___y_2477_, v___y_2483_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref_known(v___x_2517_, 1);
v___y_2407_ = v_a_2494_;
v___y_2408_ = v_cnf_2499_;
v___y_2409_ = v___y_2488_;
v___y_2410_ = v___y_2490_;
v___y_2411_ = v___y_2478_;
v___y_2412_ = v___y_2480_;
v___y_2413_ = v___y_2479_;
v___y_2414_ = v___y_2487_;
v___y_2415_ = v___y_2491_;
v___y_2416_ = v___y_2489_;
v___y_2417_ = v___y_2484_;
v___y_2418_ = v___y_2481_;
v___y_2419_ = v___y_2485_;
v___y_2420_ = v___y_2492_;
v___y_2421_ = v___y_2486_;
v___y_2422_ = v___y_2482_;
v___y_2423_ = v___y_2477_;
v___y_2424_ = v___y_2483_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_cnf_2499_);
lean_dec(v_a_2494_);
lean_dec(v___y_2490_);
lean_dec(v___y_2488_);
lean_dec_ref(v_cache_2059_);
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___x_2056_);
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_aig_2051_);
lean_dec_ref(v_tacticContext_2049_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v___y_2490_);
lean_dec(v___y_2488_);
lean_dec(v_cls_2062_);
lean_dec_ref(v_cache_2059_);
lean_dec_ref(v___f_2057_);
lean_dec_ref(v___x_2056_);
lean_dec_ref(v___x_2054_);
lean_dec(v___x_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_aig_2051_);
lean_dec_ref(v_tacticContext_2049_);
v_a_2526_ = lean_ctor_get(v___y_2493_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___y_2493_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___y_2493_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___y_2493_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
v___jp_2534_:
{
lean_object* v___x_2556_; double v___x_2557_; double v___x_2558_; double v___x_2559_; double v___x_2560_; double v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2556_ = lean_io_mono_nanos_now();
v___x_2557_ = lean_float_of_nat(v___y_2542_);
v___x_2558_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2559_ = lean_float_div(v___x_2557_, v___x_2558_);
v___x_2560_ = lean_float_of_nat(v___x_2556_);
v___x_2561_ = lean_float_div(v___x_2560_, v___x_2558_);
v___x_2562_ = lean_box_float(v___x_2559_);
v___x_2563_ = lean_box_float(v___x_2561_);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2555_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
lean_inc_ref(v___x_2056_);
lean_inc(v___y_2553_);
v___x_2566_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_2553_, v_hasTrace_2055_, v___x_2056_, v___y_2547_, v___y_2540_, v___y_2550_, v___f_2063_, v___x_2565_, v___y_2536_, v___y_2538_, v___y_2537_, v___y_2548_, v___y_2554_, v___y_2551_, v___y_2544_, v___y_2539_, v___y_2545_, v___y_2552_, v___y_2546_, v___y_2541_, v___y_2535_, v___y_2543_);
v___y_2477_ = v___y_2535_;
v___y_2478_ = v___y_2536_;
v___y_2479_ = v___y_2537_;
v___y_2480_ = v___y_2538_;
v___y_2481_ = v___y_2539_;
v___y_2482_ = v___y_2541_;
v___y_2483_ = v___y_2543_;
v___y_2484_ = v___y_2544_;
v___y_2485_ = v___y_2545_;
v___y_2486_ = v___y_2546_;
v___y_2487_ = v___y_2548_;
v___y_2488_ = v___y_2549_;
v___y_2489_ = v___y_2551_;
v___y_2490_ = v___y_2553_;
v___y_2491_ = v___y_2554_;
v___y_2492_ = v___y_2552_;
v___y_2493_ = v___x_2566_;
goto v___jp_2476_;
}
v___jp_2567_:
{
lean_object* v___x_2589_; double v___x_2590_; double v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2589_ = lean_io_get_num_heartbeats();
v___x_2590_ = lean_float_of_nat(v___y_2582_);
v___x_2591_ = lean_float_of_nat(v___x_2589_);
v___x_2592_ = lean_box_float(v___x_2590_);
v___x_2593_ = lean_box_float(v___x_2591_);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v_a_2588_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
lean_inc_ref(v___x_2056_);
lean_inc(v___y_2586_);
v___x_2596_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_2586_, v_hasTrace_2055_, v___x_2056_, v___y_2579_, v___y_2573_, v___y_2583_, v___f_2063_, v___x_2595_, v___y_2569_, v___y_2571_, v___y_2570_, v___y_2580_, v___y_2587_, v___y_2584_, v___y_2576_, v___y_2572_, v___y_2577_, v___y_2585_, v___y_2578_, v___y_2574_, v___y_2568_, v___y_2575_);
v___y_2477_ = v___y_2568_;
v___y_2478_ = v___y_2569_;
v___y_2479_ = v___y_2570_;
v___y_2480_ = v___y_2571_;
v___y_2481_ = v___y_2572_;
v___y_2482_ = v___y_2574_;
v___y_2483_ = v___y_2575_;
v___y_2484_ = v___y_2576_;
v___y_2485_ = v___y_2577_;
v___y_2486_ = v___y_2578_;
v___y_2487_ = v___y_2580_;
v___y_2488_ = v___y_2581_;
v___y_2489_ = v___y_2584_;
v___y_2490_ = v___y_2586_;
v___y_2491_ = v___y_2587_;
v___y_2492_ = v___y_2585_;
v___y_2493_ = v___x_2596_;
goto v___jp_2476_;
}
v___jp_2597_:
{
lean_object* v___x_2618_; lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2672_; 
v___x_2618_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_2606_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2672_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2672_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
uint8_t v___x_2623_; 
v___x_2623_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_2611_, v___x_2058_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_io_mono_nanos_now();
v___x_2625_ = l_IO_lazyPure___redArg(v___y_2600_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_del_object(v___x_2621_);
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 1);
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
v___y_2535_ = v___y_2599_;
v___y_2536_ = v___y_2598_;
v___y_2537_ = v___y_2601_;
v___y_2538_ = v___y_2602_;
v___y_2539_ = v___y_2603_;
v___y_2540_ = v___y_2604_;
v___y_2541_ = v___y_2605_;
v___y_2542_ = v___x_2624_;
v___y_2543_ = v___y_2606_;
v___y_2544_ = v___y_2607_;
v___y_2545_ = v___y_2609_;
v___y_2546_ = v___y_2610_;
v___y_2547_ = v___y_2611_;
v___y_2548_ = v___y_2612_;
v___y_2549_ = v___y_2613_;
v___y_2550_ = v_a_2619_;
v___y_2551_ = v___y_2614_;
v___y_2552_ = v___y_2617_;
v___y_2553_ = v___y_2615_;
v___y_2554_ = v___y_2616_;
v_a_2555_ = v___x_2631_;
goto v___jp_2534_;
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2647_; 
v_a_2634_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2636_ = v___x_2625_;
v_isShared_2637_ = v_isSharedCheck_2647_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2625_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2647_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_io_error_to_string(v_a_2634_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set_tag(v___x_2636_, 3);
lean_ctor_set(v___x_2636_, 0, v___x_2638_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2641_ = l_Lean_MessageData_ofFormat(v___x_2640_);
lean_inc(v___y_2608_);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___y_2608_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2642_);
v___x_2644_ = v___x_2621_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
v___y_2535_ = v___y_2599_;
v___y_2536_ = v___y_2598_;
v___y_2537_ = v___y_2601_;
v___y_2538_ = v___y_2602_;
v___y_2539_ = v___y_2603_;
v___y_2540_ = v___y_2604_;
v___y_2541_ = v___y_2605_;
v___y_2542_ = v___x_2624_;
v___y_2543_ = v___y_2606_;
v___y_2544_ = v___y_2607_;
v___y_2545_ = v___y_2609_;
v___y_2546_ = v___y_2610_;
v___y_2547_ = v___y_2611_;
v___y_2548_ = v___y_2612_;
v___y_2549_ = v___y_2613_;
v___y_2550_ = v_a_2619_;
v___y_2551_ = v___y_2614_;
v___y_2552_ = v___y_2617_;
v___y_2553_ = v___y_2615_;
v___y_2554_ = v___y_2616_;
v_a_2555_ = v___x_2644_;
goto v___jp_2534_;
}
}
}
}
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = lean_io_get_num_heartbeats();
v___x_2649_ = l_IO_lazyPure___redArg(v___y_2600_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_del_object(v___x_2621_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set_tag(v___x_2652_, 1);
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
v___y_2568_ = v___y_2599_;
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2601_;
v___y_2571_ = v___y_2602_;
v___y_2572_ = v___y_2603_;
v___y_2573_ = v___y_2604_;
v___y_2574_ = v___y_2605_;
v___y_2575_ = v___y_2606_;
v___y_2576_ = v___y_2607_;
v___y_2577_ = v___y_2609_;
v___y_2578_ = v___y_2610_;
v___y_2579_ = v___y_2611_;
v___y_2580_ = v___y_2612_;
v___y_2581_ = v___y_2613_;
v___y_2582_ = v___x_2648_;
v___y_2583_ = v_a_2619_;
v___y_2584_ = v___y_2614_;
v___y_2585_ = v___y_2617_;
v___y_2586_ = v___y_2615_;
v___y_2587_ = v___y_2616_;
v_a_2588_ = v___x_2655_;
goto v___jp_2567_;
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2671_; 
v_a_2658_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2660_ = v___x_2649_;
v_isShared_2661_ = v_isSharedCheck_2671_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2649_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2671_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2662_ = lean_io_error_to_string(v_a_2658_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set_tag(v___x_2660_, 3);
lean_ctor_set(v___x_2660_, 0, v___x_2662_);
v___x_2664_ = v___x_2660_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2665_ = l_Lean_MessageData_ofFormat(v___x_2664_);
lean_inc(v___y_2608_);
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___y_2608_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2666_);
v___x_2668_ = v___x_2621_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
v___y_2568_ = v___y_2599_;
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2601_;
v___y_2571_ = v___y_2602_;
v___y_2572_ = v___y_2603_;
v___y_2573_ = v___y_2604_;
v___y_2574_ = v___y_2605_;
v___y_2575_ = v___y_2606_;
v___y_2576_ = v___y_2607_;
v___y_2577_ = v___y_2609_;
v___y_2578_ = v___y_2610_;
v___y_2579_ = v___y_2611_;
v___y_2580_ = v___y_2612_;
v___y_2581_ = v___y_2613_;
v___y_2582_ = v___x_2648_;
v___y_2583_ = v_a_2619_;
v___y_2584_ = v___y_2614_;
v___y_2585_ = v___y_2617_;
v___y_2586_ = v___y_2615_;
v___y_2587_ = v___y_2616_;
v_a_2588_ = v___x_2668_;
goto v___jp_2567_;
}
}
}
}
}
}
}
v___jp_2673_:
{
lean_object* v_toCold_2688_; lean_object* v_options_2689_; lean_object* v_cnf_2690_; lean_object* v_ref_2691_; lean_object* v_inheritedTraceOptions_2692_; uint8_t v_hasTrace_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v_toCold_2688_ = lean_ctor_get(v___y_2686_, 0);
v_options_2689_ = lean_ctor_get(v_toCold_2688_, 2);
v_cnf_2690_ = lean_ctor_get(v_cnfCache_2064_, 0);
v_ref_2691_ = lean_ctor_get(v___y_2686_, 2);
v_inheritedTraceOptions_2692_ = lean_ctor_get(v_toCold_2688_, 11);
v_hasTrace_2693_ = lean_ctor_get_uint8(v_options_2689_, sizeof(void*)*1);
v___x_2694_ = lean_array_get_size(v_cnf_2690_);
v___x_2695_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_2696_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig_2051_, v_cnfCache_2064_);
v___f_2697_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_2697_, 0, v___x_2065_);
lean_closure_set(v___f_2697_, 1, v___x_2695_);
lean_closure_set(v___f_2697_, 2, v_result_2066_);
lean_closure_set(v___f_2697_, 3, v___x_2696_);
v___x_2698_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13));
v___x_2699_ = l_Lean_Name_mkStr3(v___x_2067_, v___x_2068_, v___x_2698_);
if (v_hasTrace_2693_ == 0)
{
lean_object* v___x_2700_; 
lean_dec_ref(v___f_2063_);
v___x_2700_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_2697_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
v___y_2477_ = v___y_2686_;
v___y_2478_ = v___y_2674_;
v___y_2479_ = v___y_2676_;
v___y_2480_ = v___y_2675_;
v___y_2481_ = v___y_2681_;
v___y_2482_ = v___y_2685_;
v___y_2483_ = v___y_2687_;
v___y_2484_ = v___y_2680_;
v___y_2485_ = v___y_2682_;
v___y_2486_ = v___y_2684_;
v___y_2487_ = v___y_2677_;
v___y_2488_ = v___x_2694_;
v___y_2489_ = v___y_2679_;
v___y_2490_ = v___x_2699_;
v___y_2491_ = v___y_2678_;
v___y_2492_ = v___y_2683_;
v___y_2493_ = v___x_2700_;
goto v___jp_2476_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___x_2699_);
v___x_2702_ = l_Lean_Name_append(v___x_2701_, v___x_2699_);
v___x_2703_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2692_, v_options_2689_, v___x_2702_);
lean_dec(v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = l_Lean_trace_profiler;
v___x_2705_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_2689_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; 
lean_dec_ref(v___f_2063_);
v___x_2706_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_2697_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
v___y_2477_ = v___y_2686_;
v___y_2478_ = v___y_2674_;
v___y_2479_ = v___y_2676_;
v___y_2480_ = v___y_2675_;
v___y_2481_ = v___y_2681_;
v___y_2482_ = v___y_2685_;
v___y_2483_ = v___y_2687_;
v___y_2484_ = v___y_2680_;
v___y_2485_ = v___y_2682_;
v___y_2486_ = v___y_2684_;
v___y_2487_ = v___y_2677_;
v___y_2488_ = v___x_2694_;
v___y_2489_ = v___y_2679_;
v___y_2490_ = v___x_2699_;
v___y_2491_ = v___y_2678_;
v___y_2492_ = v___y_2683_;
v___y_2493_ = v___x_2706_;
goto v___jp_2476_;
}
else
{
v___y_2598_ = v___y_2674_;
v___y_2599_ = v___y_2686_;
v___y_2600_ = v___f_2697_;
v___y_2601_ = v___y_2676_;
v___y_2602_ = v___y_2675_;
v___y_2603_ = v___y_2681_;
v___y_2604_ = v___x_2703_;
v___y_2605_ = v___y_2685_;
v___y_2606_ = v___y_2687_;
v___y_2607_ = v___y_2680_;
v___y_2608_ = v_ref_2691_;
v___y_2609_ = v___y_2682_;
v___y_2610_ = v___y_2684_;
v___y_2611_ = v_options_2689_;
v___y_2612_ = v___y_2677_;
v___y_2613_ = v___x_2694_;
v___y_2614_ = v___y_2679_;
v___y_2615_ = v___x_2699_;
v___y_2616_ = v___y_2678_;
v___y_2617_ = v___y_2683_;
goto v___jp_2597_;
}
}
else
{
v___y_2598_ = v___y_2674_;
v___y_2599_ = v___y_2686_;
v___y_2600_ = v___f_2697_;
v___y_2601_ = v___y_2676_;
v___y_2602_ = v___y_2675_;
v___y_2603_ = v___y_2681_;
v___y_2604_ = v___x_2703_;
v___y_2605_ = v___y_2685_;
v___y_2606_ = v___y_2687_;
v___y_2607_ = v___y_2680_;
v___y_2608_ = v_ref_2691_;
v___y_2609_ = v___y_2682_;
v___y_2610_ = v___y_2684_;
v___y_2611_ = v_options_2689_;
v___y_2612_ = v___y_2677_;
v___y_2613_ = v___x_2694_;
v___y_2614_ = v___y_2679_;
v___y_2615_ = v___x_2699_;
v___y_2616_ = v___y_2678_;
v___y_2617_ = v___y_2683_;
goto v___jp_2597_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticContext_2049_ = stack[0].m_obj;
lean_object* v___x_2050_ = stack[1].m_obj;
lean_object* v_aig_2051_ = stack[2].m_obj;
lean_object* v___x_2052_ = stack[3].m_obj;
lean_object* v___x_2053_ = stack[4].m_obj;
lean_object* v___x_2054_ = stack[5].m_obj;
uint8_t v_hasTrace_2055_ = stack[6].m_num;
lean_object* v___x_2056_ = stack[7].m_obj;
lean_object* v___f_2057_ = stack[8].m_obj;
lean_object* v___x_2058_ = stack[9].m_obj;
lean_object* v_cache_2059_ = stack[10].m_obj;
lean_object* v_ref_2060_ = stack[11].m_obj;
uint8_t v___x_2061_ = stack[12].m_num;
lean_object* v_cls_2062_ = stack[13].m_obj;
lean_object* v___f_2063_ = stack[14].m_obj;
lean_object* v_cnfCache_2064_ = stack[15].m_obj;
lean_object* v___x_2065_ = stack[16].m_obj;
lean_object* v_result_2066_ = stack[17].m_obj;
lean_object* v___x_2067_ = stack[18].m_obj;
lean_object* v___x_2068_ = stack[19].m_obj;
lean_object* v_____r_2069_ = stack[20].m_obj;
lean_object* v___y_2070_ = stack[21].m_obj;
lean_object* v___y_2071_ = stack[22].m_obj;
lean_object* v___y_2072_ = stack[23].m_obj;
lean_object* v___y_2073_ = stack[24].m_obj;
lean_object* v___y_2074_ = stack[25].m_obj;
lean_object* v___y_2075_ = stack[26].m_obj;
lean_object* v___y_2076_ = stack[27].m_obj;
lean_object* v___y_2077_ = stack[28].m_obj;
lean_object* v___y_2078_ = stack[29].m_obj;
lean_object* v___y_2079_ = stack[30].m_obj;
lean_object* v___y_2080_ = stack[31].m_obj;
lean_object* v___y_2081_ = stack[32].m_obj;
lean_object* v___y_2082_ = stack[33].m_obj;
lean_object* v___y_2083_ = stack[34].m_obj;
lean_object* v_res_2725_;
v_res_2725_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v_tacticContext_2049_, v___x_2050_, v_aig_2051_, v___x_2052_, v___x_2053_, v___x_2054_, v_hasTrace_2055_, v___x_2056_, v___f_2057_, v___x_2058_, v_cache_2059_, v_ref_2060_, v___x_2061_, v_cls_2062_, v___f_2063_, v_cnfCache_2064_, v___x_2065_, v_result_2066_, v___x_2067_, v___x_2068_, v_____r_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
stack->m_obj
 = v_res_2725_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___boxed(lean_object** _args){
lean_object* v_tacticContext_2726_ = _args[0];
lean_object* v___x_2727_ = _args[1];
lean_object* v_aig_2728_ = _args[2];
lean_object* v___x_2729_ = _args[3];
lean_object* v___x_2730_ = _args[4];
lean_object* v___x_2731_ = _args[5];
lean_object* v_hasTrace_2732_ = _args[6];
lean_object* v___x_2733_ = _args[7];
lean_object* v___f_2734_ = _args[8];
lean_object* v___x_2735_ = _args[9];
lean_object* v_cache_2736_ = _args[10];
lean_object* v_ref_2737_ = _args[11];
lean_object* v___x_2738_ = _args[12];
lean_object* v_cls_2739_ = _args[13];
lean_object* v___f_2740_ = _args[14];
lean_object* v_cnfCache_2741_ = _args[15];
lean_object* v___x_2742_ = _args[16];
lean_object* v_result_2743_ = _args[17];
lean_object* v___x_2744_ = _args[18];
lean_object* v___x_2745_ = _args[19];
lean_object* v_____r_2746_ = _args[20];
lean_object* v___y_2747_ = _args[21];
lean_object* v___y_2748_ = _args[22];
lean_object* v___y_2749_ = _args[23];
lean_object* v___y_2750_ = _args[24];
lean_object* v___y_2751_ = _args[25];
lean_object* v___y_2752_ = _args[26];
lean_object* v___y_2753_ = _args[27];
lean_object* v___y_2754_ = _args[28];
lean_object* v___y_2755_ = _args[29];
lean_object* v___y_2756_ = _args[30];
lean_object* v___y_2757_ = _args[31];
lean_object* v___y_2758_ = _args[32];
lean_object* v___y_2759_ = _args[33];
lean_object* v___y_2760_ = _args[34];
lean_object* v___y_2761_ = _args[35];
_start:
{
uint8_t v_hasTrace_boxed_2762_; uint8_t v___x_1193791__boxed_2763_; lean_object* v_res_2764_; 
v_hasTrace_boxed_2762_ = lean_unbox(v_hasTrace_2732_);
v___x_1193791__boxed_2763_ = lean_unbox(v___x_2738_);
v_res_2764_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v_tacticContext_2726_, v___x_2727_, v_aig_2728_, v___x_2729_, v___x_2730_, v___x_2731_, v_hasTrace_boxed_2762_, v___x_2733_, v___f_2734_, v___x_2735_, v_cache_2736_, v_ref_2737_, v___x_1193791__boxed_2763_, v_cls_2739_, v___f_2740_, v_cnfCache_2741_, v___x_2742_, v_result_2743_, v___x_2744_, v___x_2745_, v_____r_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v_ref_2737_);
lean_dec_ref(v___x_2735_);
lean_dec(v___x_2727_);
return v_res_2764_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(lean_object* v_tacticContext_2765_, lean_object* v___x_2766_, lean_object* v_aig_2767_, lean_object* v___x_2768_, lean_object* v___x_2769_, lean_object* v___x_2770_, uint8_t v___x_2771_, lean_object* v___x_2772_, lean_object* v___f_2773_, lean_object* v___x_2774_, lean_object* v_cache_2775_, lean_object* v_ref_2776_, lean_object* v_cls_2777_, lean_object* v___f_2778_, lean_object* v_cnfCache_2779_, lean_object* v___x_2780_, lean_object* v_result_2781_, lean_object* v___x_2782_, lean_object* v___x_2783_, lean_object* v_____r_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; uint8_t v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v_a_2978_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; uint8_t v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v_a_3010_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; uint8_t v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; uint8_t v___y_3095_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; uint8_t v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v_a_3271_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; uint8_t v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v_a_3304_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; uint8_t v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v_config_3423_; uint8_t v_graphviz_3424_; 
v_config_3423_ = lean_ctor_get(v_tacticContext_2765_, 5);
v_graphviz_3424_ = lean_ctor_get_uint8(v_config_3423_, sizeof(void*)*3 + 8);
if (v_graphviz_3424_ == 0)
{
v___y_3390_ = v___y_2785_;
v___y_3391_ = v___y_2786_;
v___y_3392_ = v___y_2787_;
v___y_3393_ = v___y_2788_;
v___y_3394_ = v___y_2789_;
v___y_3395_ = v___y_2790_;
v___y_3396_ = v___y_2791_;
v___y_3397_ = v___y_2792_;
v___y_3398_ = v___y_2793_;
v___y_3399_ = v___y_2794_;
v___y_3400_ = v___y_2795_;
v___y_3401_ = v___y_2796_;
v___y_3402_ = v___y_2797_;
v___y_3403_ = v___y_2798_;
goto v___jp_3389_;
}
else
{
lean_object* v_ref_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_ref_3425_ = lean_ctor_get(v___y_2797_, 2);
v___x_3426_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
lean_inc_ref(v_result_2781_);
v___x_3427_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v_result_2781_);
v___x_3428_ = l_IO_FS_writeFile(v___x_3426_, v___x_3427_);
lean_dec_ref(v___x_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_dec_ref_known(v___x_3428_, 1);
v___y_3390_ = v___y_2785_;
v___y_3391_ = v___y_2786_;
v___y_3392_ = v___y_2787_;
v___y_3393_ = v___y_2788_;
v___y_3394_ = v___y_2789_;
v___y_3395_ = v___y_2790_;
v___y_3396_ = v___y_2791_;
v___y_3397_ = v___y_2792_;
v___y_3398_ = v___y_2793_;
v___y_3399_ = v___y_2794_;
v___y_3400_ = v___y_2795_;
v___y_3401_ = v___y_2796_;
v___y_3402_ = v___y_2797_;
v___y_3403_ = v___y_2798_;
goto v___jp_3389_;
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3440_; 
lean_dec_ref(v___x_2783_);
lean_dec_ref(v___x_2782_);
lean_dec_ref(v_result_2781_);
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_cnfCache_2779_);
lean_dec_ref(v___f_2778_);
lean_dec(v_cls_2777_);
lean_dec_ref(v_cache_2775_);
lean_dec_ref(v___f_2773_);
lean_dec_ref(v___x_2772_);
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_aig_2767_);
lean_dec_ref(v_tacticContext_2765_);
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3440_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3440_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3433_ = lean_io_error_to_string(v_a_3429_);
v___x_3434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
v___x_3435_ = l_Lean_MessageData_ofFormat(v___x_3434_);
lean_inc(v_ref_3425_);
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_ref_3425_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3436_);
v___x_3438_ = v___x_3431_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
v___jp_2800_:
{
lean_object* v___x_2815_; 
v___x_2815_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___x_2766_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2805_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2827_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2827_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2827_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2822_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2767_, v_a_2816_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec(v_a_2816_);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2823_);
v___x_2825_ = v___x_2820_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_a_2816_);
lean_dec_ref(v_aig_2767_);
v_a_2828_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2817_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2817_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref(v_aig_2767_);
v_a_2836_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2815_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2815_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
v___jp_2844_:
{
if (lean_obj_tag(v___y_2860_) == 0)
{
lean_object* v_a_2861_; uint8_t v___x_2862_; 
v_a_2861_ = lean_ctor_get(v___y_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___y_2860_, 1);
v___x_2862_ = lean_unbox(v_a_2861_);
lean_dec(v_a_2861_);
switch(v___x_2862_)
{
case 0:
{
lean_object* v_toCold_2863_; lean_object* v_options_2864_; uint8_t v_hasTrace_2865_; 
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_tacticContext_2765_);
v_toCold_2863_ = lean_ctor_get(v___y_2855_, 0);
v_options_2864_ = lean_ctor_get(v_toCold_2863_, 2);
v_hasTrace_2865_ = lean_ctor_get_uint8(v_options_2864_, sizeof(void*)*1);
if (v_hasTrace_2865_ == 0)
{
lean_dec(v___y_2852_);
v___y_2801_ = v___y_2854_;
v___y_2802_ = v___y_2847_;
v___y_2803_ = v___y_2845_;
v___y_2804_ = v___y_2856_;
v___y_2805_ = v___y_2850_;
v___y_2806_ = v___y_2846_;
v___y_2807_ = v___y_2858_;
v___y_2808_ = v___y_2859_;
v___y_2809_ = v___y_2851_;
v___y_2810_ = v___y_2848_;
v___y_2811_ = v___y_2857_;
v___y_2812_ = v___y_2849_;
v___y_2813_ = v___y_2855_;
v___y_2814_ = v___y_2853_;
goto v___jp_2800_;
}
else
{
lean_object* v_inheritedTraceOptions_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v_inheritedTraceOptions_2866_ = lean_ctor_get(v_toCold_2863_, 11);
v___x_2867_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_2852_);
v___x_2868_ = l_Lean_Name_append(v___x_2867_, v___y_2852_);
v___x_2869_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2866_, v_options_2864_, v___x_2868_);
lean_dec(v___x_2868_);
if (v___x_2869_ == 0)
{
lean_dec(v___y_2852_);
v___y_2801_ = v___y_2854_;
v___y_2802_ = v___y_2847_;
v___y_2803_ = v___y_2845_;
v___y_2804_ = v___y_2856_;
v___y_2805_ = v___y_2850_;
v___y_2806_ = v___y_2846_;
v___y_2807_ = v___y_2858_;
v___y_2808_ = v___y_2859_;
v___y_2809_ = v___y_2851_;
v___y_2810_ = v___y_2848_;
v___y_2811_ = v___y_2857_;
v___y_2812_ = v___y_2849_;
v___y_2813_ = v___y_2855_;
v___y_2814_ = v___y_2853_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
v___x_2871_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_2852_, v___x_2870_, v___y_2857_, v___y_2849_, v___y_2855_, v___y_2853_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_dec_ref_known(v___x_2871_, 1);
v___y_2801_ = v___y_2854_;
v___y_2802_ = v___y_2847_;
v___y_2803_ = v___y_2845_;
v___y_2804_ = v___y_2856_;
v___y_2805_ = v___y_2850_;
v___y_2806_ = v___y_2846_;
v___y_2807_ = v___y_2858_;
v___y_2808_ = v___y_2859_;
v___y_2809_ = v___y_2851_;
v___y_2810_ = v___y_2848_;
v___y_2811_ = v___y_2857_;
v___y_2812_ = v___y_2849_;
v___y_2813_ = v___y_2855_;
v___y_2814_ = v___y_2853_;
goto v___jp_2800_;
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec_ref(v_aig_2767_);
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_2880_; lean_object* v_satExpr_2881_; lean_object* v_hypQueue_2882_; lean_object* v_usedHyps_2883_; uint8_t v_didChange_2884_; lean_object* v_theoryState_2885_; lean_object* v_solverTimeBudgetMs_2886_; lean_object* v_roundBudget_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v___y_2852_);
lean_dec_ref(v_aig_2767_);
v___x_2880_ = lean_st_ref_take(v___y_2847_);
v_satExpr_2881_ = lean_ctor_get(v___x_2880_, 0);
v_hypQueue_2882_ = lean_ctor_get(v___x_2880_, 1);
v_usedHyps_2883_ = lean_ctor_get(v___x_2880_, 2);
v_didChange_2884_ = lean_ctor_get_uint8(v___x_2880_, sizeof(void*)*6);
v_theoryState_2885_ = lean_ctor_get(v___x_2880_, 3);
v_solverTimeBudgetMs_2886_ = lean_ctor_get(v___x_2880_, 4);
v_roundBudget_2887_ = lean_ctor_get(v___x_2880_, 5);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2889_ = v___x_2880_;
v_isShared_2890_ = v_isSharedCheck_2948_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_roundBudget_2887_);
lean_inc(v_solverTimeBudgetMs_2886_);
lean_inc(v_theoryState_2885_);
lean_inc(v_usedHyps_2883_);
lean_inc(v_hypQueue_2882_);
lean_inc(v_satExpr_2881_);
lean_dec(v___x_2880_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2948_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v_satSolver_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2944_; 
v___x_2891_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_2892_ = lean_ctor_get(v_theoryState_2885_, 3);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_theoryState_2885_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; lean_object* v_unused_2946_; lean_object* v_unused_2947_; 
v_unused_2945_ = lean_ctor_get(v_theoryState_2885_, 2);
lean_dec(v_unused_2945_);
v_unused_2946_ = lean_ctor_get(v_theoryState_2885_, 1);
lean_dec(v_unused_2946_);
v_unused_2947_ = lean_ctor_get(v_theoryState_2885_, 0);
lean_dec(v_unused_2947_);
v___x_2894_ = v_theoryState_2885_;
v_isShared_2895_ = v_isSharedCheck_2944_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_satSolver_2892_);
lean_dec(v_theoryState_2885_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2944_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_mk_array(v___x_2768_, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2769_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 2, v___x_2891_);
lean_ctor_set(v___x_2894_, 1, v___x_2770_);
lean_ctor_set(v___x_2894_, 0, v___x_2898_);
v___x_2900_ = v___x_2894_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_satSolver_2892_);
v___x_2900_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2902_; 
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 3, v___x_2900_);
v___x_2902_ = v___x_2889_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_satExpr_2881_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_hypQueue_2882_);
lean_ctor_set(v_reuseFailAlloc_2942_, 2, v_usedHyps_2883_);
lean_ctor_set(v_reuseFailAlloc_2942_, 3, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2942_, 4, v_solverTimeBudgetMs_2886_);
lean_ctor_set(v_reuseFailAlloc_2942_, 5, v_roundBudget_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2942_, sizeof(void*)*6, v_didChange_2884_);
v___x_2902_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_st_ref_put(v___y_2847_, v___x_2902_);
v___x_2904_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_2854_, v___y_2847_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v_goal_2906_; lean_object* v___x_2907_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v_goal_2906_ = lean_ctor_get(v___y_2854_, 0);
lean_inc(v_goal_2906_);
v___x_2907_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_tacticContext_2765_, v_goal_2906_, v_a_2905_, v___y_2845_, v___y_2856_, v___y_2850_, v___y_2846_, v___y_2858_, v___y_2859_, v___y_2851_, v___y_2848_, v___y_2857_, v___y_2849_, v___y_2855_, v___y_2853_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2925_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2925_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2925_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
if (lean_obj_tag(v_a_2908_) == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec_ref_known(v_a_2908_, 1);
lean_del_object(v___x_2910_);
v___x_2912_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_2913_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_2912_, v___y_2857_, v___y_2849_, v___y_2855_, v___y_2853_);
return v___x_2913_;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2924_; 
v_a_2914_ = lean_ctor_get(v_a_2908_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_a_2908_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2916_ = v_a_2908_;
v_isShared_2917_ = v_isSharedCheck_2924_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v_a_2908_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2924_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2921_; 
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2919_);
v___x_2921_ = v___x_2910_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
v_a_2926_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2907_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2907_);
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
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v_tacticContext_2765_);
v_a_2934_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2904_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2904_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
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
lean_object* v___x_2949_; 
lean_dec(v___y_2852_);
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_aig_2767_);
lean_dec_ref(v_tacticContext_2765_);
v___x_2949_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_2855_, v___y_2853_);
return v___x_2949_;
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v___y_2852_);
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_aig_2767_);
lean_dec_ref(v_tacticContext_2765_);
v_a_2950_ = lean_ctor_get(v___y_2860_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___y_2860_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___y_2860_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___y_2860_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
v___jp_2958_:
{
lean_object* v___x_2979_; double v___x_2980_; double v___x_2981_; double v___x_2982_; double v___x_2983_; double v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2979_ = lean_io_mono_nanos_now();
v___x_2980_ = lean_float_of_nat(v___y_2959_);
v___x_2981_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_2982_ = lean_float_div(v___x_2980_, v___x_2981_);
v___x_2983_ = lean_float_of_nat(v___x_2979_);
v___x_2984_ = lean_float_div(v___x_2983_, v___x_2981_);
v___x_2985_ = lean_box_float(v___x_2982_);
v___x_2986_ = lean_box_float(v___x_2984_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_a_2978_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
lean_inc(v___y_2970_);
v___x_2989_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_2970_, v___x_2771_, v___x_2772_, v___y_2960_, v___y_2963_, v___y_2965_, v___f_2773_, v___x_2988_, v___y_2972_, v___y_2964_, v___y_2961_, v___y_2975_, v___y_2968_, v___y_2962_, v___y_2976_, v___y_2977_, v___y_2969_, v___y_2966_, v___y_2974_, v___y_2967_, v___y_2973_, v___y_2971_);
v___y_2845_ = v___y_2961_;
v___y_2846_ = v___y_2962_;
v___y_2847_ = v___y_2964_;
v___y_2848_ = v___y_2966_;
v___y_2849_ = v___y_2967_;
v___y_2850_ = v___y_2968_;
v___y_2851_ = v___y_2969_;
v___y_2852_ = v___y_2970_;
v___y_2853_ = v___y_2971_;
v___y_2854_ = v___y_2972_;
v___y_2855_ = v___y_2973_;
v___y_2856_ = v___y_2975_;
v___y_2857_ = v___y_2974_;
v___y_2858_ = v___y_2976_;
v___y_2859_ = v___y_2977_;
v___y_2860_ = v___x_2989_;
goto v___jp_2844_;
}
v___jp_2990_:
{
lean_object* v___x_3011_; double v___x_3012_; double v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3011_ = lean_io_get_num_heartbeats();
v___x_3012_ = lean_float_of_nat(v___y_3006_);
v___x_3013_ = lean_float_of_nat(v___x_3011_);
v___x_3014_ = lean_box_float(v___x_3012_);
v___x_3015_ = lean_box_float(v___x_3013_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v_a_3010_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
lean_inc(v___y_3001_);
v___x_3018_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_3001_, v___x_2771_, v___x_2772_, v___y_2991_, v___y_2994_, v___y_2996_, v___f_2773_, v___x_3017_, v___y_3003_, v___y_2995_, v___y_2992_, v___y_3007_, v___y_2999_, v___y_2993_, v___y_3008_, v___y_3009_, v___y_3000_, v___y_2997_, v___y_3005_, v___y_2998_, v___y_3004_, v___y_3002_);
v___y_2845_ = v___y_2992_;
v___y_2846_ = v___y_2993_;
v___y_2847_ = v___y_2995_;
v___y_2848_ = v___y_2997_;
v___y_2849_ = v___y_2998_;
v___y_2850_ = v___y_2999_;
v___y_2851_ = v___y_3000_;
v___y_2852_ = v___y_3001_;
v___y_2853_ = v___y_3002_;
v___y_2854_ = v___y_3003_;
v___y_2855_ = v___y_3004_;
v___y_2856_ = v___y_3007_;
v___y_2857_ = v___y_3005_;
v___y_2858_ = v___y_3008_;
v___y_2859_ = v___y_3009_;
v___y_2860_ = v___x_3018_;
goto v___jp_2844_;
}
v___jp_3019_:
{
lean_object* v___x_3038_; lean_object* v_a_3039_; uint8_t v___x_3040_; 
v___x_3038_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_3031_);
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref(v___x_3038_);
v___x_3040_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_3021_, v___x_2774_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_io_mono_nanos_now();
v___x_3042_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_3020_, v___y_3032_, v___y_3025_, v___y_3022_, v___y_3033_, v___y_3028_, v___y_3023_, v___y_3036_, v___y_3037_, v___y_3029_, v___y_3026_, v___y_3034_, v___y_3027_, v___y_3035_, v___y_3031_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 1);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v___y_2959_ = v___x_3041_;
v___y_2960_ = v___y_3021_;
v___y_2961_ = v___y_3022_;
v___y_2962_ = v___y_3023_;
v___y_2963_ = v___y_3024_;
v___y_2964_ = v___y_3025_;
v___y_2965_ = v_a_3039_;
v___y_2966_ = v___y_3026_;
v___y_2967_ = v___y_3027_;
v___y_2968_ = v___y_3028_;
v___y_2969_ = v___y_3029_;
v___y_2970_ = v___y_3030_;
v___y_2971_ = v___y_3031_;
v___y_2972_ = v___y_3032_;
v___y_2973_ = v___y_3035_;
v___y_2974_ = v___y_3034_;
v___y_2975_ = v___y_3033_;
v___y_2976_ = v___y_3036_;
v___y_2977_ = v___y_3037_;
v_a_2978_ = v___x_3048_;
goto v___jp_2958_;
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3042_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3042_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 0);
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
v___y_2959_ = v___x_3041_;
v___y_2960_ = v___y_3021_;
v___y_2961_ = v___y_3022_;
v___y_2962_ = v___y_3023_;
v___y_2963_ = v___y_3024_;
v___y_2964_ = v___y_3025_;
v___y_2965_ = v_a_3039_;
v___y_2966_ = v___y_3026_;
v___y_2967_ = v___y_3027_;
v___y_2968_ = v___y_3028_;
v___y_2969_ = v___y_3029_;
v___y_2970_ = v___y_3030_;
v___y_2971_ = v___y_3031_;
v___y_2972_ = v___y_3032_;
v___y_2973_ = v___y_3035_;
v___y_2974_ = v___y_3034_;
v___y_2975_ = v___y_3033_;
v___y_2976_ = v___y_3036_;
v___y_2977_ = v___y_3037_;
v_a_2978_ = v___x_3056_;
goto v___jp_2958_;
}
}
}
}
else
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_io_get_num_heartbeats();
v___x_3060_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_3020_, v___y_3032_, v___y_3025_, v___y_3022_, v___y_3033_, v___y_3028_, v___y_3023_, v___y_3036_, v___y_3037_, v___y_3029_, v___y_3026_, v___y_3034_, v___y_3027_, v___y_3035_, v___y_3031_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 1);
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
v___y_2991_ = v___y_3021_;
v___y_2992_ = v___y_3022_;
v___y_2993_ = v___y_3023_;
v___y_2994_ = v___y_3024_;
v___y_2995_ = v___y_3025_;
v___y_2996_ = v_a_3039_;
v___y_2997_ = v___y_3026_;
v___y_2998_ = v___y_3027_;
v___y_2999_ = v___y_3028_;
v___y_3000_ = v___y_3029_;
v___y_3001_ = v___y_3030_;
v___y_3002_ = v___y_3031_;
v___y_3003_ = v___y_3032_;
v___y_3004_ = v___y_3035_;
v___y_3005_ = v___y_3034_;
v___y_3006_ = v___x_3059_;
v___y_3007_ = v___y_3033_;
v___y_3008_ = v___y_3036_;
v___y_3009_ = v___y_3037_;
v_a_3010_ = v___x_3066_;
goto v___jp_2990_;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
v_a_3069_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3060_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3060_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 0);
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
v___y_2991_ = v___y_3021_;
v___y_2992_ = v___y_3022_;
v___y_2993_ = v___y_3023_;
v___y_2994_ = v___y_3024_;
v___y_2995_ = v___y_3025_;
v___y_2996_ = v_a_3039_;
v___y_2997_ = v___y_3026_;
v___y_2998_ = v___y_3027_;
v___y_2999_ = v___y_3028_;
v___y_3000_ = v___y_3029_;
v___y_3001_ = v___y_3030_;
v___y_3002_ = v___y_3031_;
v___y_3003_ = v___y_3032_;
v___y_3004_ = v___y_3035_;
v___y_3005_ = v___y_3034_;
v___y_3006_ = v___x_3059_;
v___y_3007_ = v___y_3033_;
v___y_3008_ = v___y_3036_;
v___y_3009_ = v___y_3037_;
v_a_3010_ = v___x_3074_;
goto v___jp_2990_;
}
}
}
}
}
v___jp_3077_:
{
lean_object* v_toCold_3096_; lean_object* v_ref_3097_; lean_object* v___x_3098_; 
v_toCold_3096_ = lean_ctor_get(v___y_3091_, 0);
v_ref_3097_ = lean_ctor_get(v___y_3091_, 2);
lean_inc_ref(v___y_3078_);
v___x_3098_ = l_Lean_Cadical_Solver_assume(v___y_3078_, v___y_3081_, v___y_3095_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_options_3099_; uint8_t v_hasTrace_3100_; 
lean_dec_ref_known(v___x_3098_, 1);
v_options_3099_ = lean_ctor_get(v_toCold_3096_, 2);
v_hasTrace_3100_ = lean_ctor_get_uint8(v_options_3099_, sizeof(void*)*1);
if (v_hasTrace_3100_ == 0)
{
lean_object* v___x_3101_; 
lean_dec_ref(v___f_2773_);
lean_dec_ref(v___x_2772_);
v___x_3101_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_3078_, v___y_3089_, v___y_3082_, v___y_3079_, v___y_3092_, v___y_3085_, v___y_3080_, v___y_3093_, v___y_3094_, v___y_3086_, v___y_3083_, v___y_3090_, v___y_3084_, v___y_3091_, v___y_3088_);
v___y_2845_ = v___y_3079_;
v___y_2846_ = v___y_3080_;
v___y_2847_ = v___y_3082_;
v___y_2848_ = v___y_3083_;
v___y_2849_ = v___y_3084_;
v___y_2850_ = v___y_3085_;
v___y_2851_ = v___y_3086_;
v___y_2852_ = v___y_3087_;
v___y_2853_ = v___y_3088_;
v___y_2854_ = v___y_3089_;
v___y_2855_ = v___y_3091_;
v___y_2856_ = v___y_3092_;
v___y_2857_ = v___y_3090_;
v___y_2858_ = v___y_3093_;
v___y_2859_ = v___y_3094_;
v___y_2860_ = v___x_3101_;
goto v___jp_2844_;
}
else
{
lean_object* v_inheritedTraceOptions_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v_inheritedTraceOptions_3102_ = lean_ctor_get(v_toCold_3096_, 11);
v___x_3103_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_3087_);
v___x_3104_ = l_Lean_Name_append(v___x_3103_, v___y_3087_);
v___x_3105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3102_, v_options_3099_, v___x_3104_);
lean_dec(v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = l_Lean_trace_profiler;
v___x_3107_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3099_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_dec_ref(v___f_2773_);
lean_dec_ref(v___x_2772_);
v___x_3108_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_3078_, v___y_3089_, v___y_3082_, v___y_3079_, v___y_3092_, v___y_3085_, v___y_3080_, v___y_3093_, v___y_3094_, v___y_3086_, v___y_3083_, v___y_3090_, v___y_3084_, v___y_3091_, v___y_3088_);
v___y_2845_ = v___y_3079_;
v___y_2846_ = v___y_3080_;
v___y_2847_ = v___y_3082_;
v___y_2848_ = v___y_3083_;
v___y_2849_ = v___y_3084_;
v___y_2850_ = v___y_3085_;
v___y_2851_ = v___y_3086_;
v___y_2852_ = v___y_3087_;
v___y_2853_ = v___y_3088_;
v___y_2854_ = v___y_3089_;
v___y_2855_ = v___y_3091_;
v___y_2856_ = v___y_3092_;
v___y_2857_ = v___y_3090_;
v___y_2858_ = v___y_3093_;
v___y_2859_ = v___y_3094_;
v___y_2860_ = v___x_3108_;
goto v___jp_2844_;
}
else
{
v___y_3020_ = v___y_3078_;
v___y_3021_ = v_options_3099_;
v___y_3022_ = v___y_3079_;
v___y_3023_ = v___y_3080_;
v___y_3024_ = v___x_3105_;
v___y_3025_ = v___y_3082_;
v___y_3026_ = v___y_3083_;
v___y_3027_ = v___y_3084_;
v___y_3028_ = v___y_3085_;
v___y_3029_ = v___y_3086_;
v___y_3030_ = v___y_3087_;
v___y_3031_ = v___y_3088_;
v___y_3032_ = v___y_3089_;
v___y_3033_ = v___y_3092_;
v___y_3034_ = v___y_3090_;
v___y_3035_ = v___y_3091_;
v___y_3036_ = v___y_3093_;
v___y_3037_ = v___y_3094_;
goto v___jp_3019_;
}
}
else
{
v___y_3020_ = v___y_3078_;
v___y_3021_ = v_options_3099_;
v___y_3022_ = v___y_3079_;
v___y_3023_ = v___y_3080_;
v___y_3024_ = v___x_3105_;
v___y_3025_ = v___y_3082_;
v___y_3026_ = v___y_3083_;
v___y_3027_ = v___y_3084_;
v___y_3028_ = v___y_3085_;
v___y_3029_ = v___y_3086_;
v___y_3030_ = v___y_3087_;
v___y_3031_ = v___y_3088_;
v___y_3032_ = v___y_3089_;
v___y_3033_ = v___y_3092_;
v___y_3034_ = v___y_3090_;
v___y_3035_ = v___y_3091_;
v___y_3036_ = v___y_3093_;
v___y_3037_ = v___y_3094_;
goto v___jp_3019_;
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3078_);
lean_dec_ref(v___f_2773_);
lean_dec_ref(v___x_2772_);
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_aig_2767_);
lean_dec_ref(v_tacticContext_2765_);
v_a_3109_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3111_ = v___x_3098_;
v_isShared_3112_ = v_isSharedCheck_3120_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3098_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3120_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3113_ = lean_io_error_to_string(v_a_3109_);
v___x_3114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
v___x_3115_ = l_Lean_MessageData_ofFormat(v___x_3114_);
lean_inc(v_ref_3097_);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v_ref_3097_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3116_);
v___x_3118_ = v___x_3111_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
v___jp_3121_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v_theoryState_3142_; lean_object* v_satExpr_3143_; lean_object* v_hypQueue_3144_; lean_object* v_usedHyps_3145_; uint8_t v_didChange_3146_; lean_object* v_solverTimeBudgetMs_3147_; lean_object* v_roundBudget_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3191_; 
lean_inc_ref(v_aig_2767_);
v___x_3140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3140_, 0, v_aig_2767_);
lean_ctor_set(v___x_3140_, 1, v_cache_2775_);
lean_ctor_set(v___x_3140_, 2, v___y_3123_);
v___x_3141_ = lean_st_ref_take(v___y_3127_);
v_theoryState_3142_ = lean_ctor_get(v___x_3141_, 3);
v_satExpr_3143_ = lean_ctor_get(v___x_3141_, 0);
v_hypQueue_3144_ = lean_ctor_get(v___x_3141_, 1);
v_usedHyps_3145_ = lean_ctor_get(v___x_3141_, 2);
v_didChange_3146_ = lean_ctor_get_uint8(v___x_3141_, sizeof(void*)*6);
v_solverTimeBudgetMs_3147_ = lean_ctor_get(v___x_3141_, 4);
v_roundBudget_3148_ = lean_ctor_get(v___x_3141_, 5);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3150_ = v___x_3141_;
v_isShared_3151_ = v_isSharedCheck_3191_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_roundBudget_3148_);
lean_inc(v_solverTimeBudgetMs_3147_);
lean_inc(v_theoryState_3142_);
lean_inc(v_usedHyps_3145_);
lean_inc(v_hypQueue_3144_);
lean_inc(v_satExpr_3143_);
lean_dec(v___x_3141_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3191_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v_funState_3152_; lean_object* v_preprocessCaches_3153_; lean_object* v_satSolver_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3189_; 
v_funState_3152_ = lean_ctor_get(v_theoryState_3142_, 0);
v_preprocessCaches_3153_ = lean_ctor_get(v_theoryState_3142_, 2);
v_satSolver_3154_ = lean_ctor_get(v_theoryState_3142_, 3);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_theoryState_3142_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v_theoryState_3142_, 1);
lean_dec(v_unused_3190_);
v___x_3156_ = v_theoryState_3142_;
v_isShared_3157_ = v_isSharedCheck_3189_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_satSolver_3154_);
lean_inc(v_preprocessCaches_3153_);
lean_inc(v_funState_3152_);
lean_dec(v_theoryState_3142_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3189_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v___x_3140_);
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_funState_3152_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_preprocessCaches_3153_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_satSolver_3154_);
v___x_3159_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3161_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 3, v___x_3159_);
v___x_3161_ = v___x_3150_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_satExpr_3143_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_hypQueue_3144_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_usedHyps_3145_);
lean_ctor_set(v_reuseFailAlloc_3187_, 3, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3187_, 4, v_solverTimeBudgetMs_3147_);
lean_ctor_set(v_reuseFailAlloc_3187_, 5, v_roundBudget_3148_);
lean_ctor_set_uint8(v_reuseFailAlloc_3187_, sizeof(void*)*6, v_didChange_3146_);
v___x_3161_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_st_ref_put(v___y_3127_, v___x_3161_);
v___x_3163_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_3125_, v___y_3122_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v___x_3164_; 
lean_dec_ref_known(v___x_3163_, 1);
v___x_3164_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_3127_);
if (lean_obj_tag(v___x_3164_) == 0)
{
uint8_t v_invert_3165_; 
v_invert_3165_ = lean_ctor_get_uint8(v_ref_2776_, sizeof(void*)*1);
if (v_invert_3165_ == 0)
{
lean_object* v_a_3166_; lean_object* v_gate_3167_; 
v_a_3166_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3164_, 1);
v_gate_3167_ = lean_ctor_get(v_ref_2776_, 0);
v___y_3078_ = v_a_3166_;
v___y_3079_ = v___y_3128_;
v___y_3080_ = v___y_3131_;
v___y_3081_ = v_gate_3167_;
v___y_3082_ = v___y_3127_;
v___y_3083_ = v___y_3135_;
v___y_3084_ = v___y_3137_;
v___y_3085_ = v___y_3130_;
v___y_3086_ = v___y_3134_;
v___y_3087_ = v___y_3124_;
v___y_3088_ = v___y_3139_;
v___y_3089_ = v___y_3126_;
v___y_3090_ = v___y_3136_;
v___y_3091_ = v___y_3138_;
v___y_3092_ = v___y_3129_;
v___y_3093_ = v___y_3132_;
v___y_3094_ = v___y_3133_;
v___y_3095_ = v___x_2771_;
goto v___jp_3077_;
}
else
{
lean_object* v_a_3168_; lean_object* v_gate_3169_; uint8_t v___x_3170_; 
v_a_3168_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3164_, 1);
v_gate_3169_ = lean_ctor_get(v_ref_2776_, 0);
v___x_3170_ = 0;
v___y_3078_ = v_a_3168_;
v___y_3079_ = v___y_3128_;
v___y_3080_ = v___y_3131_;
v___y_3081_ = v_gate_3169_;
v___y_3082_ = v___y_3127_;
v___y_3083_ = v___y_3135_;
v___y_3084_ = v___y_3137_;
v___y_3085_ = v___y_3130_;
v___y_3086_ = v___y_3134_;
v___y_3087_ = v___y_3124_;
v___y_3088_ = v___y_3139_;
v___y_3089_ = v___y_3126_;
v___y_3090_ = v___y_3136_;
v___y_3091_ = v___y_3138_;
v___y_3092_ = v___y_3129_;
v___y_3093_ = v___y_3132_;
v___y_3094_ = v___y_3133_;
v___y_3095_ = v___x_3170_;
goto v___jp_3077_;
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v___y_3124_);
lean_dec_ref(v___f_2773_);
lean_dec_ref(v___x_2772_);
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_aig_2767_);
lean_dec_ref(v_tacticContext_2765_);
v_a_3171_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3164_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3164_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v___y_3124_);
lean_dec_ref(v___f_2773_);
lean_dec_ref(v___x_2772_);
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_aig_2767_);
lean_dec_ref(v_tacticContext_2765_);
v_a_3179_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3163_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3163_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
}
}
}
v___jp_3192_:
{
if (lean_obj_tag(v___y_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v_toCold_3211_; lean_object* v_options_3212_; uint8_t v_hasTrace_3213_; 
v_a_3210_ = lean_ctor_get(v___y_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___y_3209_, 1);
v_toCold_3211_ = lean_ctor_get(v___y_3207_, 0);
v_options_3212_ = lean_ctor_get(v_toCold_3211_, 2);
v_hasTrace_3213_ = lean_ctor_get_uint8(v_options_3212_, sizeof(void*)*1);
if (v_hasTrace_3213_ == 0)
{
lean_object* v_cnf_3214_; 
lean_dec(v_cls_2777_);
v_cnf_3214_ = lean_ctor_get(v_a_3210_, 0);
lean_inc_ref(v_cnf_3214_);
v___y_3122_ = v_cnf_3214_;
v___y_3123_ = v_a_3210_;
v___y_3124_ = v___y_3204_;
v___y_3125_ = v___y_3198_;
v___y_3126_ = v___y_3202_;
v___y_3127_ = v___y_3208_;
v___y_3128_ = v___y_3205_;
v___y_3129_ = v___y_3203_;
v___y_3130_ = v___y_3193_;
v___y_3131_ = v___y_3199_;
v___y_3132_ = v___y_3197_;
v___y_3133_ = v___y_3200_;
v___y_3134_ = v___y_3206_;
v___y_3135_ = v___y_3201_;
v___y_3136_ = v___y_3196_;
v___y_3137_ = v___y_3195_;
v___y_3138_ = v___y_3207_;
v___y_3139_ = v___y_3194_;
goto v___jp_3121_;
}
else
{
lean_object* v_cnf_3215_; lean_object* v_inheritedTraceOptions_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v_cnf_3215_ = lean_ctor_get(v_a_3210_, 0);
lean_inc_ref(v_cnf_3215_);
v_inheritedTraceOptions_3216_ = lean_ctor_get(v_toCold_3211_, 11);
v___x_3217_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v_cls_2777_);
v___x_3218_ = l_Lean_Name_append(v___x_3217_, v_cls_2777_);
v___x_3219_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3216_, v_options_3212_, v___x_3218_);
lean_dec(v___x_3218_);
if (v___x_3219_ == 0)
{
lean_dec(v_cls_2777_);
v___y_3122_ = v_cnf_3215_;
v___y_3123_ = v_a_3210_;
v___y_3124_ = v___y_3204_;
v___y_3125_ = v___y_3198_;
v___y_3126_ = v___y_3202_;
v___y_3127_ = v___y_3208_;
v___y_3128_ = v___y_3205_;
v___y_3129_ = v___y_3203_;
v___y_3130_ = v___y_3193_;
v___y_3131_ = v___y_3199_;
v___y_3132_ = v___y_3197_;
v___y_3133_ = v___y_3200_;
v___y_3134_ = v___y_3206_;
v___y_3135_ = v___y_3201_;
v___y_3136_ = v___y_3196_;
v___y_3137_ = v___y_3195_;
v___y_3138_ = v___y_3207_;
v___y_3139_ = v___y_3194_;
goto v___jp_3121_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3220_ = lean_array_get_size(v_cnf_3215_);
v___x_3221_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_3222_ = l_Nat_reprFast(v___x_3220_);
v___x_3223_ = lean_string_append(v___x_3221_, v___x_3222_);
lean_dec_ref(v___x_3222_);
v___x_3224_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_3225_ = lean_string_append(v___x_3223_, v___x_3224_);
v___x_3226_ = lean_nat_sub(v___x_3220_, v___y_3198_);
v___x_3227_ = l_Nat_reprFast(v___x_3226_);
v___x_3228_ = lean_string_append(v___x_3225_, v___x_3227_);
lean_dec_ref(v___x_3227_);
v___x_3229_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_3230_ = lean_string_append(v___x_3228_, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
v___x_3232_ = l_Lean_MessageData_ofFormat(v___x_3231_);
v___x_3233_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_2777_, v___x_3232_, v___y_3196_, v___y_3195_, v___y_3207_, v___y_3194_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_dec_ref_known(v___x_3233_, 1);
v___y_3122_ = v_cnf_3215_;
v___y_3123_ = v_a_3210_;
v___y_3124_ = v___y_3204_;
v___y_3125_ = v___y_3198_;
v___y_3126_ = v___y_3202_;
v___y_3127_ = v___y_3208_;
v___y_3128_ = v___y_3205_;
v___y_3129_ = v___y_3203_;
v___y_3130_ = v___y_3193_;
v___y_3131_ = v___y_3199_;
v___y_3132_ = v___y_3197_;
v___y_3133_ = v___y_3200_;
v___y_3134_ = v___y_3206_;
v___y_3135_ = v___y_3201_;
v___y_3136_ = v___y_3196_;
v___y_3137_ = v___y_3195_;
v___y_3138_ = v___y_3207_;
v___y_3139_ = v___y_3194_;
goto v___jp_3121_;
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_cnf_3215_);
lean_dec(v_a_3210_);
lean_dec(v___y_3204_);
lean_dec(v___y_3198_);
lean_dec_ref(v_cache_2775_);
lean_dec_ref(v___f_2773_);
lean_dec_ref(v___x_2772_);
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_aig_2767_);
lean_dec_ref(v_tacticContext_2765_);
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v___y_3204_);
lean_dec(v___y_3198_);
lean_dec(v_cls_2777_);
lean_dec_ref(v_cache_2775_);
lean_dec_ref(v___f_2773_);
lean_dec_ref(v___x_2772_);
lean_dec_ref(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec_ref(v_aig_2767_);
lean_dec_ref(v_tacticContext_2765_);
v_a_3242_ = lean_ctor_get(v___y_3209_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___y_3209_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___y_3209_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___y_3209_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
v___jp_3250_:
{
lean_object* v___x_3272_; double v___x_3273_; double v___x_3274_; double v___x_3275_; double v___x_3276_; double v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3272_ = lean_io_mono_nanos_now();
v___x_3273_ = lean_float_of_nat(v___y_3255_);
v___x_3274_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_3275_ = lean_float_div(v___x_3273_, v___x_3274_);
v___x_3276_ = lean_float_of_nat(v___x_3272_);
v___x_3277_ = lean_float_div(v___x_3276_, v___x_3274_);
v___x_3278_ = lean_box_float(v___x_3275_);
v___x_3279_ = lean_box_float(v___x_3277_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v_a_3271_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
lean_inc_ref(v___x_2772_);
lean_inc(v___y_3266_);
v___x_3282_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_3266_, v___x_2771_, v___x_2772_, v___y_3254_, v___y_3259_, v___y_3252_, v___f_2778_, v___x_3281_, v___y_3264_, v___y_3270_, v___y_3267_, v___y_3265_, v___y_3251_, v___y_3261_, v___y_3258_, v___y_3262_, v___y_3268_, v___y_3263_, v___y_3257_, v___y_3256_, v___y_3269_, v___y_3253_);
v___y_3193_ = v___y_3251_;
v___y_3194_ = v___y_3253_;
v___y_3195_ = v___y_3256_;
v___y_3196_ = v___y_3257_;
v___y_3197_ = v___y_3258_;
v___y_3198_ = v___y_3260_;
v___y_3199_ = v___y_3261_;
v___y_3200_ = v___y_3262_;
v___y_3201_ = v___y_3263_;
v___y_3202_ = v___y_3264_;
v___y_3203_ = v___y_3265_;
v___y_3204_ = v___y_3266_;
v___y_3205_ = v___y_3267_;
v___y_3206_ = v___y_3268_;
v___y_3207_ = v___y_3269_;
v___y_3208_ = v___y_3270_;
v___y_3209_ = v___x_3282_;
goto v___jp_3192_;
}
v___jp_3283_:
{
lean_object* v___x_3305_; double v___x_3306_; double v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3305_ = lean_io_get_num_heartbeats();
v___x_3306_ = lean_float_of_nat(v___y_3284_);
v___x_3307_ = lean_float_of_nat(v___x_3305_);
v___x_3308_ = lean_box_float(v___x_3306_);
v___x_3309_ = lean_box_float(v___x_3307_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_a_3304_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
lean_inc_ref(v___x_2772_);
lean_inc(v___y_3299_);
v___x_3312_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_3299_, v___x_2771_, v___x_2772_, v___y_3288_, v___y_3292_, v___y_3286_, v___f_2778_, v___x_3311_, v___y_3297_, v___y_3303_, v___y_3300_, v___y_3298_, v___y_3285_, v___y_3294_, v___y_3291_, v___y_3295_, v___y_3301_, v___y_3296_, v___y_3290_, v___y_3289_, v___y_3302_, v___y_3287_);
v___y_3193_ = v___y_3285_;
v___y_3194_ = v___y_3287_;
v___y_3195_ = v___y_3289_;
v___y_3196_ = v___y_3290_;
v___y_3197_ = v___y_3291_;
v___y_3198_ = v___y_3293_;
v___y_3199_ = v___y_3294_;
v___y_3200_ = v___y_3295_;
v___y_3201_ = v___y_3296_;
v___y_3202_ = v___y_3297_;
v___y_3203_ = v___y_3298_;
v___y_3204_ = v___y_3299_;
v___y_3205_ = v___y_3300_;
v___y_3206_ = v___y_3301_;
v___y_3207_ = v___y_3302_;
v___y_3208_ = v___y_3303_;
v___y_3209_ = v___x_3312_;
goto v___jp_3192_;
}
v___jp_3313_:
{
lean_object* v___x_3334_; lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3388_; 
v___x_3334_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_3315_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3388_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3388_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
uint8_t v___x_3339_; 
v___x_3339_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_3316_, v___x_2774_);
if (v___x_3339_ == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_io_mono_nanos_now();
v___x_3341_ = l_IO_lazyPure___redArg(v___y_3324_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_del_object(v___x_3337_);
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set_tag(v___x_3344_, 1);
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
v___y_3251_ = v___y_3314_;
v___y_3252_ = v_a_3335_;
v___y_3253_ = v___y_3315_;
v___y_3254_ = v___y_3316_;
v___y_3255_ = v___x_3340_;
v___y_3256_ = v___y_3318_;
v___y_3257_ = v___y_3317_;
v___y_3258_ = v___y_3319_;
v___y_3259_ = v___y_3320_;
v___y_3260_ = v___y_3321_;
v___y_3261_ = v___y_3322_;
v___y_3262_ = v___y_3323_;
v___y_3263_ = v___y_3325_;
v___y_3264_ = v___y_3326_;
v___y_3265_ = v___y_3327_;
v___y_3266_ = v___y_3329_;
v___y_3267_ = v___y_3330_;
v___y_3268_ = v___y_3331_;
v___y_3269_ = v___y_3332_;
v___y_3270_ = v___y_3333_;
v_a_3271_ = v___x_3347_;
goto v___jp_3250_;
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3363_; 
v_a_3350_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3352_ = v___x_3341_;
v_isShared_3353_ = v_isSharedCheck_3363_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3341_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3363_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3354_ = lean_io_error_to_string(v_a_3350_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set_tag(v___x_3352_, 3);
lean_ctor_set(v___x_3352_, 0, v___x_3354_);
v___x_3356_ = v___x_3352_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3357_ = l_Lean_MessageData_ofFormat(v___x_3356_);
lean_inc(v___y_3328_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___y_3328_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3358_);
v___x_3360_ = v___x_3337_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
v___y_3251_ = v___y_3314_;
v___y_3252_ = v_a_3335_;
v___y_3253_ = v___y_3315_;
v___y_3254_ = v___y_3316_;
v___y_3255_ = v___x_3340_;
v___y_3256_ = v___y_3318_;
v___y_3257_ = v___y_3317_;
v___y_3258_ = v___y_3319_;
v___y_3259_ = v___y_3320_;
v___y_3260_ = v___y_3321_;
v___y_3261_ = v___y_3322_;
v___y_3262_ = v___y_3323_;
v___y_3263_ = v___y_3325_;
v___y_3264_ = v___y_3326_;
v___y_3265_ = v___y_3327_;
v___y_3266_ = v___y_3329_;
v___y_3267_ = v___y_3330_;
v___y_3268_ = v___y_3331_;
v___y_3269_ = v___y_3332_;
v___y_3270_ = v___y_3333_;
v_a_3271_ = v___x_3360_;
goto v___jp_3250_;
}
}
}
}
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = lean_io_get_num_heartbeats();
v___x_3365_ = l_IO_lazyPure___redArg(v___y_3324_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_del_object(v___x_3337_);
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3365_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 1);
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
v___y_3284_ = v___x_3364_;
v___y_3285_ = v___y_3314_;
v___y_3286_ = v_a_3335_;
v___y_3287_ = v___y_3315_;
v___y_3288_ = v___y_3316_;
v___y_3289_ = v___y_3318_;
v___y_3290_ = v___y_3317_;
v___y_3291_ = v___y_3319_;
v___y_3292_ = v___y_3320_;
v___y_3293_ = v___y_3321_;
v___y_3294_ = v___y_3322_;
v___y_3295_ = v___y_3323_;
v___y_3296_ = v___y_3325_;
v___y_3297_ = v___y_3326_;
v___y_3298_ = v___y_3327_;
v___y_3299_ = v___y_3329_;
v___y_3300_ = v___y_3330_;
v___y_3301_ = v___y_3331_;
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3333_;
v_a_3304_ = v___x_3371_;
goto v___jp_3283_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3387_; 
v_a_3374_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3376_ = v___x_3365_;
v_isShared_3377_ = v_isSharedCheck_3387_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3365_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3387_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3378_ = lean_io_error_to_string(v_a_3374_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set_tag(v___x_3376_, 3);
lean_ctor_set(v___x_3376_, 0, v___x_3378_);
v___x_3380_ = v___x_3376_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3381_ = l_Lean_MessageData_ofFormat(v___x_3380_);
lean_inc(v___y_3328_);
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___y_3328_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3382_);
v___x_3384_ = v___x_3337_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
v___y_3284_ = v___x_3364_;
v___y_3285_ = v___y_3314_;
v___y_3286_ = v_a_3335_;
v___y_3287_ = v___y_3315_;
v___y_3288_ = v___y_3316_;
v___y_3289_ = v___y_3318_;
v___y_3290_ = v___y_3317_;
v___y_3291_ = v___y_3319_;
v___y_3292_ = v___y_3320_;
v___y_3293_ = v___y_3321_;
v___y_3294_ = v___y_3322_;
v___y_3295_ = v___y_3323_;
v___y_3296_ = v___y_3325_;
v___y_3297_ = v___y_3326_;
v___y_3298_ = v___y_3327_;
v___y_3299_ = v___y_3329_;
v___y_3300_ = v___y_3330_;
v___y_3301_ = v___y_3331_;
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3333_;
v_a_3304_ = v___x_3384_;
goto v___jp_3283_;
}
}
}
}
}
}
}
v___jp_3389_:
{
lean_object* v_toCold_3404_; lean_object* v_options_3405_; lean_object* v_cnf_3406_; lean_object* v_ref_3407_; lean_object* v_inheritedTraceOptions_3408_; uint8_t v_hasTrace_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___f_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v_toCold_3404_ = lean_ctor_get(v___y_3402_, 0);
v_options_3405_ = lean_ctor_get(v_toCold_3404_, 2);
v_cnf_3406_ = lean_ctor_get(v_cnfCache_2779_, 0);
v_ref_3407_ = lean_ctor_get(v___y_3402_, 2);
v_inheritedTraceOptions_3408_ = lean_ctor_get(v_toCold_3404_, 11);
v_hasTrace_3409_ = lean_ctor_get_uint8(v_options_3405_, sizeof(void*)*1);
v___x_3410_ = lean_array_get_size(v_cnf_3406_);
v___x_3411_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_3412_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v_aig_2767_, v_cnfCache_2779_);
v___f_3413_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_3413_, 0, v___x_2780_);
lean_closure_set(v___f_3413_, 1, v___x_3411_);
lean_closure_set(v___f_3413_, 2, v_result_2781_);
lean_closure_set(v___f_3413_, 3, v___x_3412_);
v___x_3414_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__13));
v___x_3415_ = l_Lean_Name_mkStr3(v___x_2782_, v___x_2783_, v___x_3414_);
if (v_hasTrace_3409_ == 0)
{
lean_object* v___x_3416_; 
lean_dec_ref(v___f_2778_);
v___x_3416_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_3413_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
v___y_3193_ = v___y_3394_;
v___y_3194_ = v___y_3403_;
v___y_3195_ = v___y_3401_;
v___y_3196_ = v___y_3400_;
v___y_3197_ = v___y_3396_;
v___y_3198_ = v___x_3410_;
v___y_3199_ = v___y_3395_;
v___y_3200_ = v___y_3397_;
v___y_3201_ = v___y_3399_;
v___y_3202_ = v___y_3390_;
v___y_3203_ = v___y_3393_;
v___y_3204_ = v___x_3415_;
v___y_3205_ = v___y_3392_;
v___y_3206_ = v___y_3398_;
v___y_3207_ = v___y_3402_;
v___y_3208_ = v___y_3391_;
v___y_3209_ = v___x_3416_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3417_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___x_3415_);
v___x_3418_ = l_Lean_Name_append(v___x_3417_, v___x_3415_);
v___x_3419_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3408_, v_options_3405_, v___x_3418_);
lean_dec(v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3420_ = l_Lean_trace_profiler;
v___x_3421_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3405_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
lean_dec_ref(v___f_2778_);
v___x_3422_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_3413_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
v___y_3193_ = v___y_3394_;
v___y_3194_ = v___y_3403_;
v___y_3195_ = v___y_3401_;
v___y_3196_ = v___y_3400_;
v___y_3197_ = v___y_3396_;
v___y_3198_ = v___x_3410_;
v___y_3199_ = v___y_3395_;
v___y_3200_ = v___y_3397_;
v___y_3201_ = v___y_3399_;
v___y_3202_ = v___y_3390_;
v___y_3203_ = v___y_3393_;
v___y_3204_ = v___x_3415_;
v___y_3205_ = v___y_3392_;
v___y_3206_ = v___y_3398_;
v___y_3207_ = v___y_3402_;
v___y_3208_ = v___y_3391_;
v___y_3209_ = v___x_3422_;
goto v___jp_3192_;
}
else
{
v___y_3314_ = v___y_3394_;
v___y_3315_ = v___y_3403_;
v___y_3316_ = v_options_3405_;
v___y_3317_ = v___y_3400_;
v___y_3318_ = v___y_3401_;
v___y_3319_ = v___y_3396_;
v___y_3320_ = v___x_3419_;
v___y_3321_ = v___x_3410_;
v___y_3322_ = v___y_3395_;
v___y_3323_ = v___y_3397_;
v___y_3324_ = v___f_3413_;
v___y_3325_ = v___y_3399_;
v___y_3326_ = v___y_3390_;
v___y_3327_ = v___y_3393_;
v___y_3328_ = v_ref_3407_;
v___y_3329_ = v___x_3415_;
v___y_3330_ = v___y_3392_;
v___y_3331_ = v___y_3398_;
v___y_3332_ = v___y_3402_;
v___y_3333_ = v___y_3391_;
goto v___jp_3313_;
}
}
else
{
v___y_3314_ = v___y_3394_;
v___y_3315_ = v___y_3403_;
v___y_3316_ = v_options_3405_;
v___y_3317_ = v___y_3400_;
v___y_3318_ = v___y_3401_;
v___y_3319_ = v___y_3396_;
v___y_3320_ = v___x_3419_;
v___y_3321_ = v___x_3410_;
v___y_3322_ = v___y_3395_;
v___y_3323_ = v___y_3397_;
v___y_3324_ = v___f_3413_;
v___y_3325_ = v___y_3399_;
v___y_3326_ = v___y_3390_;
v___y_3327_ = v___y_3393_;
v___y_3328_ = v_ref_3407_;
v___y_3329_ = v___x_3415_;
v___y_3330_ = v___y_3392_;
v___y_3331_ = v___y_3398_;
v___y_3332_ = v___y_3402_;
v___y_3333_ = v___y_3391_;
goto v___jp_3313_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticContext_2765_ = stack[0].m_obj;
lean_object* v___x_2766_ = stack[1].m_obj;
lean_object* v_aig_2767_ = stack[2].m_obj;
lean_object* v___x_2768_ = stack[3].m_obj;
lean_object* v___x_2769_ = stack[4].m_obj;
lean_object* v___x_2770_ = stack[5].m_obj;
uint8_t v___x_2771_ = stack[6].m_num;
lean_object* v___x_2772_ = stack[7].m_obj;
lean_object* v___f_2773_ = stack[8].m_obj;
lean_object* v___x_2774_ = stack[9].m_obj;
lean_object* v_cache_2775_ = stack[10].m_obj;
lean_object* v_ref_2776_ = stack[11].m_obj;
lean_object* v_cls_2777_ = stack[12].m_obj;
lean_object* v___f_2778_ = stack[13].m_obj;
lean_object* v_cnfCache_2779_ = stack[14].m_obj;
lean_object* v___x_2780_ = stack[15].m_obj;
lean_object* v_result_2781_ = stack[16].m_obj;
lean_object* v___x_2782_ = stack[17].m_obj;
lean_object* v___x_2783_ = stack[18].m_obj;
lean_object* v_____r_2784_ = stack[19].m_obj;
lean_object* v___y_2785_ = stack[20].m_obj;
lean_object* v___y_2786_ = stack[21].m_obj;
lean_object* v___y_2787_ = stack[22].m_obj;
lean_object* v___y_2788_ = stack[23].m_obj;
lean_object* v___y_2789_ = stack[24].m_obj;
lean_object* v___y_2790_ = stack[25].m_obj;
lean_object* v___y_2791_ = stack[26].m_obj;
lean_object* v___y_2792_ = stack[27].m_obj;
lean_object* v___y_2793_ = stack[28].m_obj;
lean_object* v___y_2794_ = stack[29].m_obj;
lean_object* v___y_2795_ = stack[30].m_obj;
lean_object* v___y_2796_ = stack[31].m_obj;
lean_object* v___y_2797_ = stack[32].m_obj;
lean_object* v___y_2798_ = stack[33].m_obj;
lean_object* v_res_3441_;
v_res_3441_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v_tacticContext_2765_, v___x_2766_, v_aig_2767_, v___x_2768_, v___x_2769_, v___x_2770_, v___x_2771_, v___x_2772_, v___f_2773_, v___x_2774_, v_cache_2775_, v_ref_2776_, v_cls_2777_, v___f_2778_, v_cnfCache_2779_, v___x_2780_, v_result_2781_, v___x_2782_, v___x_2783_, v_____r_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
stack->m_obj
 = v_res_3441_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11___boxed(lean_object** _args){
lean_object* v_tacticContext_3442_ = _args[0];
lean_object* v___x_3443_ = _args[1];
lean_object* v_aig_3444_ = _args[2];
lean_object* v___x_3445_ = _args[3];
lean_object* v___x_3446_ = _args[4];
lean_object* v___x_3447_ = _args[5];
lean_object* v___x_3448_ = _args[6];
lean_object* v___x_3449_ = _args[7];
lean_object* v___f_3450_ = _args[8];
lean_object* v___x_3451_ = _args[9];
lean_object* v_cache_3452_ = _args[10];
lean_object* v_ref_3453_ = _args[11];
lean_object* v_cls_3454_ = _args[12];
lean_object* v___f_3455_ = _args[13];
lean_object* v_cnfCache_3456_ = _args[14];
lean_object* v___x_3457_ = _args[15];
lean_object* v_result_3458_ = _args[16];
lean_object* v___x_3459_ = _args[17];
lean_object* v___x_3460_ = _args[18];
lean_object* v_____r_3461_ = _args[19];
lean_object* v___y_3462_ = _args[20];
lean_object* v___y_3463_ = _args[21];
lean_object* v___y_3464_ = _args[22];
lean_object* v___y_3465_ = _args[23];
lean_object* v___y_3466_ = _args[24];
lean_object* v___y_3467_ = _args[25];
lean_object* v___y_3468_ = _args[26];
lean_object* v___y_3469_ = _args[27];
lean_object* v___y_3470_ = _args[28];
lean_object* v___y_3471_ = _args[29];
lean_object* v___y_3472_ = _args[30];
lean_object* v___y_3473_ = _args[31];
lean_object* v___y_3474_ = _args[32];
lean_object* v___y_3475_ = _args[33];
lean_object* v___y_3476_ = _args[34];
_start:
{
uint8_t v___x_1195816__boxed_3477_; lean_object* v_res_3478_; 
v___x_1195816__boxed_3477_ = lean_unbox(v___x_3448_);
v_res_3478_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v_tacticContext_3442_, v___x_3443_, v_aig_3444_, v___x_3445_, v___x_3446_, v___x_3447_, v___x_1195816__boxed_3477_, v___x_3449_, v___f_3450_, v___x_3451_, v_cache_3452_, v_ref_3453_, v_cls_3454_, v___f_3455_, v_cnfCache_3456_, v___x_3457_, v_result_3458_, v___x_3459_, v___x_3460_, v_____r_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v_ref_3453_);
lean_dec_ref(v___x_3451_);
lean_dec(v___x_3443_);
return v_res_3478_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(lean_object* v_e_3479_){
_start:
{
if (lean_obj_tag(v_e_3479_) == 0)
{
uint8_t v___x_3480_; 
v___x_3480_ = 2;
return v___x_3480_;
}
else
{
uint8_t v___x_3481_; 
v___x_3481_ = 0;
return v___x_3481_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3479_ = stack[0].m_obj;
uint8_t v_res_3482_;
v_res_3482_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(v_e_3479_);
stack->m_num = v_res_3482_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20___boxed(lean_object* v_e_3483_){
_start:
{
uint8_t v_res_3484_; lean_object* v_r_3485_; 
v_res_3484_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(v_e_3483_);
lean_dec_ref(v_e_3483_);
v_r_3485_ = lean_box(v_res_3484_);
return v_r_3485_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(lean_object* v_cls_3486_, uint8_t v_collapsed_3487_, lean_object* v_tag_3488_, lean_object* v_opts_3489_, uint8_t v_clsEnabled_3490_, lean_object* v_oldTraces_3491_, lean_object* v_msg_3492_, lean_object* v_resStartStop_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_fst_3509_; lean_object* v_snd_3510_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v_data_3514_; lean_object* v_fst_3525_; lean_object* v_snd_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; lean_object* v___y_3530_; lean_object* v_a_3531_; uint8_t v___y_3546_; double v___y_3578_; 
v_fst_3509_ = lean_ctor_get(v_resStartStop_3493_, 0);
lean_inc(v_fst_3509_);
v_snd_3510_ = lean_ctor_get(v_resStartStop_3493_, 1);
lean_inc(v_snd_3510_);
lean_dec_ref(v_resStartStop_3493_);
v_fst_3525_ = lean_ctor_get(v_snd_3510_, 0);
lean_inc(v_fst_3525_);
v_snd_3526_ = lean_ctor_get(v_snd_3510_, 1);
lean_inc(v_snd_3526_);
lean_dec(v_snd_3510_);
v___x_3527_ = l_Lean_trace_profiler;
v___x_3528_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3489_, v___x_3527_);
if (v___x_3528_ == 0)
{
v___y_3546_ = v___x_3528_;
goto v___jp_3545_;
}
else
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3584_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3489_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; lean_object* v___x_3586_; double v___x_3587_; double v___x_3588_; double v___x_3589_; 
v___x_3585_ = l_Lean_trace_profiler_threshold;
v___x_3586_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3489_, v___x_3585_);
v___x_3587_ = lean_float_of_nat(v___x_3586_);
v___x_3588_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_3589_ = lean_float_div(v___x_3587_, v___x_3588_);
v___y_3578_ = v___x_3589_;
goto v___jp_3577_;
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; double v___x_3592_; 
v___x_3590_ = l_Lean_trace_profiler_threshold;
v___x_3591_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3489_, v___x_3590_);
v___x_3592_ = lean_float_of_nat(v___x_3591_);
v___y_3578_ = v___x_3592_;
goto v___jp_3577_;
}
}
v___jp_3511_:
{
lean_object* v___x_3515_; 
lean_inc(v___y_3513_);
v___x_3515_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_3491_, v_data_3514_, v___y_3513_, v___y_3512_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v___x_3516_; 
lean_dec_ref_known(v___x_3515_, 1);
v___x_3516_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3509_);
return v___x_3516_;
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec(v_fst_3509_);
v_a_3517_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3515_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
v___jp_3529_:
{
uint8_t v_result_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; double v___x_3535_; lean_object* v_data_3536_; 
v_result_3532_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_spec__20(v_fst_3509_);
v___x_3533_ = lean_box(v_result_3532_);
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
v___x_3535_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_3488_);
lean_inc_ref(v___x_3534_);
lean_inc(v_cls_3486_);
v_data_3536_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3536_, 0, v_cls_3486_);
lean_ctor_set(v_data_3536_, 1, v___x_3534_);
lean_ctor_set(v_data_3536_, 2, v_tag_3488_);
lean_ctor_set_float(v_data_3536_, sizeof(void*)*3, v___x_3535_);
lean_ctor_set_float(v_data_3536_, sizeof(void*)*3 + 8, v___x_3535_);
lean_ctor_set_uint8(v_data_3536_, sizeof(void*)*3 + 16, v_collapsed_3487_);
if (v___x_3528_ == 0)
{
lean_dec_ref_known(v___x_3534_, 1);
lean_dec(v_snd_3526_);
lean_dec(v_fst_3525_);
lean_dec_ref(v_tag_3488_);
lean_dec(v_cls_3486_);
v___y_3512_ = v_a_3531_;
v___y_3513_ = v___y_3530_;
v_data_3514_ = v_data_3536_;
goto v___jp_3511_;
}
else
{
lean_object* v_data_3537_; double v___x_3538_; double v___x_3539_; 
lean_dec_ref_known(v_data_3536_, 3);
v_data_3537_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3537_, 0, v_cls_3486_);
lean_ctor_set(v_data_3537_, 1, v___x_3534_);
lean_ctor_set(v_data_3537_, 2, v_tag_3488_);
v___x_3538_ = lean_unbox_float(v_fst_3525_);
lean_dec(v_fst_3525_);
lean_ctor_set_float(v_data_3537_, sizeof(void*)*3, v___x_3538_);
v___x_3539_ = lean_unbox_float(v_snd_3526_);
lean_dec(v_snd_3526_);
lean_ctor_set_float(v_data_3537_, sizeof(void*)*3 + 8, v___x_3539_);
lean_ctor_set_uint8(v_data_3537_, sizeof(void*)*3 + 16, v_collapsed_3487_);
v___y_3512_ = v_a_3531_;
v___y_3513_ = v___y_3530_;
v_data_3514_ = v_data_3537_;
goto v___jp_3511_;
}
}
v___jp_3540_:
{
lean_object* v_ref_3541_; lean_object* v___x_3542_; 
v_ref_3541_ = lean_ctor_get(v___y_3506_, 2);
lean_inc(v___y_3507_);
lean_inc_ref(v___y_3506_);
lean_inc(v___y_3505_);
lean_inc_ref(v___y_3504_);
lean_inc(v___y_3503_);
lean_inc_ref(v___y_3502_);
lean_inc(v___y_3501_);
lean_inc_ref(v___y_3500_);
lean_inc(v___y_3499_);
lean_inc(v___y_3498_);
lean_inc_ref(v___y_3497_);
lean_inc(v___y_3496_);
lean_inc(v___y_3495_);
lean_inc_ref(v___y_3494_);
lean_inc(v_fst_3509_);
v___x_3542_ = lean_apply_16(v_msg_3492_, v_fst_3509_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, lean_box(0));
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v___y_3530_ = v_ref_3541_;
v_a_3531_ = v_a_3543_;
goto v___jp_3529_;
}
else
{
lean_object* v___x_3544_; 
lean_dec_ref_known(v___x_3542_, 1);
v___x_3544_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_3530_ = v_ref_3541_;
v_a_3531_ = v___x_3544_;
goto v___jp_3529_;
}
}
v___jp_3545_:
{
if (v_clsEnabled_3490_ == 0)
{
if (v___y_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v_traceState_3548_; lean_object* v_env_3549_; lean_object* v_nextMacroScope_3550_; lean_object* v_ngen_3551_; lean_object* v_auxDeclNGen_3552_; lean_object* v_cache_3553_; lean_object* v_recordedDeps_3554_; lean_object* v_messages_3555_; lean_object* v_infoState_3556_; lean_object* v_snapshotTasks_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_snd_3526_);
lean_dec(v_fst_3525_);
lean_dec_ref(v_msg_3492_);
lean_dec_ref(v_tag_3488_);
lean_dec(v_cls_3486_);
v___x_3547_ = lean_st_ref_take(v___y_3507_);
v_traceState_3548_ = lean_ctor_get(v___x_3547_, 4);
v_env_3549_ = lean_ctor_get(v___x_3547_, 0);
v_nextMacroScope_3550_ = lean_ctor_get(v___x_3547_, 1);
v_ngen_3551_ = lean_ctor_get(v___x_3547_, 2);
v_auxDeclNGen_3552_ = lean_ctor_get(v___x_3547_, 3);
v_cache_3553_ = lean_ctor_get(v___x_3547_, 5);
v_recordedDeps_3554_ = lean_ctor_get(v___x_3547_, 6);
v_messages_3555_ = lean_ctor_get(v___x_3547_, 7);
v_infoState_3556_ = lean_ctor_get(v___x_3547_, 8);
v_snapshotTasks_3557_ = lean_ctor_get(v___x_3547_, 9);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3559_ = v___x_3547_;
v_isShared_3560_ = v_isSharedCheck_3576_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_snapshotTasks_3557_);
lean_inc(v_infoState_3556_);
lean_inc(v_messages_3555_);
lean_inc(v_recordedDeps_3554_);
lean_inc(v_cache_3553_);
lean_inc(v_traceState_3548_);
lean_inc(v_auxDeclNGen_3552_);
lean_inc(v_ngen_3551_);
lean_inc(v_nextMacroScope_3550_);
lean_inc(v_env_3549_);
lean_dec(v___x_3547_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3576_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
uint64_t v_tid_3561_; lean_object* v_traces_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3575_; 
v_tid_3561_ = lean_ctor_get_uint64(v_traceState_3548_, sizeof(void*)*1);
v_traces_3562_ = lean_ctor_get(v_traceState_3548_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_traceState_3548_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3564_ = v_traceState_3548_;
v_isShared_3565_ = v_isSharedCheck_3575_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_traces_3562_);
lean_dec(v_traceState_3548_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3575_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3566_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3491_, v_traces_3562_);
lean_dec_ref(v_traces_3562_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3566_);
v___x_3568_ = v___x_3564_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3566_);
lean_ctor_set_uint64(v_reuseFailAlloc_3574_, sizeof(void*)*1, v_tid_3561_);
v___x_3568_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3570_; 
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 4, v___x_3568_);
v___x_3570_ = v___x_3559_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_env_3549_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_nextMacroScope_3550_);
lean_ctor_set(v_reuseFailAlloc_3573_, 2, v_ngen_3551_);
lean_ctor_set(v_reuseFailAlloc_3573_, 3, v_auxDeclNGen_3552_);
lean_ctor_set(v_reuseFailAlloc_3573_, 4, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3573_, 5, v_cache_3553_);
lean_ctor_set(v_reuseFailAlloc_3573_, 6, v_recordedDeps_3554_);
lean_ctor_set(v_reuseFailAlloc_3573_, 7, v_messages_3555_);
lean_ctor_set(v_reuseFailAlloc_3573_, 8, v_infoState_3556_);
lean_ctor_set(v_reuseFailAlloc_3573_, 9, v_snapshotTasks_3557_);
v___x_3570_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_st_ref_put(v___y_3507_, v___x_3570_);
v___x_3572_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3509_);
return v___x_3572_;
}
}
}
}
}
else
{
goto v___jp_3540_;
}
}
else
{
goto v___jp_3540_;
}
}
v___jp_3577_:
{
double v___x_3579_; double v___x_3580_; double v___x_3581_; uint8_t v___x_3582_; 
v___x_3579_ = lean_unbox_float(v_snd_3526_);
v___x_3580_ = lean_unbox_float(v_fst_3525_);
v___x_3581_ = lean_float_sub(v___x_3579_, v___x_3580_);
v___x_3582_ = lean_float_decLt(v___y_3578_, v___x_3581_);
v___y_3546_ = v___x_3582_;
goto v___jp_3545_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3486_ = stack[0].m_obj;
uint8_t v_collapsed_3487_ = stack[1].m_num;
lean_object* v_tag_3488_ = stack[2].m_obj;
lean_object* v_opts_3489_ = stack[3].m_obj;
uint8_t v_clsEnabled_3490_ = stack[4].m_num;
lean_object* v_oldTraces_3491_ = stack[5].m_obj;
lean_object* v_msg_3492_ = stack[6].m_obj;
lean_object* v_resStartStop_3493_ = stack[7].m_obj;
lean_object* v___y_3494_ = stack[8].m_obj;
lean_object* v___y_3495_ = stack[9].m_obj;
lean_object* v___y_3496_ = stack[10].m_obj;
lean_object* v___y_3497_ = stack[11].m_obj;
lean_object* v___y_3498_ = stack[12].m_obj;
lean_object* v___y_3499_ = stack[13].m_obj;
lean_object* v___y_3500_ = stack[14].m_obj;
lean_object* v___y_3501_ = stack[15].m_obj;
lean_object* v___y_3502_ = stack[16].m_obj;
lean_object* v___y_3503_ = stack[17].m_obj;
lean_object* v___y_3504_ = stack[18].m_obj;
lean_object* v___y_3505_ = stack[19].m_obj;
lean_object* v___y_3506_ = stack[20].m_obj;
lean_object* v___y_3507_ = stack[21].m_obj;
lean_object* v_res_3593_;
v_res_3593_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_3486_, v_collapsed_3487_, v_tag_3488_, v_opts_3489_, v_clsEnabled_3490_, v_oldTraces_3491_, v_msg_3492_, v_resStartStop_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
stack->m_obj
 = v_res_3593_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9___boxed(lean_object** _args){
lean_object* v_cls_3594_ = _args[0];
lean_object* v_collapsed_3595_ = _args[1];
lean_object* v_tag_3596_ = _args[2];
lean_object* v_opts_3597_ = _args[3];
lean_object* v_clsEnabled_3598_ = _args[4];
lean_object* v_oldTraces_3599_ = _args[5];
lean_object* v_msg_3600_ = _args[6];
lean_object* v_resStartStop_3601_ = _args[7];
lean_object* v___y_3602_ = _args[8];
lean_object* v___y_3603_ = _args[9];
lean_object* v___y_3604_ = _args[10];
lean_object* v___y_3605_ = _args[11];
lean_object* v___y_3606_ = _args[12];
lean_object* v___y_3607_ = _args[13];
lean_object* v___y_3608_ = _args[14];
lean_object* v___y_3609_ = _args[15];
lean_object* v___y_3610_ = _args[16];
lean_object* v___y_3611_ = _args[17];
lean_object* v___y_3612_ = _args[18];
lean_object* v___y_3613_ = _args[19];
lean_object* v___y_3614_ = _args[20];
lean_object* v___y_3615_ = _args[21];
lean_object* v___y_3616_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_3617_; uint8_t v_clsEnabled_boxed_3618_; lean_object* v_res_3619_; 
v_collapsed_boxed_3617_ = lean_unbox(v_collapsed_3595_);
v_clsEnabled_boxed_3618_ = lean_unbox(v_clsEnabled_3598_);
v_res_3619_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_3594_, v_collapsed_boxed_3617_, v_tag_3596_, v_opts_3597_, v_clsEnabled_boxed_3618_, v_oldTraces_3599_, v_msg_3600_, v_resStartStop_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v_opts_3597_);
return v_res_3619_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(lean_object* v_e_3620_){
_start:
{
if (lean_obj_tag(v_e_3620_) == 0)
{
uint8_t v___x_3621_; 
v___x_3621_ = 2;
return v___x_3621_;
}
else
{
uint8_t v___x_3622_; 
v___x_3622_ = 0;
return v___x_3622_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3620_ = stack[0].m_obj;
uint8_t v_res_3623_;
v_res_3623_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(v_e_3620_);
stack->m_num = v_res_3623_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22___boxed(lean_object* v_e_3624_){
_start:
{
uint8_t v_res_3625_; lean_object* v_r_3626_; 
v_res_3625_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(v_e_3624_);
lean_dec_ref(v_e_3624_);
v_r_3626_ = lean_box(v_res_3625_);
return v_r_3626_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(lean_object* v_cls_3627_, uint8_t v_collapsed_3628_, lean_object* v_tag_3629_, lean_object* v_opts_3630_, uint8_t v_clsEnabled_3631_, lean_object* v_oldTraces_3632_, lean_object* v_msg_3633_, lean_object* v_resStartStop_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_fst_3650_; lean_object* v_snd_3651_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v_data_3655_; lean_object* v_fst_3666_; lean_object* v_snd_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; lean_object* v___y_3671_; lean_object* v_a_3672_; uint8_t v___y_3687_; double v___y_3719_; 
v_fst_3650_ = lean_ctor_get(v_resStartStop_3634_, 0);
lean_inc(v_fst_3650_);
v_snd_3651_ = lean_ctor_get(v_resStartStop_3634_, 1);
lean_inc(v_snd_3651_);
lean_dec_ref(v_resStartStop_3634_);
v_fst_3666_ = lean_ctor_get(v_snd_3651_, 0);
lean_inc(v_fst_3666_);
v_snd_3667_ = lean_ctor_get(v_snd_3651_, 1);
lean_inc(v_snd_3667_);
lean_dec(v_snd_3651_);
v___x_3668_ = l_Lean_trace_profiler;
v___x_3669_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3630_, v___x_3668_);
if (v___x_3669_ == 0)
{
v___y_3687_ = v___x_3669_;
goto v___jp_3686_;
}
else
{
lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3725_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_opts_3630_, v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; double v___x_3728_; double v___x_3729_; double v___x_3730_; 
v___x_3726_ = l_Lean_trace_profiler_threshold;
v___x_3727_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3630_, v___x_3726_);
v___x_3728_ = lean_float_of_nat(v___x_3727_);
v___x_3729_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__3);
v___x_3730_ = lean_float_div(v___x_3728_, v___x_3729_);
v___y_3719_ = v___x_3730_;
goto v___jp_3718_;
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; double v___x_3733_; 
v___x_3731_ = l_Lean_trace_profiler_threshold;
v___x_3732_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__11(v_opts_3630_, v___x_3731_);
v___x_3733_ = lean_float_of_nat(v___x_3732_);
v___y_3719_ = v___x_3733_;
goto v___jp_3718_;
}
}
v___jp_3652_:
{
lean_object* v___x_3656_; 
lean_inc(v___y_3653_);
v___x_3656_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_3632_, v_data_3655_, v___y_3653_, v___y_3654_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v___x_3657_; 
lean_dec_ref_known(v___x_3656_, 1);
v___x_3657_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3650_);
return v___x_3657_;
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v_fst_3650_);
v_a_3658_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3656_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3656_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
v___jp_3670_:
{
uint8_t v_result_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; double v___x_3676_; lean_object* v_data_3677_; 
v_result_3673_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_spec__22(v_fst_3650_);
v___x_3674_ = lean_box(v_result_3673_);
v___x_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
v___x_3676_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__0);
lean_inc_ref(v_tag_3629_);
lean_inc_ref(v___x_3675_);
lean_inc(v_cls_3627_);
v_data_3677_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3677_, 0, v_cls_3627_);
lean_ctor_set(v_data_3677_, 1, v___x_3675_);
lean_ctor_set(v_data_3677_, 2, v_tag_3629_);
lean_ctor_set_float(v_data_3677_, sizeof(void*)*3, v___x_3676_);
lean_ctor_set_float(v_data_3677_, sizeof(void*)*3 + 8, v___x_3676_);
lean_ctor_set_uint8(v_data_3677_, sizeof(void*)*3 + 16, v_collapsed_3628_);
if (v___x_3669_ == 0)
{
lean_dec_ref_known(v___x_3675_, 1);
lean_dec(v_snd_3667_);
lean_dec(v_fst_3666_);
lean_dec_ref(v_tag_3629_);
lean_dec(v_cls_3627_);
v___y_3653_ = v___y_3671_;
v___y_3654_ = v_a_3672_;
v_data_3655_ = v_data_3677_;
goto v___jp_3652_;
}
else
{
lean_object* v_data_3678_; double v___x_3679_; double v___x_3680_; 
lean_dec_ref_known(v_data_3677_, 3);
v_data_3678_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3678_, 0, v_cls_3627_);
lean_ctor_set(v_data_3678_, 1, v___x_3675_);
lean_ctor_set(v_data_3678_, 2, v_tag_3629_);
v___x_3679_ = lean_unbox_float(v_fst_3666_);
lean_dec(v_fst_3666_);
lean_ctor_set_float(v_data_3678_, sizeof(void*)*3, v___x_3679_);
v___x_3680_ = lean_unbox_float(v_snd_3667_);
lean_dec(v_snd_3667_);
lean_ctor_set_float(v_data_3678_, sizeof(void*)*3 + 8, v___x_3680_);
lean_ctor_set_uint8(v_data_3678_, sizeof(void*)*3 + 16, v_collapsed_3628_);
v___y_3653_ = v___y_3671_;
v___y_3654_ = v_a_3672_;
v_data_3655_ = v_data_3678_;
goto v___jp_3652_;
}
}
v___jp_3681_:
{
lean_object* v_ref_3682_; lean_object* v___x_3683_; 
v_ref_3682_ = lean_ctor_get(v___y_3647_, 2);
lean_inc(v___y_3648_);
lean_inc_ref(v___y_3647_);
lean_inc(v___y_3646_);
lean_inc_ref(v___y_3645_);
lean_inc(v___y_3644_);
lean_inc_ref(v___y_3643_);
lean_inc(v___y_3642_);
lean_inc_ref(v___y_3641_);
lean_inc(v___y_3640_);
lean_inc(v___y_3639_);
lean_inc_ref(v___y_3638_);
lean_inc(v___y_3637_);
lean_inc(v___y_3636_);
lean_inc_ref(v___y_3635_);
lean_inc(v_fst_3650_);
v___x_3683_ = lean_apply_16(v_msg_3633_, v_fst_3650_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, lean_box(0));
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v___y_3671_ = v_ref_3682_;
v_a_3672_ = v_a_3684_;
goto v___jp_3670_;
}
else
{
lean_object* v___x_3685_; 
lean_dec_ref_known(v___x_3683_, 1);
v___x_3685_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6___closed__2);
v___y_3671_ = v_ref_3682_;
v_a_3672_ = v___x_3685_;
goto v___jp_3670_;
}
}
v___jp_3686_:
{
if (v_clsEnabled_3631_ == 0)
{
if (v___y_3687_ == 0)
{
lean_object* v___x_3688_; lean_object* v_traceState_3689_; lean_object* v_env_3690_; lean_object* v_nextMacroScope_3691_; lean_object* v_ngen_3692_; lean_object* v_auxDeclNGen_3693_; lean_object* v_cache_3694_; lean_object* v_recordedDeps_3695_; lean_object* v_messages_3696_; lean_object* v_infoState_3697_; lean_object* v_snapshotTasks_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3717_; 
lean_dec(v_snd_3667_);
lean_dec(v_fst_3666_);
lean_dec_ref(v_msg_3633_);
lean_dec_ref(v_tag_3629_);
lean_dec(v_cls_3627_);
v___x_3688_ = lean_st_ref_take(v___y_3648_);
v_traceState_3689_ = lean_ctor_get(v___x_3688_, 4);
v_env_3690_ = lean_ctor_get(v___x_3688_, 0);
v_nextMacroScope_3691_ = lean_ctor_get(v___x_3688_, 1);
v_ngen_3692_ = lean_ctor_get(v___x_3688_, 2);
v_auxDeclNGen_3693_ = lean_ctor_get(v___x_3688_, 3);
v_cache_3694_ = lean_ctor_get(v___x_3688_, 5);
v_recordedDeps_3695_ = lean_ctor_get(v___x_3688_, 6);
v_messages_3696_ = lean_ctor_get(v___x_3688_, 7);
v_infoState_3697_ = lean_ctor_get(v___x_3688_, 8);
v_snapshotTasks_3698_ = lean_ctor_get(v___x_3688_, 9);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3700_ = v___x_3688_;
v_isShared_3701_ = v_isSharedCheck_3717_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_snapshotTasks_3698_);
lean_inc(v_infoState_3697_);
lean_inc(v_messages_3696_);
lean_inc(v_recordedDeps_3695_);
lean_inc(v_cache_3694_);
lean_inc(v_traceState_3689_);
lean_inc(v_auxDeclNGen_3693_);
lean_inc(v_ngen_3692_);
lean_inc(v_nextMacroScope_3691_);
lean_inc(v_env_3690_);
lean_dec(v___x_3688_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3717_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
uint64_t v_tid_3702_; lean_object* v_traces_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3716_; 
v_tid_3702_ = lean_ctor_get_uint64(v_traceState_3689_, sizeof(void*)*1);
v_traces_3703_ = lean_ctor_get(v_traceState_3689_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_traceState_3689_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3705_ = v_traceState_3689_;
v_isShared_3706_ = v_isSharedCheck_3716_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_traces_3703_);
lean_dec(v_traceState_3689_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3716_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3707_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3632_, v_traces_3703_);
lean_dec_ref(v_traces_3703_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3707_);
v___x_3709_ = v___x_3705_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3707_);
lean_ctor_set_uint64(v_reuseFailAlloc_3715_, sizeof(void*)*1, v_tid_3702_);
v___x_3709_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3711_; 
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 4, v___x_3709_);
v___x_3711_ = v___x_3700_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_env_3690_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_nextMacroScope_3691_);
lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_ngen_3692_);
lean_ctor_set(v_reuseFailAlloc_3714_, 3, v_auxDeclNGen_3693_);
lean_ctor_set(v_reuseFailAlloc_3714_, 4, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3714_, 5, v_cache_3694_);
lean_ctor_set(v_reuseFailAlloc_3714_, 6, v_recordedDeps_3695_);
lean_ctor_set(v_reuseFailAlloc_3714_, 7, v_messages_3696_);
lean_ctor_set(v_reuseFailAlloc_3714_, 8, v_infoState_3697_);
lean_ctor_set(v_reuseFailAlloc_3714_, 9, v_snapshotTasks_3698_);
v___x_3711_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_st_ref_put(v___y_3648_, v___x_3711_);
v___x_3713_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_fst_3650_);
return v___x_3713_;
}
}
}
}
}
else
{
goto v___jp_3681_;
}
}
else
{
goto v___jp_3681_;
}
}
v___jp_3718_:
{
double v___x_3720_; double v___x_3721_; double v___x_3722_; uint8_t v___x_3723_; 
v___x_3720_ = lean_unbox_float(v_snd_3667_);
v___x_3721_ = lean_unbox_float(v_fst_3666_);
v___x_3722_ = lean_float_sub(v___x_3720_, v___x_3721_);
v___x_3723_ = lean_float_decLt(v___y_3719_, v___x_3722_);
v___y_3687_ = v___x_3723_;
goto v___jp_3686_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3627_ = stack[0].m_obj;
uint8_t v_collapsed_3628_ = stack[1].m_num;
lean_object* v_tag_3629_ = stack[2].m_obj;
lean_object* v_opts_3630_ = stack[3].m_obj;
uint8_t v_clsEnabled_3631_ = stack[4].m_num;
lean_object* v_oldTraces_3632_ = stack[5].m_obj;
lean_object* v_msg_3633_ = stack[6].m_obj;
lean_object* v_resStartStop_3634_ = stack[7].m_obj;
lean_object* v___y_3635_ = stack[8].m_obj;
lean_object* v___y_3636_ = stack[9].m_obj;
lean_object* v___y_3637_ = stack[10].m_obj;
lean_object* v___y_3638_ = stack[11].m_obj;
lean_object* v___y_3639_ = stack[12].m_obj;
lean_object* v___y_3640_ = stack[13].m_obj;
lean_object* v___y_3641_ = stack[14].m_obj;
lean_object* v___y_3642_ = stack[15].m_obj;
lean_object* v___y_3643_ = stack[16].m_obj;
lean_object* v___y_3644_ = stack[17].m_obj;
lean_object* v___y_3645_ = stack[18].m_obj;
lean_object* v___y_3646_ = stack[19].m_obj;
lean_object* v___y_3647_ = stack[20].m_obj;
lean_object* v___y_3648_ = stack[21].m_obj;
lean_object* v_res_3734_;
v_res_3734_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_3627_, v_collapsed_3628_, v_tag_3629_, v_opts_3630_, v_clsEnabled_3631_, v_oldTraces_3632_, v_msg_3633_, v_resStartStop_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
stack->m_obj
 = v_res_3734_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10___boxed(lean_object** _args){
lean_object* v_cls_3735_ = _args[0];
lean_object* v_collapsed_3736_ = _args[1];
lean_object* v_tag_3737_ = _args[2];
lean_object* v_opts_3738_ = _args[3];
lean_object* v_clsEnabled_3739_ = _args[4];
lean_object* v_oldTraces_3740_ = _args[5];
lean_object* v_msg_3741_ = _args[6];
lean_object* v_resStartStop_3742_ = _args[7];
lean_object* v___y_3743_ = _args[8];
lean_object* v___y_3744_ = _args[9];
lean_object* v___y_3745_ = _args[10];
lean_object* v___y_3746_ = _args[11];
lean_object* v___y_3747_ = _args[12];
lean_object* v___y_3748_ = _args[13];
lean_object* v___y_3749_ = _args[14];
lean_object* v___y_3750_ = _args[15];
lean_object* v___y_3751_ = _args[16];
lean_object* v___y_3752_ = _args[17];
lean_object* v___y_3753_ = _args[18];
lean_object* v___y_3754_ = _args[19];
lean_object* v___y_3755_ = _args[20];
lean_object* v___y_3756_ = _args[21];
lean_object* v___y_3757_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_3758_; uint8_t v_clsEnabled_boxed_3759_; lean_object* v_res_3760_; 
v_collapsed_boxed_3758_ = lean_unbox(v_collapsed_3736_);
v_clsEnabled_boxed_3759_ = lean_unbox(v_clsEnabled_3739_);
v_res_3760_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_3735_, v_collapsed_boxed_3758_, v_tag_3737_, v_opts_3738_, v_clsEnabled_boxed_3759_, v_oldTraces_3740_, v_msg_3741_, v_resStartStop_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec_ref(v_opts_3738_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(lean_object* v_aig_3761_){
_start:
{
lean_object* v_decls_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_decls_3762_ = lean_ctor_get(v_aig_3761_, 0);
v___x_3763_ = lean_array_get_size(v_decls_3762_);
v___x_3764_ = 0;
v___x_3765_ = lean_box(v___x_3764_);
v___x_3766_ = lean_mk_array(v___x_3763_, v___x_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1___boxed(lean_object* v_aig_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(v_aig_3767_);
lean_dec_ref(v_aig_3767_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(lean_object* v_aig_3771_){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___closed__0));
v___x_3773_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1_spec__1(v_aig_3771_);
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1___boxed(lean_object* v_aig_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(v_aig_3775_);
lean_dec_ref(v_aig_3775_);
return v_res_3776_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8(void){
_start:
{
lean_object* v_cls_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_cls_3788_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7));
v___x_3789_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
v___x_3790_ = l_Lean_Name_append(v___x_3789_, v_cls_3788_);
return v___x_3790_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9));
v___x_3796_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
v___x_3797_ = l_Lean_Name_append(v___x_3796_, v___x_3795_);
return v___x_3797_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0;
v___x_3802_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__1(v___x_3801_);
return v___x_3802_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3803_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__14);
v___x_3804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_takeBVState___redArg___closed__2);
v___x_3805_ = l_Std_Sat_AIG_empty___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__0;
v___x_3806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___x_3804_);
lean_ctor_set(v___x_3806_, 2, v___x_3803_);
return v___x_3806_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v_toCold_3989_; lean_object* v_options_3990_; lean_object* v_ref_3991_; lean_object* v_inheritedTraceOptions_3992_; uint8_t v_hasTrace_3993_; lean_object* v___f_3994_; lean_object* v___f_3995_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; uint8_t v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; uint8_t v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v_a_4024_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; uint8_t v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; uint8_t v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v_a_4061_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; uint8_t v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; uint8_t v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; uint8_t v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; uint8_t v___y_4166_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; uint8_t v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___f_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v_cls_4277_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; uint8_t v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; uint8_t v___y_4361_; uint8_t v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v_a_4376_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; uint8_t v___y_4404_; uint8_t v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v_a_4419_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; uint8_t v___y_4443_; uint8_t v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; uint8_t v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; uint8_t v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4608_; lean_object* v___y_4609_; lean_object* v___y_4610_; uint8_t v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; uint8_t v___y_4678_; lean_object* v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; uint8_t v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v___y_4694_; lean_object* v___y_4695_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v_a_4698_; lean_object* v___y_4708_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; uint8_t v___y_4714_; lean_object* v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; uint8_t v___y_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4731_; lean_object* v___y_4732_; lean_object* v___y_4733_; lean_object* v_a_4734_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; uint8_t v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; uint8_t v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4761_; lean_object* v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4768_; lean_object* v___y_4769_; lean_object* v___y_4770_; lean_object* v___y_4771_; lean_object* v___y_4772_; lean_object* v_ctx_4830_; lean_object* v___y_4831_; lean_object* v___y_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4836_; lean_object* v___y_4837_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___y_4840_; lean_object* v___y_4841_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; 
v_toCold_3989_ = lean_ctor_get(v_a_3820_, 0);
v_options_3990_ = lean_ctor_get(v_toCold_3989_, 2);
v_ref_3991_ = lean_ctor_get(v_a_3820_, 2);
v_inheritedTraceOptions_3992_ = lean_ctor_get(v_toCold_3989_, 11);
v_hasTrace_3993_ = lean_ctor_get_uint8(v_options_3990_, sizeof(void*)*1);
v___f_3994_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__0));
v___f_3995_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__1));
v___f_4273_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__2));
v___x_4274_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__3));
v___x_4275_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__4));
v___x_4276_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__5));
v_cls_4277_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__7));
if (v_hasTrace_3993_ == 0)
{
lean_object* v_tacticContext_4900_; 
v_tacticContext_4900_ = lean_ctor_get(v_a_3808_, 2);
v_ctx_4830_ = v_tacticContext_4900_;
v___y_4831_ = v_a_3808_;
v___y_4832_ = v_a_3809_;
v___y_4833_ = v_a_3810_;
v___y_4834_ = v_a_3811_;
v___y_4835_ = v_a_3812_;
v___y_4836_ = v_a_3813_;
v___y_4837_ = v_a_3814_;
v___y_4838_ = v_a_3815_;
v___y_4839_ = v_a_3816_;
v___y_4840_ = v_a_3817_;
v___y_4841_ = v_a_3818_;
v___y_4842_ = v_a_3819_;
v___y_4843_ = v_a_3820_;
v___y_4844_ = v_a_3821_;
goto v___jp_4829_;
}
else
{
lean_object* v___f_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; uint8_t v___x_4904_; lean_object* v___y_4906_; lean_object* v___y_4907_; lean_object* v_a_4908_; lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v_a_4920_; lean_object* v___y_4923_; lean_object* v___y_4924_; lean_object* v___y_4925_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___y_4939_; uint8_t v___y_4940_; lean_object* v___y_4941_; lean_object* v___y_4942_; lean_object* v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4945_; lean_object* v_a_4946_; lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; uint8_t v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; uint8_t v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; uint8_t v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4996_; uint8_t v___y_4997_; lean_object* v___y_4998_; lean_object* v___y_4999_; lean_object* v_a_5000_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5012_; lean_object* v___y_5013_; uint8_t v___y_5014_; lean_object* v___y_5015_; lean_object* v___y_5016_; uint8_t v___y_5017_; lean_object* v___y_5018_; lean_object* v___y_5019_; uint8_t v___y_5020_; lean_object* v___y_5021_; lean_object* v___y_5022_; lean_object* v___y_5023_; lean_object* v_a_5024_; lean_object* v___y_5037_; lean_object* v___y_5038_; lean_object* v___y_5039_; lean_object* v___y_5040_; uint8_t v___y_5041_; lean_object* v___y_5042_; lean_object* v___y_5043_; uint8_t v___y_5044_; lean_object* v___y_5045_; uint8_t v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5049_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v_a_5112_; lean_object* v___y_5125_; lean_object* v___y_5126_; lean_object* v_a_5127_; lean_object* v___y_5130_; lean_object* v___y_5131_; lean_object* v___y_5132_; lean_object* v___y_5143_; lean_object* v___y_5144_; lean_object* v___y_5145_; lean_object* v___y_5146_; lean_object* v___y_5147_; uint8_t v___y_5148_; lean_object* v___y_5149_; lean_object* v___y_5150_; lean_object* v___y_5151_; lean_object* v___y_5152_; lean_object* v_a_5153_; lean_object* v___y_5179_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; uint8_t v___y_5184_; lean_object* v___y_5185_; lean_object* v___y_5186_; lean_object* v___y_5187_; lean_object* v___y_5188_; lean_object* v___y_5189_; lean_object* v___y_5193_; lean_object* v___y_5194_; lean_object* v___y_5195_; lean_object* v___y_5196_; lean_object* v___y_5197_; uint8_t v___y_5198_; lean_object* v___y_5199_; lean_object* v___y_5200_; lean_object* v___y_5201_; lean_object* v___y_5202_; uint8_t v___y_5203_; lean_object* v___y_5204_; lean_object* v___y_5205_; lean_object* v_a_5206_; lean_object* v___y_5216_; lean_object* v___y_5217_; lean_object* v___y_5218_; lean_object* v___y_5219_; lean_object* v___y_5220_; uint8_t v___y_5221_; lean_object* v___y_5222_; lean_object* v___y_5223_; lean_object* v___y_5224_; uint8_t v___y_5225_; lean_object* v___y_5226_; lean_object* v___y_5227_; lean_object* v___y_5228_; lean_object* v_a_5229_; lean_object* v___y_5242_; lean_object* v___y_5243_; lean_object* v___y_5244_; lean_object* v___y_5245_; lean_object* v___y_5246_; uint8_t v___y_5247_; lean_object* v___y_5248_; lean_object* v___y_5249_; lean_object* v___y_5250_; lean_object* v___y_5251_; uint8_t v___y_5252_; uint8_t v___y_5253_; lean_object* v___y_5254_; 
v___f_4901_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__16));
v___x_4902_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
v___x_4903_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4904_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3992_, v_options_3990_, v___x_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_5437_; uint8_t v___x_5438_; 
v___x_5437_ = l_Lean_trace_profiler;
v___x_5438_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3990_, v___x_5437_);
if (v___x_5438_ == 0)
{
lean_object* v_tacticContext_5439_; 
v_tacticContext_5439_ = lean_ctor_get(v_a_3808_, 2);
v_ctx_4830_ = v_tacticContext_5439_;
v___y_4831_ = v_a_3808_;
v___y_4832_ = v_a_3809_;
v___y_4833_ = v_a_3810_;
v___y_4834_ = v_a_3811_;
v___y_4835_ = v_a_3812_;
v___y_4836_ = v_a_3813_;
v___y_4837_ = v_a_3814_;
v___y_4838_ = v_a_3815_;
v___y_4839_ = v_a_3816_;
v___y_4840_ = v_a_3817_;
v___y_4841_ = v_a_3818_;
v___y_4842_ = v_a_3819_;
v___y_4843_ = v_a_3820_;
v___y_4844_ = v_a_3821_;
goto v___jp_4829_;
}
else
{
goto v___jp_5314_;
}
}
else
{
goto v___jp_5314_;
}
v___jp_4905_:
{
lean_object* v___x_4909_; double v___x_4910_; double v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4909_ = lean_io_get_num_heartbeats();
v___x_4910_ = lean_float_of_nat(v___y_4906_);
v___x_4911_ = lean_float_of_nat(v___x_4909_);
v___x_4912_ = lean_box_float(v___x_4910_);
v___x_4913_ = lean_box_float(v___x_4911_);
v___x_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4912_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
v___x_4915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4915_, 0, v_a_4908_);
lean_ctor_set(v___x_4915_, 1, v___x_4914_);
v___x_4916_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_4277_, v_hasTrace_3993_, v___x_4902_, v_options_3990_, v___x_4904_, v___y_4907_, v___f_4901_, v___x_4915_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
return v___x_4916_;
}
v___jp_4917_:
{
lean_object* v___x_4921_; 
v___x_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4921_, 0, v_a_4920_);
v___y_4906_ = v___y_4918_;
v___y_4907_ = v___y_4919_;
v_a_4908_ = v___x_4921_;
goto v___jp_4905_;
}
v___jp_4922_:
{
if (lean_obj_tag(v___y_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
v_a_4926_ = lean_ctor_get(v___y_4925_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___y_4925_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___y_4925_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___y_4925_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
lean_ctor_set_tag(v___x_4928_, 1);
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
v___y_4906_ = v___y_4923_;
v___y_4907_ = v___y_4924_;
v_a_4908_ = v___x_4931_;
goto v___jp_4905_;
}
}
}
else
{
lean_object* v_a_4934_; 
v_a_4934_ = lean_ctor_get(v___y_4925_, 0);
lean_inc(v_a_4934_);
lean_dec_ref_known(v___y_4925_, 1);
v___y_4918_ = v___y_4923_;
v___y_4919_ = v___y_4924_;
v_a_4920_ = v_a_4934_;
goto v___jp_4917_;
}
}
v___jp_4935_:
{
lean_object* v_result_4947_; lean_object* v_aig_4948_; lean_object* v_cache_4949_; lean_object* v_ref_4950_; lean_object* v_decls_4951_; lean_object* v___x_4952_; 
v_result_4947_ = lean_ctor_get(v_a_4946_, 0);
lean_inc_ref(v_result_4947_);
v_aig_4948_ = lean_ctor_get(v_result_4947_, 0);
lean_inc_ref(v_aig_4948_);
v_cache_4949_ = lean_ctor_get(v_a_4946_, 1);
lean_inc_ref(v_cache_4949_);
lean_dec_ref(v_a_4946_);
v_ref_4950_ = lean_ctor_get(v_result_4947_, 1);
lean_inc_ref(v_ref_4950_);
v_decls_4951_ = lean_ctor_get(v_aig_4948_, 0);
v___x_4952_ = lean_array_get_size(v_decls_4951_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
lean_dec(v___y_4944_);
v___x_4953_ = lean_box(0);
lean_inc_ref(v___y_4941_);
lean_inc_ref(v___y_4939_);
v___x_4954_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v___y_4939_, v___x_4952_, v_aig_4948_, v___y_4942_, v___y_4938_, v___y_4941_, v___y_4940_, v___x_4902_, v___f_3995_, v___y_4937_, v_cache_4949_, v_ref_4950_, v_cls_4277_, v___f_3994_, v___y_4936_, v___x_4274_, v_result_4947_, v___x_4275_, v___x_4276_, v___x_4953_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
lean_dec_ref(v_ref_4950_);
v___y_4923_ = v___y_4943_;
v___y_4924_ = v___y_4945_;
v___y_4925_ = v___x_4954_;
goto v___jp_4922_;
}
else
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4955_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_4956_ = l_Nat_reprFast(v___x_4952_);
v___x_4957_ = lean_string_append(v___x_4955_, v___x_4956_);
lean_dec_ref(v___x_4956_);
v___x_4958_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_4959_ = lean_string_append(v___x_4957_, v___x_4958_);
v___x_4960_ = lean_nat_sub(v___x_4952_, v___y_4944_);
lean_dec(v___y_4944_);
v___x_4961_ = l_Nat_reprFast(v___x_4960_);
v___x_4962_ = lean_string_append(v___x_4959_, v___x_4961_);
lean_dec_ref(v___x_4961_);
v___x_4963_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_4964_ = lean_string_append(v___x_4962_, v___x_4963_);
v___x_4965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4964_);
v___x_4966_ = l_Lean_MessageData_ofFormat(v___x_4965_);
v___x_4967_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4277_, v___x_4966_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4969_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4968_);
lean_dec_ref_known(v___x_4967_, 1);
lean_inc_ref(v___y_4941_);
lean_inc_ref(v___y_4939_);
v___x_4969_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__11(v___y_4939_, v___x_4952_, v_aig_4948_, v___y_4942_, v___y_4938_, v___y_4941_, v___y_4940_, v___x_4902_, v___f_3995_, v___y_4937_, v_cache_4949_, v_ref_4950_, v_cls_4277_, v___f_3994_, v___y_4936_, v___x_4274_, v_result_4947_, v___x_4275_, v___x_4276_, v_a_4968_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
lean_dec_ref(v_ref_4950_);
v___y_4923_ = v___y_4943_;
v___y_4924_ = v___y_4945_;
v___y_4925_ = v___x_4969_;
goto v___jp_4922_;
}
else
{
lean_object* v_a_4970_; 
lean_dec_ref(v_ref_4950_);
lean_dec_ref(v_cache_4949_);
lean_dec_ref(v_aig_4948_);
lean_dec_ref(v_result_4947_);
lean_dec(v___y_4942_);
lean_dec(v___y_4938_);
lean_dec_ref(v___y_4936_);
v_a_4970_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4970_);
lean_dec_ref_known(v___x_4967_, 1);
v___y_4918_ = v___y_4943_;
v___y_4919_ = v___y_4945_;
v_a_4920_ = v_a_4970_;
goto v___jp_4917_;
}
}
}
v___jp_4971_:
{
if (lean_obj_tag(v___y_4982_) == 0)
{
lean_object* v_a_4983_; 
v_a_4983_ = lean_ctor_get(v___y_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___y_4982_, 1);
v___y_4936_ = v___y_4972_;
v___y_4937_ = v___y_4974_;
v___y_4938_ = v___y_4973_;
v___y_4939_ = v___y_4975_;
v___y_4940_ = v___y_4976_;
v___y_4941_ = v___y_4977_;
v___y_4942_ = v___y_4978_;
v___y_4943_ = v___y_4979_;
v___y_4944_ = v___y_4981_;
v___y_4945_ = v___y_4980_;
v_a_4946_ = v_a_4983_;
goto v___jp_4935_;
}
else
{
lean_object* v_a_4984_; 
lean_dec(v___y_4981_);
lean_dec(v___y_4978_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
v_a_4984_ = lean_ctor_get(v___y_4982_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v___y_4982_, 1);
v___y_4918_ = v___y_4979_;
v___y_4919_ = v___y_4980_;
v_a_4920_ = v_a_4984_;
goto v___jp_4917_;
}
}
v___jp_4985_:
{
lean_object* v___x_5001_; double v___x_5002_; double v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5001_ = lean_io_get_num_heartbeats();
v___x_5002_ = lean_float_of_nat(v___y_4995_);
v___x_5003_ = lean_float_of_nat(v___x_5001_);
v___x_5004_ = lean_box_float(v___x_5002_);
v___x_5005_ = lean_box_float(v___x_5003_);
v___x_5006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5004_);
lean_ctor_set(v___x_5006_, 1, v___x_5005_);
v___x_5007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5007_, 0, v_a_5000_);
lean_ctor_set(v___x_5007_, 1, v___x_5006_);
v___x_5008_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4277_, v___y_4997_, v___x_4902_, v_options_3990_, v___y_4993_, v___y_4996_, v___f_4273_, v___x_5007_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
v___y_4972_ = v___y_4986_;
v___y_4973_ = v___y_4988_;
v___y_4974_ = v___y_4987_;
v___y_4975_ = v___y_4989_;
v___y_4976_ = v___y_4990_;
v___y_4977_ = v___y_4991_;
v___y_4978_ = v___y_4992_;
v___y_4979_ = v___y_4994_;
v___y_4980_ = v___y_4999_;
v___y_4981_ = v___y_4998_;
v___y_4982_ = v___x_5008_;
goto v___jp_4971_;
}
v___jp_5009_:
{
lean_object* v___x_5025_; double v___x_5026_; double v___x_5027_; double v___x_5028_; double v___x_5029_; double v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5025_ = lean_io_mono_nanos_now();
v___x_5026_ = lean_float_of_nat(v___y_5021_);
v___x_5027_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_5028_ = lean_float_div(v___x_5026_, v___x_5027_);
v___x_5029_ = lean_float_of_nat(v___x_5025_);
v___x_5030_ = lean_float_div(v___x_5029_, v___x_5027_);
v___x_5031_ = lean_box_float(v___x_5028_);
v___x_5032_ = lean_box_float(v___x_5030_);
v___x_5033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5031_);
lean_ctor_set(v___x_5033_, 1, v___x_5032_);
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v_a_5024_);
lean_ctor_set(v___x_5034_, 1, v___x_5033_);
v___x_5035_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4277_, v___y_5020_, v___x_4902_, v_options_3990_, v___y_5017_, v___y_5019_, v___f_4273_, v___x_5034_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
v___y_4972_ = v___y_5010_;
v___y_4973_ = v___y_5012_;
v___y_4974_ = v___y_5011_;
v___y_4975_ = v___y_5013_;
v___y_4976_ = v___y_5014_;
v___y_4977_ = v___y_5015_;
v___y_4978_ = v___y_5016_;
v___y_4979_ = v___y_5018_;
v___y_4980_ = v___y_5023_;
v___y_4981_ = v___y_5022_;
v___y_4982_ = v___x_5035_;
goto v___jp_4971_;
}
v___jp_5036_:
{
lean_object* v___x_5050_; 
v___x_5050_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3821_);
if (v___y_5046_ == 0)
{
lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5079_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5053_ = v___x_5050_;
v_isShared_5054_ = v_isSharedCheck_5079_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_dec(v___x_5050_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5079_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5055_ = lean_io_mono_nanos_now();
v___x_5056_ = l_IO_lazyPure___redArg(v___y_5047_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v_a_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5064_; 
lean_del_object(v___x_5053_);
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5059_ = v___x_5056_;
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_a_5057_);
lean_dec(v___x_5056_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v___x_5062_; 
if (v_isShared_5060_ == 0)
{
lean_ctor_set_tag(v___x_5059_, 1);
v___x_5062_ = v___x_5059_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
v___y_5010_ = v___y_5037_;
v___y_5011_ = v___y_5039_;
v___y_5012_ = v___y_5038_;
v___y_5013_ = v___y_5040_;
v___y_5014_ = v___y_5041_;
v___y_5015_ = v___y_5042_;
v___y_5016_ = v___y_5043_;
v___y_5017_ = v___y_5044_;
v___y_5018_ = v___y_5045_;
v___y_5019_ = v_a_5051_;
v___y_5020_ = v___y_5046_;
v___y_5021_ = v___x_5055_;
v___y_5022_ = v___y_5049_;
v___y_5023_ = v___y_5048_;
v_a_5024_ = v___x_5062_;
goto v___jp_5009_;
}
}
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5078_; 
v_a_5065_ = lean_ctor_get(v___x_5056_, 0);
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5067_ = v___x_5056_;
v_isShared_5068_ = v_isSharedCheck_5078_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_5056_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5078_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5069_; lean_object* v___x_5071_; 
v___x_5069_ = lean_io_error_to_string(v_a_5065_);
if (v_isShared_5068_ == 0)
{
lean_ctor_set_tag(v___x_5067_, 3);
lean_ctor_set(v___x_5067_, 0, v___x_5069_);
v___x_5071_ = v___x_5067_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5072_ = l_Lean_MessageData_ofFormat(v___x_5071_);
lean_inc(v_ref_3991_);
v___x_5073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5073_, 0, v_ref_3991_);
lean_ctor_set(v___x_5073_, 1, v___x_5072_);
if (v_isShared_5054_ == 0)
{
lean_ctor_set(v___x_5053_, 0, v___x_5073_);
v___x_5075_ = v___x_5053_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5073_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
v___y_5010_ = v___y_5037_;
v___y_5011_ = v___y_5039_;
v___y_5012_ = v___y_5038_;
v___y_5013_ = v___y_5040_;
v___y_5014_ = v___y_5041_;
v___y_5015_ = v___y_5042_;
v___y_5016_ = v___y_5043_;
v___y_5017_ = v___y_5044_;
v___y_5018_ = v___y_5045_;
v___y_5019_ = v_a_5051_;
v___y_5020_ = v___y_5046_;
v___y_5021_ = v___x_5055_;
v___y_5022_ = v___y_5049_;
v___y_5023_ = v___y_5048_;
v_a_5024_ = v___x_5075_;
goto v___jp_5009_;
}
}
}
}
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5108_; 
v_a_5080_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5082_ = v___x_5050_;
v_isShared_5083_ = v_isSharedCheck_5108_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5050_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5108_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = lean_io_get_num_heartbeats();
v___x_5085_ = l_IO_lazyPure___redArg(v___y_5047_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
lean_del_object(v___x_5082_);
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5085_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5085_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
lean_ctor_set_tag(v___x_5088_, 1);
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
v___y_4986_ = v___y_5037_;
v___y_4987_ = v___y_5039_;
v___y_4988_ = v___y_5038_;
v___y_4989_ = v___y_5040_;
v___y_4990_ = v___y_5041_;
v___y_4991_ = v___y_5042_;
v___y_4992_ = v___y_5043_;
v___y_4993_ = v___y_5044_;
v___y_4994_ = v___y_5045_;
v___y_4995_ = v___x_5084_;
v___y_4996_ = v_a_5080_;
v___y_4997_ = v___y_5046_;
v___y_4998_ = v___y_5049_;
v___y_4999_ = v___y_5048_;
v_a_5000_ = v___x_5091_;
goto v___jp_4985_;
}
}
}
else
{
lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5107_; 
v_a_5094_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5096_ = v___x_5085_;
v_isShared_5097_ = v_isSharedCheck_5107_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5085_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5107_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5098_; lean_object* v___x_5100_; 
v___x_5098_ = lean_io_error_to_string(v_a_5094_);
if (v_isShared_5097_ == 0)
{
lean_ctor_set_tag(v___x_5096_, 3);
lean_ctor_set(v___x_5096_, 0, v___x_5098_);
v___x_5100_ = v___x_5096_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___x_5098_);
v___x_5100_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5104_; 
v___x_5101_ = l_Lean_MessageData_ofFormat(v___x_5100_);
lean_inc(v_ref_3991_);
v___x_5102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5102_, 0, v_ref_3991_);
lean_ctor_set(v___x_5102_, 1, v___x_5101_);
if (v_isShared_5083_ == 0)
{
lean_ctor_set(v___x_5082_, 0, v___x_5102_);
v___x_5104_ = v___x_5082_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v___x_5102_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
v___y_4986_ = v___y_5037_;
v___y_4987_ = v___y_5039_;
v___y_4988_ = v___y_5038_;
v___y_4989_ = v___y_5040_;
v___y_4990_ = v___y_5041_;
v___y_4991_ = v___y_5042_;
v___y_4992_ = v___y_5043_;
v___y_4993_ = v___y_5044_;
v___y_4994_ = v___y_5045_;
v___y_4995_ = v___x_5084_;
v___y_4996_ = v_a_5080_;
v___y_4997_ = v___y_5046_;
v___y_4998_ = v___y_5049_;
v___y_4999_ = v___y_5048_;
v_a_5000_ = v___x_5104_;
goto v___jp_4985_;
}
}
}
}
}
}
}
v___jp_5109_:
{
lean_object* v___x_5113_; double v___x_5114_; double v___x_5115_; double v___x_5116_; double v___x_5117_; double v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
v___x_5113_ = lean_io_mono_nanos_now();
v___x_5114_ = lean_float_of_nat(v___y_5110_);
v___x_5115_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_5116_ = lean_float_div(v___x_5114_, v___x_5115_);
v___x_5117_ = lean_float_of_nat(v___x_5113_);
v___x_5118_ = lean_float_div(v___x_5117_, v___x_5115_);
v___x_5119_ = lean_box_float(v___x_5116_);
v___x_5120_ = lean_box_float(v___x_5118_);
v___x_5121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5121_, 0, v___x_5119_);
lean_ctor_set(v___x_5121_, 1, v___x_5120_);
v___x_5122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5122_, 0, v_a_5112_);
lean_ctor_set(v___x_5122_, 1, v___x_5121_);
v___x_5123_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__10(v_cls_4277_, v_hasTrace_3993_, v___x_4902_, v_options_3990_, v___x_4904_, v___y_5111_, v___f_4901_, v___x_5122_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
return v___x_5123_;
}
v___jp_5124_:
{
lean_object* v___x_5128_; 
v___x_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5128_, 0, v_a_5127_);
v___y_5110_ = v___y_5125_;
v___y_5111_ = v___y_5126_;
v_a_5112_ = v___x_5128_;
goto v___jp_5109_;
}
v___jp_5129_:
{
if (lean_obj_tag(v___y_5132_) == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5140_; 
v_a_5133_ = lean_ctor_get(v___y_5132_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___y_5132_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___y_5132_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___y_5132_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5138_; 
if (v_isShared_5136_ == 0)
{
lean_ctor_set_tag(v___x_5135_, 1);
v___x_5138_ = v___x_5135_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
v___y_5110_ = v___y_5130_;
v___y_5111_ = v___y_5131_;
v_a_5112_ = v___x_5138_;
goto v___jp_5109_;
}
}
}
else
{
lean_object* v_a_5141_; 
v_a_5141_ = lean_ctor_get(v___y_5132_, 0);
lean_inc(v_a_5141_);
lean_dec_ref_known(v___y_5132_, 1);
v___y_5125_ = v___y_5130_;
v___y_5126_ = v___y_5131_;
v_a_5127_ = v_a_5141_;
goto v___jp_5124_;
}
}
v___jp_5142_:
{
lean_object* v_result_5154_; lean_object* v_aig_5155_; lean_object* v_cache_5156_; lean_object* v_ref_5157_; lean_object* v_decls_5158_; lean_object* v___x_5159_; 
v_result_5154_ = lean_ctor_get(v_a_5153_, 0);
lean_inc_ref(v_result_5154_);
v_aig_5155_ = lean_ctor_get(v_result_5154_, 0);
lean_inc_ref(v_aig_5155_);
v_cache_5156_ = lean_ctor_get(v_a_5153_, 1);
lean_inc_ref(v_cache_5156_);
lean_dec_ref(v_a_5153_);
v_ref_5157_ = lean_ctor_get(v_result_5154_, 1);
lean_inc_ref(v_ref_5157_);
v_decls_5158_ = lean_ctor_get(v_aig_5155_, 0);
v___x_5159_ = lean_array_get_size(v_decls_5158_);
if (v___x_4904_ == 0)
{
lean_object* v___x_5160_; lean_object* v___x_5161_; 
lean_dec(v___y_5151_);
v___x_5160_ = lean_box(0);
lean_inc_ref(v___y_5146_);
lean_inc_ref(v___y_5149_);
v___x_5161_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v___y_5149_, v___x_5159_, v_aig_5155_, v___y_5147_, v___y_5144_, v___y_5146_, v_hasTrace_3993_, v___x_4902_, v___f_3995_, v___y_5143_, v_cache_5156_, v_ref_5157_, v___y_5148_, v_cls_4277_, v___f_3994_, v___y_5145_, v___x_4274_, v_result_5154_, v___x_4275_, v___x_4276_, v___x_5160_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
lean_dec_ref(v_ref_5157_);
v___y_5130_ = v___y_5150_;
v___y_5131_ = v___y_5152_;
v___y_5132_ = v___x_5161_;
goto v___jp_5129_;
}
else
{
lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
v___x_5162_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_5163_ = l_Nat_reprFast(v___x_5159_);
v___x_5164_ = lean_string_append(v___x_5162_, v___x_5163_);
lean_dec_ref(v___x_5163_);
v___x_5165_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_5166_ = lean_string_append(v___x_5164_, v___x_5165_);
v___x_5167_ = lean_nat_sub(v___x_5159_, v___y_5151_);
lean_dec(v___y_5151_);
v___x_5168_ = l_Nat_reprFast(v___x_5167_);
v___x_5169_ = lean_string_append(v___x_5166_, v___x_5168_);
lean_dec_ref(v___x_5168_);
v___x_5170_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_5171_ = lean_string_append(v___x_5169_, v___x_5170_);
v___x_5172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5171_);
v___x_5173_ = l_Lean_MessageData_ofFormat(v___x_5172_);
v___x_5174_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4277_, v___x_5173_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v___x_5176_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc(v_a_5175_);
lean_dec_ref_known(v___x_5174_, 1);
lean_inc_ref(v___y_5146_);
lean_inc_ref(v___y_5149_);
v___x_5176_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16(v___y_5149_, v___x_5159_, v_aig_5155_, v___y_5147_, v___y_5144_, v___y_5146_, v_hasTrace_3993_, v___x_4902_, v___f_3995_, v___y_5143_, v_cache_5156_, v_ref_5157_, v___y_5148_, v_cls_4277_, v___f_3994_, v___y_5145_, v___x_4274_, v_result_5154_, v___x_4275_, v___x_4276_, v_a_5175_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
lean_dec_ref(v_ref_5157_);
v___y_5130_ = v___y_5150_;
v___y_5131_ = v___y_5152_;
v___y_5132_ = v___x_5176_;
goto v___jp_5129_;
}
else
{
lean_object* v_a_5177_; 
lean_dec_ref(v_ref_5157_);
lean_dec_ref(v_cache_5156_);
lean_dec_ref(v_aig_5155_);
lean_dec_ref(v_result_5154_);
lean_dec(v___y_5147_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
v_a_5177_ = lean_ctor_get(v___x_5174_, 0);
lean_inc(v_a_5177_);
lean_dec_ref_known(v___x_5174_, 1);
v___y_5125_ = v___y_5150_;
v___y_5126_ = v___y_5152_;
v_a_5127_ = v_a_5177_;
goto v___jp_5124_;
}
}
}
v___jp_5178_:
{
if (lean_obj_tag(v___y_5189_) == 0)
{
lean_object* v_a_5190_; 
v_a_5190_ = lean_ctor_get(v___y_5189_, 0);
lean_inc(v_a_5190_);
lean_dec_ref_known(v___y_5189_, 1);
v___y_5143_ = v___y_5179_;
v___y_5144_ = v___y_5180_;
v___y_5145_ = v___y_5181_;
v___y_5146_ = v___y_5183_;
v___y_5147_ = v___y_5182_;
v___y_5148_ = v___y_5184_;
v___y_5149_ = v___y_5185_;
v___y_5150_ = v___y_5186_;
v___y_5151_ = v___y_5187_;
v___y_5152_ = v___y_5188_;
v_a_5153_ = v_a_5190_;
goto v___jp_5142_;
}
else
{
lean_object* v_a_5191_; 
lean_dec(v___y_5187_);
lean_dec(v___y_5182_);
lean_dec_ref(v___y_5181_);
lean_dec(v___y_5180_);
v_a_5191_ = lean_ctor_get(v___y_5189_, 0);
lean_inc(v_a_5191_);
lean_dec_ref_known(v___y_5189_, 1);
v___y_5125_ = v___y_5186_;
v___y_5126_ = v___y_5188_;
v_a_5127_ = v_a_5191_;
goto v___jp_5124_;
}
}
v___jp_5192_:
{
lean_object* v___x_5207_; double v___x_5208_; double v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
v___x_5207_ = lean_io_get_num_heartbeats();
v___x_5208_ = lean_float_of_nat(v___y_5202_);
v___x_5209_ = lean_float_of_nat(v___x_5207_);
v___x_5210_ = lean_box_float(v___x_5208_);
v___x_5211_ = lean_box_float(v___x_5209_);
v___x_5212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5210_);
lean_ctor_set(v___x_5212_, 1, v___x_5211_);
v___x_5213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5213_, 0, v_a_5206_);
lean_ctor_set(v___x_5213_, 1, v___x_5212_);
v___x_5214_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4277_, v_hasTrace_3993_, v___x_4902_, v_options_3990_, v___y_5203_, v___y_5204_, v___f_4273_, v___x_5213_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
v___y_5179_ = v___y_5193_;
v___y_5180_ = v___y_5194_;
v___y_5181_ = v___y_5195_;
v___y_5182_ = v___y_5197_;
v___y_5183_ = v___y_5196_;
v___y_5184_ = v___y_5198_;
v___y_5185_ = v___y_5199_;
v___y_5186_ = v___y_5200_;
v___y_5187_ = v___y_5201_;
v___y_5188_ = v___y_5205_;
v___y_5189_ = v___x_5214_;
goto v___jp_5178_;
}
v___jp_5215_:
{
lean_object* v___x_5230_; double v___x_5231_; double v___x_5232_; double v___x_5233_; double v___x_5234_; double v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; 
v___x_5230_ = lean_io_mono_nanos_now();
v___x_5231_ = lean_float_of_nat(v___y_5226_);
v___x_5232_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_5233_ = lean_float_div(v___x_5231_, v___x_5232_);
v___x_5234_ = lean_float_of_nat(v___x_5230_);
v___x_5235_ = lean_float_div(v___x_5234_, v___x_5232_);
v___x_5236_ = lean_box_float(v___x_5233_);
v___x_5237_ = lean_box_float(v___x_5235_);
v___x_5238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5236_);
lean_ctor_set(v___x_5238_, 1, v___x_5237_);
v___x_5239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5239_, 0, v_a_5229_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
v___x_5240_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4277_, v_hasTrace_3993_, v___x_4902_, v_options_3990_, v___y_5225_, v___y_5227_, v___f_4273_, v___x_5239_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
v___y_5179_ = v___y_5216_;
v___y_5180_ = v___y_5217_;
v___y_5181_ = v___y_5218_;
v___y_5182_ = v___y_5220_;
v___y_5183_ = v___y_5219_;
v___y_5184_ = v___y_5221_;
v___y_5185_ = v___y_5222_;
v___y_5186_ = v___y_5223_;
v___y_5187_ = v___y_5224_;
v___y_5188_ = v___y_5228_;
v___y_5189_ = v___x_5240_;
goto v___jp_5178_;
}
v___jp_5241_:
{
lean_object* v___x_5255_; 
v___x_5255_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3821_);
if (v___y_5253_ == 0)
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5284_; 
v_a_5256_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5258_ = v___x_5255_;
v_isShared_5259_ = v_isSharedCheck_5284_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5255_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5284_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5260_; lean_object* v___x_5261_; 
v___x_5260_ = lean_io_mono_nanos_now();
v___x_5261_ = l_IO_lazyPure___redArg(v___y_5249_);
if (lean_obj_tag(v___x_5261_) == 0)
{
lean_object* v_a_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5269_; 
lean_del_object(v___x_5258_);
v_a_5262_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5264_ = v___x_5261_;
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_a_5262_);
lean_dec(v___x_5261_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
lean_ctor_set_tag(v___x_5264_, 1);
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_a_5262_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
v___y_5216_ = v___y_5242_;
v___y_5217_ = v___y_5243_;
v___y_5218_ = v___y_5244_;
v___y_5219_ = v___y_5246_;
v___y_5220_ = v___y_5245_;
v___y_5221_ = v___y_5247_;
v___y_5222_ = v___y_5248_;
v___y_5223_ = v___y_5250_;
v___y_5224_ = v___y_5251_;
v___y_5225_ = v___y_5252_;
v___y_5226_ = v___x_5260_;
v___y_5227_ = v_a_5256_;
v___y_5228_ = v___y_5254_;
v_a_5229_ = v___x_5267_;
goto v___jp_5215_;
}
}
}
else
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5283_; 
v_a_5270_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5283_ == 0)
{
v___x_5272_ = v___x_5261_;
v_isShared_5273_ = v_isSharedCheck_5283_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v___x_5261_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5283_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5274_; lean_object* v___x_5276_; 
v___x_5274_ = lean_io_error_to_string(v_a_5270_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set_tag(v___x_5272_, 3);
lean_ctor_set(v___x_5272_, 0, v___x_5274_);
v___x_5276_ = v___x_5272_;
goto v_reusejp_5275_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v___x_5274_);
v___x_5276_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5275_;
}
v_reusejp_5275_:
{
lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5280_; 
v___x_5277_ = l_Lean_MessageData_ofFormat(v___x_5276_);
lean_inc(v_ref_3991_);
v___x_5278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5278_, 0, v_ref_3991_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set(v___x_5258_, 0, v___x_5278_);
v___x_5280_ = v___x_5258_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5278_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
v___y_5216_ = v___y_5242_;
v___y_5217_ = v___y_5243_;
v___y_5218_ = v___y_5244_;
v___y_5219_ = v___y_5246_;
v___y_5220_ = v___y_5245_;
v___y_5221_ = v___y_5247_;
v___y_5222_ = v___y_5248_;
v___y_5223_ = v___y_5250_;
v___y_5224_ = v___y_5251_;
v___y_5225_ = v___y_5252_;
v___y_5226_ = v___x_5260_;
v___y_5227_ = v_a_5256_;
v___y_5228_ = v___y_5254_;
v_a_5229_ = v___x_5280_;
goto v___jp_5215_;
}
}
}
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5313_; 
v_a_5285_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5287_ = v___x_5255_;
v_isShared_5288_ = v_isSharedCheck_5313_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5255_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5313_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5289_ = lean_io_get_num_heartbeats();
v___x_5290_ = l_IO_lazyPure___redArg(v___y_5249_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5298_; 
lean_del_object(v___x_5287_);
v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5293_ = v___x_5290_;
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5290_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5296_; 
if (v_isShared_5294_ == 0)
{
lean_ctor_set_tag(v___x_5293_, 1);
v___x_5296_ = v___x_5293_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
v___y_5193_ = v___y_5242_;
v___y_5194_ = v___y_5243_;
v___y_5195_ = v___y_5244_;
v___y_5196_ = v___y_5246_;
v___y_5197_ = v___y_5245_;
v___y_5198_ = v___y_5247_;
v___y_5199_ = v___y_5248_;
v___y_5200_ = v___y_5250_;
v___y_5201_ = v___y_5251_;
v___y_5202_ = v___x_5289_;
v___y_5203_ = v___y_5252_;
v___y_5204_ = v_a_5285_;
v___y_5205_ = v___y_5254_;
v_a_5206_ = v___x_5296_;
goto v___jp_5192_;
}
}
}
else
{
lean_object* v_a_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5312_; 
v_a_5299_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5301_ = v___x_5290_;
v_isShared_5302_ = v_isSharedCheck_5312_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_a_5299_);
lean_dec(v___x_5290_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5312_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5303_; lean_object* v___x_5305_; 
v___x_5303_ = lean_io_error_to_string(v_a_5299_);
if (v_isShared_5302_ == 0)
{
lean_ctor_set_tag(v___x_5301_, 3);
lean_ctor_set(v___x_5301_, 0, v___x_5303_);
v___x_5305_ = v___x_5301_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v___x_5303_);
v___x_5305_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5309_; 
v___x_5306_ = l_Lean_MessageData_ofFormat(v___x_5305_);
lean_inc(v_ref_3991_);
v___x_5307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5307_, 0, v_ref_3991_);
lean_ctor_set(v___x_5307_, 1, v___x_5306_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5307_);
v___x_5309_ = v___x_5287_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5307_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
v___y_5193_ = v___y_5242_;
v___y_5194_ = v___y_5243_;
v___y_5195_ = v___y_5244_;
v___y_5196_ = v___y_5246_;
v___y_5197_ = v___y_5245_;
v___y_5198_ = v___y_5247_;
v___y_5199_ = v___y_5248_;
v___y_5200_ = v___y_5250_;
v___y_5201_ = v___y_5251_;
v___y_5202_ = v___x_5289_;
v___y_5203_ = v___y_5252_;
v___y_5204_ = v_a_5285_;
v___y_5205_ = v___y_5254_;
v_a_5206_ = v___x_5309_;
goto v___jp_5192_;
}
}
}
}
}
}
}
v___jp_5314_:
{
lean_object* v___x_5315_; lean_object* v_a_5316_; lean_object* v___x_5317_; uint8_t v___x_5318_; 
v___x_5315_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v_a_3821_);
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5316_);
lean_dec_ref(v___x_5315_);
v___x_5317_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5318_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3990_, v___x_5317_);
if (v___x_5318_ == 0)
{
lean_object* v___x_5319_; lean_object* v_tacticContext_5320_; lean_object* v___x_5321_; lean_object* v_satExpr_5322_; lean_object* v_bvExpr_5323_; lean_object* v___x_5324_; lean_object* v_theoryState_5325_; lean_object* v_bitvecState_5326_; lean_object* v___x_5327_; lean_object* v_theoryState_5328_; lean_object* v_satExpr_5329_; lean_object* v_hypQueue_5330_; lean_object* v_usedHyps_5331_; uint8_t v_didChange_5332_; lean_object* v_solverTimeBudgetMs_5333_; lean_object* v_roundBudget_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5377_; 
v___x_5319_ = lean_io_mono_nanos_now();
v_tacticContext_5320_ = lean_ctor_get(v_a_3808_, 2);
v___x_5321_ = lean_st_ref_get(v_a_3809_);
v_satExpr_5322_ = lean_ctor_get(v___x_5321_, 0);
lean_inc_ref(v_satExpr_5322_);
lean_dec(v___x_5321_);
v_bvExpr_5323_ = lean_ctor_get(v_satExpr_5322_, 0);
lean_inc_ref(v_bvExpr_5323_);
lean_dec_ref(v_satExpr_5322_);
v___x_5324_ = lean_st_ref_get(v_a_3809_);
v_theoryState_5325_ = lean_ctor_get(v___x_5324_, 3);
lean_inc_ref(v_theoryState_5325_);
lean_dec(v___x_5324_);
v_bitvecState_5326_ = lean_ctor_get(v_theoryState_5325_, 1);
lean_inc_ref(v_bitvecState_5326_);
lean_dec_ref(v_theoryState_5325_);
v___x_5327_ = lean_st_ref_take(v_a_3809_);
v_theoryState_5328_ = lean_ctor_get(v___x_5327_, 3);
v_satExpr_5329_ = lean_ctor_get(v___x_5327_, 0);
v_hypQueue_5330_ = lean_ctor_get(v___x_5327_, 1);
v_usedHyps_5331_ = lean_ctor_get(v___x_5327_, 2);
v_didChange_5332_ = lean_ctor_get_uint8(v___x_5327_, sizeof(void*)*6);
v_solverTimeBudgetMs_5333_ = lean_ctor_get(v___x_5327_, 4);
v_roundBudget_5334_ = lean_ctor_get(v___x_5327_, 5);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5336_ = v___x_5327_;
v_isShared_5337_ = v_isSharedCheck_5377_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_roundBudget_5334_);
lean_inc(v_solverTimeBudgetMs_5333_);
lean_inc(v_theoryState_5328_);
lean_inc(v_usedHyps_5331_);
lean_inc(v_hypQueue_5330_);
lean_inc(v_satExpr_5329_);
lean_dec(v___x_5327_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5377_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v_funState_5338_; lean_object* v_preprocessCaches_5339_; lean_object* v_satSolver_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5375_; 
v_funState_5338_ = lean_ctor_get(v_theoryState_5328_, 0);
v_preprocessCaches_5339_ = lean_ctor_get(v_theoryState_5328_, 2);
v_satSolver_5340_ = lean_ctor_get(v_theoryState_5328_, 3);
v_isSharedCheck_5375_ = !lean_is_exclusive(v_theoryState_5328_);
if (v_isSharedCheck_5375_ == 0)
{
lean_object* v_unused_5376_; 
v_unused_5376_ = lean_ctor_get(v_theoryState_5328_, 1);
lean_dec(v_unused_5376_);
v___x_5342_ = v_theoryState_5328_;
v_isShared_5343_ = v_isSharedCheck_5375_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_satSolver_5340_);
lean_inc(v_preprocessCaches_5339_);
lean_inc(v_funState_5338_);
lean_dec(v_theoryState_5328_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5375_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5348_; 
v___x_5344_ = lean_unsigned_to_nat(0u);
v___x_5345_ = lean_unsigned_to_nat(16u);
v___x_5346_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 1, v___x_5346_);
v___x_5348_ = v___x_5342_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_funState_5338_);
lean_ctor_set(v_reuseFailAlloc_5374_, 1, v___x_5346_);
lean_ctor_set(v_reuseFailAlloc_5374_, 2, v_preprocessCaches_5339_);
lean_ctor_set(v_reuseFailAlloc_5374_, 3, v_satSolver_5340_);
v___x_5348_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5350_; 
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 3, v___x_5348_);
v___x_5350_ = v___x_5336_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_satExpr_5329_);
lean_ctor_set(v_reuseFailAlloc_5373_, 1, v_hypQueue_5330_);
lean_ctor_set(v_reuseFailAlloc_5373_, 2, v_usedHyps_5331_);
lean_ctor_set(v_reuseFailAlloc_5373_, 3, v___x_5348_);
lean_ctor_set(v_reuseFailAlloc_5373_, 4, v_solverTimeBudgetMs_5333_);
lean_ctor_set(v_reuseFailAlloc_5373_, 5, v_roundBudget_5334_);
lean_ctor_set_uint8(v_reuseFailAlloc_5373_, sizeof(void*)*6, v_didChange_5332_);
v___x_5350_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
lean_object* v___x_5351_; lean_object* v_aig_5352_; lean_object* v_blastCache_5353_; lean_object* v_cnfCache_5354_; lean_object* v_decls_5355_; lean_object* v___f_5356_; lean_object* v___x_5357_; 
v___x_5351_ = lean_st_ref_put(v_a_3809_, v___x_5350_);
v_aig_5352_ = lean_ctor_get(v_bitvecState_5326_, 0);
lean_inc_ref(v_aig_5352_);
v_blastCache_5353_ = lean_ctor_get(v_bitvecState_5326_, 1);
lean_inc_ref(v_blastCache_5353_);
v_cnfCache_5354_ = lean_ctor_get(v_bitvecState_5326_, 2);
lean_inc_ref(v_cnfCache_5354_);
lean_dec_ref(v_bitvecState_5326_);
v_decls_5355_ = lean_ctor_get(v_aig_5352_, 0);
lean_inc_ref(v_decls_5355_);
v___f_5356_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_5356_, 0, v_aig_5352_);
lean_closure_set(v___f_5356_, 1, v_bvExpr_5323_);
lean_closure_set(v___f_5356_, 2, v_blastCache_5353_);
v___x_5357_ = lean_array_get_size(v_decls_5355_);
lean_dec_ref(v_decls_5355_);
if (v___x_4904_ == 0)
{
lean_object* v___x_5358_; uint8_t v___x_5359_; 
v___x_5358_ = l_Lean_trace_profiler;
v___x_5359_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3990_, v___x_5358_);
if (v___x_5359_ == 0)
{
lean_object* v___x_5360_; 
v___x_5360_ = l_IO_lazyPure___redArg(v___f_5356_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_a_5361_; 
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
lean_inc(v_a_5361_);
lean_dec_ref_known(v___x_5360_, 1);
v___y_5143_ = v___x_5317_;
v___y_5144_ = v___x_5344_;
v___y_5145_ = v_cnfCache_5354_;
v___y_5146_ = v___x_5346_;
v___y_5147_ = v___x_5345_;
v___y_5148_ = v___x_5318_;
v___y_5149_ = v_tacticContext_5320_;
v___y_5150_ = v___x_5319_;
v___y_5151_ = v___x_5357_;
v___y_5152_ = v_a_5316_;
v_a_5153_ = v_a_5361_;
goto v___jp_5142_;
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5372_; 
lean_dec_ref(v_cnfCache_5354_);
v_a_5362_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5364_ = v___x_5360_;
v_isShared_5365_ = v_isSharedCheck_5372_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5360_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5372_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5366_; lean_object* v___x_5368_; 
v___x_5366_ = lean_io_error_to_string(v_a_5362_);
if (v_isShared_5365_ == 0)
{
lean_ctor_set_tag(v___x_5364_, 3);
lean_ctor_set(v___x_5364_, 0, v___x_5366_);
v___x_5368_ = v___x_5364_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5366_);
v___x_5368_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
lean_object* v___x_5369_; lean_object* v___x_5370_; 
v___x_5369_ = l_Lean_MessageData_ofFormat(v___x_5368_);
lean_inc(v_ref_3991_);
v___x_5370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5370_, 0, v_ref_3991_);
lean_ctor_set(v___x_5370_, 1, v___x_5369_);
v___y_5125_ = v___x_5319_;
v___y_5126_ = v_a_5316_;
v_a_5127_ = v___x_5370_;
goto v___jp_5124_;
}
}
}
}
else
{
v___y_5242_ = v___x_5317_;
v___y_5243_ = v___x_5344_;
v___y_5244_ = v_cnfCache_5354_;
v___y_5245_ = v___x_5345_;
v___y_5246_ = v___x_5346_;
v___y_5247_ = v___x_5318_;
v___y_5248_ = v_tacticContext_5320_;
v___y_5249_ = v___f_5356_;
v___y_5250_ = v___x_5319_;
v___y_5251_ = v___x_5357_;
v___y_5252_ = v___x_4904_;
v___y_5253_ = v___x_5318_;
v___y_5254_ = v_a_5316_;
goto v___jp_5241_;
}
}
else
{
v___y_5242_ = v___x_5317_;
v___y_5243_ = v___x_5344_;
v___y_5244_ = v_cnfCache_5354_;
v___y_5245_ = v___x_5345_;
v___y_5246_ = v___x_5346_;
v___y_5247_ = v___x_5318_;
v___y_5248_ = v_tacticContext_5320_;
v___y_5249_ = v___f_5356_;
v___y_5250_ = v___x_5319_;
v___y_5251_ = v___x_5357_;
v___y_5252_ = v___x_4904_;
v___y_5253_ = v___x_5318_;
v___y_5254_ = v_a_5316_;
goto v___jp_5241_;
}
}
}
}
}
}
else
{
lean_object* v___x_5378_; lean_object* v_tacticContext_5379_; lean_object* v___x_5380_; lean_object* v_satExpr_5381_; lean_object* v_bvExpr_5382_; lean_object* v___x_5383_; lean_object* v_theoryState_5384_; lean_object* v_bitvecState_5385_; lean_object* v___x_5386_; lean_object* v_theoryState_5387_; lean_object* v_satExpr_5388_; lean_object* v_hypQueue_5389_; lean_object* v_usedHyps_5390_; uint8_t v_didChange_5391_; lean_object* v_solverTimeBudgetMs_5392_; lean_object* v_roundBudget_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5436_; 
v___x_5378_ = lean_io_get_num_heartbeats();
v_tacticContext_5379_ = lean_ctor_get(v_a_3808_, 2);
v___x_5380_ = lean_st_ref_get(v_a_3809_);
v_satExpr_5381_ = lean_ctor_get(v___x_5380_, 0);
lean_inc_ref(v_satExpr_5381_);
lean_dec(v___x_5380_);
v_bvExpr_5382_ = lean_ctor_get(v_satExpr_5381_, 0);
lean_inc_ref(v_bvExpr_5382_);
lean_dec_ref(v_satExpr_5381_);
v___x_5383_ = lean_st_ref_get(v_a_3809_);
v_theoryState_5384_ = lean_ctor_get(v___x_5383_, 3);
lean_inc_ref(v_theoryState_5384_);
lean_dec(v___x_5383_);
v_bitvecState_5385_ = lean_ctor_get(v_theoryState_5384_, 1);
lean_inc_ref(v_bitvecState_5385_);
lean_dec_ref(v_theoryState_5384_);
v___x_5386_ = lean_st_ref_take(v_a_3809_);
v_theoryState_5387_ = lean_ctor_get(v___x_5386_, 3);
v_satExpr_5388_ = lean_ctor_get(v___x_5386_, 0);
v_hypQueue_5389_ = lean_ctor_get(v___x_5386_, 1);
v_usedHyps_5390_ = lean_ctor_get(v___x_5386_, 2);
v_didChange_5391_ = lean_ctor_get_uint8(v___x_5386_, sizeof(void*)*6);
v_solverTimeBudgetMs_5392_ = lean_ctor_get(v___x_5386_, 4);
v_roundBudget_5393_ = lean_ctor_get(v___x_5386_, 5);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5395_ = v___x_5386_;
v_isShared_5396_ = v_isSharedCheck_5436_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_roundBudget_5393_);
lean_inc(v_solverTimeBudgetMs_5392_);
lean_inc(v_theoryState_5387_);
lean_inc(v_usedHyps_5390_);
lean_inc(v_hypQueue_5389_);
lean_inc(v_satExpr_5388_);
lean_dec(v___x_5386_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5436_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v_funState_5397_; lean_object* v_preprocessCaches_5398_; lean_object* v_satSolver_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5434_; 
v_funState_5397_ = lean_ctor_get(v_theoryState_5387_, 0);
v_preprocessCaches_5398_ = lean_ctor_get(v_theoryState_5387_, 2);
v_satSolver_5399_ = lean_ctor_get(v_theoryState_5387_, 3);
v_isSharedCheck_5434_ = !lean_is_exclusive(v_theoryState_5387_);
if (v_isSharedCheck_5434_ == 0)
{
lean_object* v_unused_5435_; 
v_unused_5435_ = lean_ctor_get(v_theoryState_5387_, 1);
lean_dec(v_unused_5435_);
v___x_5401_ = v_theoryState_5387_;
v_isShared_5402_ = v_isSharedCheck_5434_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_satSolver_5399_);
lean_inc(v_preprocessCaches_5398_);
lean_inc(v_funState_5397_);
lean_dec(v_theoryState_5387_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5434_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5407_; 
v___x_5403_ = lean_unsigned_to_nat(0u);
v___x_5404_ = lean_unsigned_to_nat(16u);
v___x_5405_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 1, v___x_5405_);
v___x_5407_ = v___x_5401_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_funState_5397_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v___x_5405_);
lean_ctor_set(v_reuseFailAlloc_5433_, 2, v_preprocessCaches_5398_);
lean_ctor_set(v_reuseFailAlloc_5433_, 3, v_satSolver_5399_);
v___x_5407_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
lean_object* v___x_5409_; 
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 3, v___x_5407_);
v___x_5409_ = v___x_5395_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_satExpr_5388_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v_hypQueue_5389_);
lean_ctor_set(v_reuseFailAlloc_5432_, 2, v_usedHyps_5390_);
lean_ctor_set(v_reuseFailAlloc_5432_, 3, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5432_, 4, v_solverTimeBudgetMs_5392_);
lean_ctor_set(v_reuseFailAlloc_5432_, 5, v_roundBudget_5393_);
lean_ctor_set_uint8(v_reuseFailAlloc_5432_, sizeof(void*)*6, v_didChange_5391_);
v___x_5409_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
lean_object* v___x_5410_; lean_object* v_aig_5411_; lean_object* v_blastCache_5412_; lean_object* v_cnfCache_5413_; lean_object* v_decls_5414_; lean_object* v___f_5415_; lean_object* v___x_5416_; 
v___x_5410_ = lean_st_ref_put(v_a_3809_, v___x_5409_);
v_aig_5411_ = lean_ctor_get(v_bitvecState_5385_, 0);
lean_inc_ref(v_aig_5411_);
v_blastCache_5412_ = lean_ctor_get(v_bitvecState_5385_, 1);
lean_inc_ref(v_blastCache_5412_);
v_cnfCache_5413_ = lean_ctor_get(v_bitvecState_5385_, 2);
lean_inc_ref(v_cnfCache_5413_);
lean_dec_ref(v_bitvecState_5385_);
v_decls_5414_ = lean_ctor_get(v_aig_5411_, 0);
lean_inc_ref(v_decls_5414_);
v___f_5415_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_5415_, 0, v_aig_5411_);
lean_closure_set(v___f_5415_, 1, v_bvExpr_5382_);
lean_closure_set(v___f_5415_, 2, v_blastCache_5412_);
v___x_5416_ = lean_array_get_size(v_decls_5414_);
lean_dec_ref(v_decls_5414_);
if (v___x_4904_ == 0)
{
lean_object* v___x_5417_; uint8_t v___x_5418_; 
v___x_5417_ = l_Lean_trace_profiler;
v___x_5418_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_3990_, v___x_5417_);
if (v___x_5418_ == 0)
{
lean_object* v___x_5419_; 
v___x_5419_ = l_IO_lazyPure___redArg(v___f_5415_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_a_5420_);
lean_dec_ref_known(v___x_5419_, 1);
v___y_4936_ = v_cnfCache_5413_;
v___y_4937_ = v___x_5317_;
v___y_4938_ = v___x_5403_;
v___y_4939_ = v_tacticContext_5379_;
v___y_4940_ = v___x_5318_;
v___y_4941_ = v___x_5405_;
v___y_4942_ = v___x_5404_;
v___y_4943_ = v___x_5378_;
v___y_4944_ = v___x_5416_;
v___y_4945_ = v_a_5316_;
v_a_4946_ = v_a_5420_;
goto v___jp_4935_;
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5431_; 
lean_dec_ref(v_cnfCache_5413_);
v_a_5421_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5423_ = v___x_5419_;
v_isShared_5424_ = v_isSharedCheck_5431_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5419_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5431_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5425_; lean_object* v___x_5427_; 
v___x_5425_ = lean_io_error_to_string(v_a_5421_);
if (v_isShared_5424_ == 0)
{
lean_ctor_set_tag(v___x_5423_, 3);
lean_ctor_set(v___x_5423_, 0, v___x_5425_);
v___x_5427_ = v___x_5423_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v___x_5425_);
v___x_5427_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5428_ = l_Lean_MessageData_ofFormat(v___x_5427_);
lean_inc(v_ref_3991_);
v___x_5429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5429_, 0, v_ref_3991_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___y_4918_ = v___x_5378_;
v___y_4919_ = v_a_5316_;
v_a_4920_ = v___x_5429_;
goto v___jp_4917_;
}
}
}
}
else
{
v___y_5037_ = v_cnfCache_5413_;
v___y_5038_ = v___x_5403_;
v___y_5039_ = v___x_5317_;
v___y_5040_ = v_tacticContext_5379_;
v___y_5041_ = v___x_5318_;
v___y_5042_ = v___x_5405_;
v___y_5043_ = v___x_5404_;
v___y_5044_ = v___x_4904_;
v___y_5045_ = v___x_5378_;
v___y_5046_ = v___x_5318_;
v___y_5047_ = v___f_5415_;
v___y_5048_ = v_a_5316_;
v___y_5049_ = v___x_5416_;
goto v___jp_5036_;
}
}
else
{
v___y_5037_ = v_cnfCache_5413_;
v___y_5038_ = v___x_5403_;
v___y_5039_ = v___x_5317_;
v___y_5040_ = v_tacticContext_5379_;
v___y_5041_ = v___x_5318_;
v___y_5042_ = v___x_5405_;
v___y_5043_ = v___x_5404_;
v___y_5044_ = v___x_4904_;
v___y_5045_ = v___x_5378_;
v___y_5046_ = v___x_5318_;
v___y_5047_ = v___f_5415_;
v___y_5048_ = v_a_5316_;
v___y_5049_ = v___x_5416_;
goto v___jp_5036_;
}
}
}
}
}
}
}
}
v___jp_3823_:
{
lean_object* v___x_3840_; 
v___x_3840_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_getAssignment(v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3825_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
v___x_3842_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_3830_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3852_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3852_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3852_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
v___x_3847_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_3824_, v_a_3841_, v_a_3843_);
lean_dec(v_a_3843_);
lean_dec(v_a_3841_);
v___x_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3848_);
v___x_3850_ = v___x_3845_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v_a_3841_);
lean_dec_ref(v___y_3824_);
v_a_3853_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3842_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3842_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
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
return v___x_3858_;
}
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v___y_3824_);
v_a_3861_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3840_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3840_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
v___jp_3869_:
{
if (lean_obj_tag(v___y_3891_) == 0)
{
lean_object* v_a_3892_; uint8_t v___x_3893_; 
v_a_3892_ = lean_ctor_get(v___y_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___y_3891_, 1);
v___x_3893_ = lean_unbox(v_a_3892_);
lean_dec(v_a_3892_);
switch(v___x_3893_)
{
case 0:
{
lean_object* v_toCold_3894_; lean_object* v_options_3895_; uint8_t v_hasTrace_3896_; 
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
v_toCold_3894_ = lean_ctor_get(v___y_3878_, 0);
v_options_3895_ = lean_ctor_get(v_toCold_3894_, 2);
v_hasTrace_3896_ = lean_ctor_get_uint8(v_options_3895_, sizeof(void*)*1);
if (v_hasTrace_3896_ == 0)
{
v___y_3824_ = v___y_3875_;
v___y_3825_ = v___y_3883_;
v___y_3826_ = v___y_3884_;
v___y_3827_ = v___y_3879_;
v___y_3828_ = v___y_3881_;
v___y_3829_ = v___y_3885_;
v___y_3830_ = v___y_3877_;
v___y_3831_ = v___y_3876_;
v___y_3832_ = v___y_3887_;
v___y_3833_ = v___y_3882_;
v___y_3834_ = v___y_3880_;
v___y_3835_ = v___y_3889_;
v___y_3836_ = v___y_3871_;
v___y_3837_ = v___y_3886_;
v___y_3838_ = v___y_3878_;
v___y_3839_ = v___y_3890_;
goto v___jp_3823_;
}
else
{
lean_object* v_inheritedTraceOptions_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_inheritedTraceOptions_3897_ = lean_ctor_get(v_toCold_3894_, 11);
v___x_3898_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_3873_);
v___x_3899_ = l_Lean_Name_append(v___x_3898_, v___y_3873_);
v___x_3900_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3897_, v_options_3895_, v___x_3899_);
lean_dec(v___x_3899_);
if (v___x_3900_ == 0)
{
v___y_3824_ = v___y_3875_;
v___y_3825_ = v___y_3883_;
v___y_3826_ = v___y_3884_;
v___y_3827_ = v___y_3879_;
v___y_3828_ = v___y_3881_;
v___y_3829_ = v___y_3885_;
v___y_3830_ = v___y_3877_;
v___y_3831_ = v___y_3876_;
v___y_3832_ = v___y_3887_;
v___y_3833_ = v___y_3882_;
v___y_3834_ = v___y_3880_;
v___y_3835_ = v___y_3889_;
v___y_3836_ = v___y_3871_;
v___y_3837_ = v___y_3886_;
v___y_3838_ = v___y_3878_;
v___y_3839_ = v___y_3890_;
goto v___jp_3823_;
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__3);
lean_inc(v___y_3873_);
v___x_3902_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v___y_3873_, v___x_3901_, v___y_3871_, v___y_3886_, v___y_3878_, v___y_3890_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_dec_ref_known(v___x_3902_, 1);
v___y_3824_ = v___y_3875_;
v___y_3825_ = v___y_3883_;
v___y_3826_ = v___y_3884_;
v___y_3827_ = v___y_3879_;
v___y_3828_ = v___y_3881_;
v___y_3829_ = v___y_3885_;
v___y_3830_ = v___y_3877_;
v___y_3831_ = v___y_3876_;
v___y_3832_ = v___y_3887_;
v___y_3833_ = v___y_3882_;
v___y_3834_ = v___y_3880_;
v___y_3835_ = v___y_3889_;
v___y_3836_ = v___y_3871_;
v___y_3837_ = v___y_3886_;
v___y_3838_ = v___y_3878_;
v___y_3839_ = v___y_3890_;
goto v___jp_3823_;
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3875_);
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
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
case 1:
{
lean_object* v___x_3911_; lean_object* v_satExpr_3912_; lean_object* v_hypQueue_3913_; lean_object* v_usedHyps_3914_; uint8_t v_didChange_3915_; lean_object* v_theoryState_3916_; lean_object* v_solverTimeBudgetMs_3917_; lean_object* v_roundBudget_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3875_);
v___x_3911_ = lean_st_ref_take(v___y_3879_);
v_satExpr_3912_ = lean_ctor_get(v___x_3911_, 0);
v_hypQueue_3913_ = lean_ctor_get(v___x_3911_, 1);
v_usedHyps_3914_ = lean_ctor_get(v___x_3911_, 2);
v_didChange_3915_ = lean_ctor_get_uint8(v___x_3911_, sizeof(void*)*6);
v_theoryState_3916_ = lean_ctor_get(v___x_3911_, 3);
v_solverTimeBudgetMs_3917_ = lean_ctor_get(v___x_3911_, 4);
v_roundBudget_3918_ = lean_ctor_get(v___x_3911_, 5);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3920_ = v___x_3911_;
v_isShared_3921_ = v_isSharedCheck_3979_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_roundBudget_3918_);
lean_inc(v_solverTimeBudgetMs_3917_);
lean_inc(v_theoryState_3916_);
lean_inc(v_usedHyps_3914_);
lean_inc(v_hypQueue_3913_);
lean_inc(v_satExpr_3912_);
lean_dec(v___x_3911_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3979_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3922_; lean_object* v_satSolver_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3975_; 
v___x_3922_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__6);
v_satSolver_3923_ = lean_ctor_get(v_theoryState_3916_, 3);
v_isSharedCheck_3975_ = !lean_is_exclusive(v_theoryState_3916_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; lean_object* v_unused_3977_; lean_object* v_unused_3978_; 
v_unused_3976_ = lean_ctor_get(v_theoryState_3916_, 2);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_theoryState_3916_, 1);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v_theoryState_3916_, 0);
lean_dec(v_unused_3978_);
v___x_3925_ = v_theoryState_3916_;
v_isShared_3926_ = v_isSharedCheck_3975_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_satSolver_3923_);
lean_dec(v_theoryState_3916_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3975_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3927_ = lean_box(0);
v___x_3928_ = lean_mk_array(v___y_3872_, v___x_3927_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___y_3874_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
lean_inc_ref(v___y_3888_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 2, v___x_3922_);
lean_ctor_set(v___x_3925_, 1, v___y_3888_);
lean_ctor_set(v___x_3925_, 0, v___x_3929_);
v___x_3931_ = v___x_3925_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v___y_3888_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_satSolver_3923_);
v___x_3931_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3933_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 3, v___x_3931_);
v___x_3933_ = v___x_3920_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_satExpr_3912_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_hypQueue_3913_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v_usedHyps_3914_);
lean_ctor_set(v_reuseFailAlloc_3973_, 3, v___x_3931_);
lean_ctor_set(v_reuseFailAlloc_3973_, 4, v_solverTimeBudgetMs_3917_);
lean_ctor_set(v_reuseFailAlloc_3973_, 5, v_roundBudget_3918_);
lean_ctor_set_uint8(v_reuseFailAlloc_3973_, sizeof(void*)*6, v_didChange_3915_);
v___x_3933_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_st_ref_put(v___y_3879_, v___x_3933_);
v___x_3935_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getReflectionResult___redArg(v___y_3884_, v___y_3879_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v_goal_3937_; lean_object* v___x_3938_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v_goal_3937_ = lean_ctor_get(v___y_3884_, 0);
lean_inc(v_goal_3937_);
lean_inc_ref(v___y_3870_);
v___x_3938_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v___y_3870_, v_goal_3937_, v_a_3936_, v___y_3881_, v___y_3885_, v___y_3877_, v___y_3876_, v___y_3887_, v___y_3882_, v___y_3880_, v___y_3889_, v___y_3871_, v___y_3886_, v___y_3878_, v___y_3890_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3956_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3941_ = v___x_3938_;
v_isShared_3942_ = v_isSharedCheck_3956_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3938_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3956_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
if (lean_obj_tag(v_a_3939_) == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec_ref_known(v_a_3939_, 1);
lean_del_object(v___x_3941_);
v___x_3943_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__8);
v___x_3944_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v___x_3943_, v___y_3871_, v___y_3886_, v___y_3878_, v___y_3890_);
return v___x_3944_;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3955_; 
v_a_3945_ = lean_ctor_get(v_a_3939_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_a_3939_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3947_ = v_a_3939_;
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v_a_3939_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3955_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3952_; 
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3950_);
v___x_3952_ = v___x_3941_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
v_a_3957_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3938_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3938_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_a_3965_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3935_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3935_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
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
lean_object* v___x_3980_; 
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
v___x_3980_ = l_Lean_Meta_Tactic_BVDecide_External_throwSatTimeout___redArg(v___y_3878_, v___y_3890_);
return v___x_3980_;
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
v_a_3981_ = lean_ctor_get(v___y_3891_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___y_3891_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___y_3891_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___y_3891_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
v___jp_3996_:
{
lean_object* v___x_4025_; double v___x_4026_; double v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4025_ = lean_io_get_num_heartbeats();
v___x_4026_ = lean_float_of_nat(v___y_3999_);
v___x_4027_ = lean_float_of_nat(v___x_4025_);
v___x_4028_ = lean_box_float(v___x_4026_);
v___x_4029_ = lean_box_float(v___x_4027_);
v___x_4030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4028_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
v___x_4031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4031_, 0, v_a_4024_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
lean_inc_ref(v___y_4017_);
lean_inc(v___y_4013_);
v___x_4032_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_4013_, v___y_4014_, v___y_4017_, v___y_4015_, v___y_4009_, v___y_4018_, v___f_3995_, v___x_4031_, v___y_4008_, v___y_4004_, v___y_4006_, v___y_4020_, v___y_4003_, v___y_4002_, v___y_4010_, v___y_4007_, v___y_4005_, v___y_4023_, v___y_3997_, v___y_4021_, v___y_4016_, v___y_4011_);
v___y_3870_ = v___y_4012_;
v___y_3871_ = v___y_3997_;
v___y_3872_ = v___y_3998_;
v___y_3873_ = v___y_4013_;
v___y_3874_ = v___y_4000_;
v___y_3875_ = v___y_4001_;
v___y_3876_ = v___y_4002_;
v___y_3877_ = v___y_4003_;
v___y_3878_ = v___y_4016_;
v___y_3879_ = v___y_4004_;
v___y_3880_ = v___y_4005_;
v___y_3881_ = v___y_4006_;
v___y_3882_ = v___y_4007_;
v___y_3883_ = v___y_4019_;
v___y_3884_ = v___y_4008_;
v___y_3885_ = v___y_4020_;
v___y_3886_ = v___y_4021_;
v___y_3887_ = v___y_4010_;
v___y_3888_ = v___y_4022_;
v___y_3889_ = v___y_4023_;
v___y_3890_ = v___y_4011_;
v___y_3891_ = v___x_4032_;
goto v___jp_3869_;
}
v___jp_4033_:
{
lean_object* v___x_4062_; double v___x_4063_; double v___x_4064_; double v___x_4065_; double v___x_4066_; double v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4062_ = lean_io_mono_nanos_now();
v___x_4063_ = lean_float_of_nat(v___y_4045_);
v___x_4064_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4065_ = lean_float_div(v___x_4063_, v___x_4064_);
v___x_4066_ = lean_float_of_nat(v___x_4062_);
v___x_4067_ = lean_float_div(v___x_4066_, v___x_4064_);
v___x_4068_ = lean_box_float(v___x_4065_);
v___x_4069_ = lean_box_float(v___x_4067_);
v___x_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_a_4061_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
lean_inc_ref(v___y_4054_);
lean_inc(v___y_4050_);
v___x_4072_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6(v___y_4050_, v___y_4051_, v___y_4054_, v___y_4052_, v___y_4046_, v___y_4055_, v___f_3995_, v___x_4071_, v___y_4044_, v___y_4040_, v___y_4042_, v___y_4057_, v___y_4039_, v___y_4038_, v___y_4047_, v___y_4043_, v___y_4041_, v___y_4060_, v___y_4034_, v___y_4058_, v___y_4053_, v___y_4048_);
v___y_3870_ = v___y_4049_;
v___y_3871_ = v___y_4034_;
v___y_3872_ = v___y_4035_;
v___y_3873_ = v___y_4050_;
v___y_3874_ = v___y_4036_;
v___y_3875_ = v___y_4037_;
v___y_3876_ = v___y_4038_;
v___y_3877_ = v___y_4039_;
v___y_3878_ = v___y_4053_;
v___y_3879_ = v___y_4040_;
v___y_3880_ = v___y_4041_;
v___y_3881_ = v___y_4042_;
v___y_3882_ = v___y_4043_;
v___y_3883_ = v___y_4056_;
v___y_3884_ = v___y_4044_;
v___y_3885_ = v___y_4057_;
v___y_3886_ = v___y_4058_;
v___y_3887_ = v___y_4047_;
v___y_3888_ = v___y_4059_;
v___y_3889_ = v___y_4060_;
v___y_3890_ = v___y_4048_;
v___y_3891_ = v___x_4072_;
goto v___jp_3869_;
}
v___jp_4073_:
{
lean_object* v___x_4100_; lean_object* v_a_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; 
v___x_4100_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4088_);
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref(v___x_4100_);
v___x_4102_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4103_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4092_, v___x_4102_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = lean_io_mono_nanos_now();
v___x_4105_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4081_, v___y_4085_, v___y_4080_, v___y_4084_, v___y_4096_, v___y_4079_, v___y_4078_, v___y_4087_, v___y_4083_, v___y_4082_, v___y_4099_, v___y_4074_, v___y_4097_, v___y_4093_, v___y_4088_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4105_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4105_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
lean_ctor_set_tag(v___x_4108_, 1);
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
v___y_4034_ = v___y_4074_;
v___y_4035_ = v___y_4075_;
v___y_4036_ = v___y_4076_;
v___y_4037_ = v___y_4077_;
v___y_4038_ = v___y_4078_;
v___y_4039_ = v___y_4079_;
v___y_4040_ = v___y_4080_;
v___y_4041_ = v___y_4082_;
v___y_4042_ = v___y_4084_;
v___y_4043_ = v___y_4083_;
v___y_4044_ = v___y_4085_;
v___y_4045_ = v___x_4104_;
v___y_4046_ = v___y_4086_;
v___y_4047_ = v___y_4087_;
v___y_4048_ = v___y_4088_;
v___y_4049_ = v___y_4089_;
v___y_4050_ = v___y_4090_;
v___y_4051_ = v___y_4091_;
v___y_4052_ = v___y_4092_;
v___y_4053_ = v___y_4093_;
v___y_4054_ = v___y_4094_;
v___y_4055_ = v_a_4101_;
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
v___y_4059_ = v___y_4098_;
v___y_4060_ = v___y_4099_;
v_a_4061_ = v___x_4111_;
goto v___jp_4033_;
}
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
v_a_4114_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4105_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4105_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 0);
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
v___y_4034_ = v___y_4074_;
v___y_4035_ = v___y_4075_;
v___y_4036_ = v___y_4076_;
v___y_4037_ = v___y_4077_;
v___y_4038_ = v___y_4078_;
v___y_4039_ = v___y_4079_;
v___y_4040_ = v___y_4080_;
v___y_4041_ = v___y_4082_;
v___y_4042_ = v___y_4084_;
v___y_4043_ = v___y_4083_;
v___y_4044_ = v___y_4085_;
v___y_4045_ = v___x_4104_;
v___y_4046_ = v___y_4086_;
v___y_4047_ = v___y_4087_;
v___y_4048_ = v___y_4088_;
v___y_4049_ = v___y_4089_;
v___y_4050_ = v___y_4090_;
v___y_4051_ = v___y_4091_;
v___y_4052_ = v___y_4092_;
v___y_4053_ = v___y_4093_;
v___y_4054_ = v___y_4094_;
v___y_4055_ = v_a_4101_;
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
v___y_4059_ = v___y_4098_;
v___y_4060_ = v___y_4099_;
v_a_4061_ = v___x_4119_;
goto v___jp_4033_;
}
}
}
}
else
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4122_ = lean_io_get_num_heartbeats();
v___x_4123_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4081_, v___y_4085_, v___y_4080_, v___y_4084_, v___y_4096_, v___y_4079_, v___y_4078_, v___y_4087_, v___y_4083_, v___y_4082_, v___y_4099_, v___y_4074_, v___y_4097_, v___y_4093_, v___y_4088_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4123_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4123_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
lean_ctor_set_tag(v___x_4126_, 1);
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
v___y_3997_ = v___y_4074_;
v___y_3998_ = v___y_4075_;
v___y_3999_ = v___x_4122_;
v___y_4000_ = v___y_4076_;
v___y_4001_ = v___y_4077_;
v___y_4002_ = v___y_4078_;
v___y_4003_ = v___y_4079_;
v___y_4004_ = v___y_4080_;
v___y_4005_ = v___y_4082_;
v___y_4006_ = v___y_4084_;
v___y_4007_ = v___y_4083_;
v___y_4008_ = v___y_4085_;
v___y_4009_ = v___y_4086_;
v___y_4010_ = v___y_4087_;
v___y_4011_ = v___y_4088_;
v___y_4012_ = v___y_4089_;
v___y_4013_ = v___y_4090_;
v___y_4014_ = v___y_4091_;
v___y_4015_ = v___y_4092_;
v___y_4016_ = v___y_4093_;
v___y_4017_ = v___y_4094_;
v___y_4018_ = v_a_4101_;
v___y_4019_ = v___y_4095_;
v___y_4020_ = v___y_4096_;
v___y_4021_ = v___y_4097_;
v___y_4022_ = v___y_4098_;
v___y_4023_ = v___y_4099_;
v_a_4024_ = v___x_4129_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
v_a_4132_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4123_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4123_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 0);
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
v___y_3997_ = v___y_4074_;
v___y_3998_ = v___y_4075_;
v___y_3999_ = v___x_4122_;
v___y_4000_ = v___y_4076_;
v___y_4001_ = v___y_4077_;
v___y_4002_ = v___y_4078_;
v___y_4003_ = v___y_4079_;
v___y_4004_ = v___y_4080_;
v___y_4005_ = v___y_4082_;
v___y_4006_ = v___y_4084_;
v___y_4007_ = v___y_4083_;
v___y_4008_ = v___y_4085_;
v___y_4009_ = v___y_4086_;
v___y_4010_ = v___y_4087_;
v___y_4011_ = v___y_4088_;
v___y_4012_ = v___y_4089_;
v___y_4013_ = v___y_4090_;
v___y_4014_ = v___y_4091_;
v___y_4015_ = v___y_4092_;
v___y_4016_ = v___y_4093_;
v___y_4017_ = v___y_4094_;
v___y_4018_ = v_a_4101_;
v___y_4019_ = v___y_4095_;
v___y_4020_ = v___y_4096_;
v___y_4021_ = v___y_4097_;
v___y_4022_ = v___y_4098_;
v___y_4023_ = v___y_4099_;
v_a_4024_ = v___x_4137_;
goto v___jp_3996_;
}
}
}
}
}
v___jp_4140_:
{
lean_object* v_toCold_4167_; lean_object* v_ref_4168_; lean_object* v___x_4169_; 
v_toCold_4167_ = lean_ctor_get(v___y_4159_, 0);
v_ref_4168_ = lean_ctor_get(v___y_4159_, 2);
lean_inc_ref(v___y_4149_);
v___x_4169_ = l_Lean_Cadical_Solver_assume(v___y_4149_, v___y_4148_, v___y_4166_);
lean_dec(v___y_4148_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_options_4170_; uint8_t v_hasTrace_4171_; 
lean_dec_ref_known(v___x_4169_, 1);
v_options_4170_ = lean_ctor_get(v_toCold_4167_, 2);
v_hasTrace_4171_ = lean_ctor_get_uint8(v_options_4170_, sizeof(void*)*1);
if (v_hasTrace_4171_ == 0)
{
lean_object* v___x_4172_; 
v___x_4172_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4149_, v___y_4153_, v___y_4147_, v___y_4152_, v___y_4162_, v___y_4146_, v___y_4145_, v___y_4154_, v___y_4151_, v___y_4150_, v___y_4164_, v___y_4141_, v___y_4163_, v___y_4159_, v___y_4155_);
v___y_3870_ = v___y_4156_;
v___y_3871_ = v___y_4141_;
v___y_3872_ = v___y_4142_;
v___y_3873_ = v___y_4157_;
v___y_3874_ = v___y_4143_;
v___y_3875_ = v___y_4144_;
v___y_3876_ = v___y_4145_;
v___y_3877_ = v___y_4146_;
v___y_3878_ = v___y_4159_;
v___y_3879_ = v___y_4147_;
v___y_3880_ = v___y_4150_;
v___y_3881_ = v___y_4152_;
v___y_3882_ = v___y_4151_;
v___y_3883_ = v___y_4161_;
v___y_3884_ = v___y_4153_;
v___y_3885_ = v___y_4162_;
v___y_3886_ = v___y_4163_;
v___y_3887_ = v___y_4154_;
v___y_3888_ = v___y_4165_;
v___y_3889_ = v___y_4164_;
v___y_3890_ = v___y_4155_;
v___y_3891_ = v___x_4172_;
goto v___jp_3869_;
}
else
{
lean_object* v_inheritedTraceOptions_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v_inheritedTraceOptions_4173_ = lean_ctor_get(v_toCold_4167_, 11);
v___x_4174_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__1));
lean_inc(v___y_4157_);
v___x_4175_ = l_Lean_Name_append(v___x_4174_, v___y_4157_);
v___x_4176_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4173_, v_options_4170_, v___x_4175_);
lean_dec(v___x_4175_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; uint8_t v___x_4178_; 
v___x_4177_ = l_Lean_trace_profiler;
v___x_4178_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4170_, v___x_4177_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; 
v___x_4179_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_runSatSolver(v___y_4149_, v___y_4153_, v___y_4147_, v___y_4152_, v___y_4162_, v___y_4146_, v___y_4145_, v___y_4154_, v___y_4151_, v___y_4150_, v___y_4164_, v___y_4141_, v___y_4163_, v___y_4159_, v___y_4155_);
v___y_3870_ = v___y_4156_;
v___y_3871_ = v___y_4141_;
v___y_3872_ = v___y_4142_;
v___y_3873_ = v___y_4157_;
v___y_3874_ = v___y_4143_;
v___y_3875_ = v___y_4144_;
v___y_3876_ = v___y_4145_;
v___y_3877_ = v___y_4146_;
v___y_3878_ = v___y_4159_;
v___y_3879_ = v___y_4147_;
v___y_3880_ = v___y_4150_;
v___y_3881_ = v___y_4152_;
v___y_3882_ = v___y_4151_;
v___y_3883_ = v___y_4161_;
v___y_3884_ = v___y_4153_;
v___y_3885_ = v___y_4162_;
v___y_3886_ = v___y_4163_;
v___y_3887_ = v___y_4154_;
v___y_3888_ = v___y_4165_;
v___y_3889_ = v___y_4164_;
v___y_3890_ = v___y_4155_;
v___y_3891_ = v___x_4179_;
goto v___jp_3869_;
}
else
{
v___y_4074_ = v___y_4141_;
v___y_4075_ = v___y_4142_;
v___y_4076_ = v___y_4143_;
v___y_4077_ = v___y_4144_;
v___y_4078_ = v___y_4145_;
v___y_4079_ = v___y_4146_;
v___y_4080_ = v___y_4147_;
v___y_4081_ = v___y_4149_;
v___y_4082_ = v___y_4150_;
v___y_4083_ = v___y_4151_;
v___y_4084_ = v___y_4152_;
v___y_4085_ = v___y_4153_;
v___y_4086_ = v___x_4176_;
v___y_4087_ = v___y_4154_;
v___y_4088_ = v___y_4155_;
v___y_4089_ = v___y_4156_;
v___y_4090_ = v___y_4157_;
v___y_4091_ = v___y_4158_;
v___y_4092_ = v_options_4170_;
v___y_4093_ = v___y_4159_;
v___y_4094_ = v___y_4160_;
v___y_4095_ = v___y_4161_;
v___y_4096_ = v___y_4162_;
v___y_4097_ = v___y_4163_;
v___y_4098_ = v___y_4165_;
v___y_4099_ = v___y_4164_;
goto v___jp_4073_;
}
}
else
{
v___y_4074_ = v___y_4141_;
v___y_4075_ = v___y_4142_;
v___y_4076_ = v___y_4143_;
v___y_4077_ = v___y_4144_;
v___y_4078_ = v___y_4145_;
v___y_4079_ = v___y_4146_;
v___y_4080_ = v___y_4147_;
v___y_4081_ = v___y_4149_;
v___y_4082_ = v___y_4150_;
v___y_4083_ = v___y_4151_;
v___y_4084_ = v___y_4152_;
v___y_4085_ = v___y_4153_;
v___y_4086_ = v___x_4176_;
v___y_4087_ = v___y_4154_;
v___y_4088_ = v___y_4155_;
v___y_4089_ = v___y_4156_;
v___y_4090_ = v___y_4157_;
v___y_4091_ = v___y_4158_;
v___y_4092_ = v_options_4170_;
v___y_4093_ = v___y_4159_;
v___y_4094_ = v___y_4160_;
v___y_4095_ = v___y_4161_;
v___y_4096_ = v___y_4162_;
v___y_4097_ = v___y_4163_;
v___y_4098_ = v___y_4165_;
v___y_4099_ = v___y_4164_;
goto v___jp_4073_;
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4191_; 
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4149_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec(v___y_4142_);
v_a_4180_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4182_ = v___x_4169_;
v_isShared_4183_ = v_isSharedCheck_4191_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4169_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4191_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4189_; 
v___x_4184_ = lean_io_error_to_string(v_a_4180_);
v___x_4185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
v___x_4186_ = l_Lean_MessageData_ofFormat(v___x_4185_);
lean_inc(v_ref_4168_);
v___x_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4187_, 0, v_ref_4168_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v___x_4187_);
v___x_4189_ = v___x_4182_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
v___jp_4192_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v_theoryState_4223_; lean_object* v_satExpr_4224_; lean_object* v_hypQueue_4225_; lean_object* v_usedHyps_4226_; uint8_t v_didChange_4227_; lean_object* v_solverTimeBudgetMs_4228_; lean_object* v_roundBudget_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4272_; 
lean_inc_ref(v___y_4198_);
v___x_4221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4221_, 0, v___y_4198_);
lean_ctor_set(v___x_4221_, 1, v___y_4204_);
lean_ctor_set(v___x_4221_, 2, v___y_4205_);
v___x_4222_ = lean_st_ref_take(v___y_4208_);
v_theoryState_4223_ = lean_ctor_get(v___x_4222_, 3);
v_satExpr_4224_ = lean_ctor_get(v___x_4222_, 0);
v_hypQueue_4225_ = lean_ctor_get(v___x_4222_, 1);
v_usedHyps_4226_ = lean_ctor_get(v___x_4222_, 2);
v_didChange_4227_ = lean_ctor_get_uint8(v___x_4222_, sizeof(void*)*6);
v_solverTimeBudgetMs_4228_ = lean_ctor_get(v___x_4222_, 4);
v_roundBudget_4229_ = lean_ctor_get(v___x_4222_, 5);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4231_ = v___x_4222_;
v_isShared_4232_ = v_isSharedCheck_4272_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_roundBudget_4229_);
lean_inc(v_solverTimeBudgetMs_4228_);
lean_inc(v_theoryState_4223_);
lean_inc(v_usedHyps_4226_);
lean_inc(v_hypQueue_4225_);
lean_inc(v_satExpr_4224_);
lean_dec(v___x_4222_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4272_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v_funState_4233_; lean_object* v_preprocessCaches_4234_; lean_object* v_satSolver_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4270_; 
v_funState_4233_ = lean_ctor_get(v_theoryState_4223_, 0);
v_preprocessCaches_4234_ = lean_ctor_get(v_theoryState_4223_, 2);
v_satSolver_4235_ = lean_ctor_get(v_theoryState_4223_, 3);
v_isSharedCheck_4270_ = !lean_is_exclusive(v_theoryState_4223_);
if (v_isSharedCheck_4270_ == 0)
{
lean_object* v_unused_4271_; 
v_unused_4271_ = lean_ctor_get(v_theoryState_4223_, 1);
lean_dec(v_unused_4271_);
v___x_4237_ = v_theoryState_4223_;
v_isShared_4238_ = v_isSharedCheck_4270_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_satSolver_4235_);
lean_inc(v_preprocessCaches_4234_);
lean_inc(v_funState_4233_);
lean_dec(v_theoryState_4223_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4270_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 1, v___x_4221_);
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_funState_4233_);
lean_ctor_set(v_reuseFailAlloc_4269_, 1, v___x_4221_);
lean_ctor_set(v_reuseFailAlloc_4269_, 2, v_preprocessCaches_4234_);
lean_ctor_set(v_reuseFailAlloc_4269_, 3, v_satSolver_4235_);
v___x_4240_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
lean_object* v___x_4242_; 
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 3, v___x_4240_);
v___x_4242_ = v___x_4231_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_satExpr_4224_);
lean_ctor_set(v_reuseFailAlloc_4268_, 1, v_hypQueue_4225_);
lean_ctor_set(v_reuseFailAlloc_4268_, 2, v_usedHyps_4226_);
lean_ctor_set(v_reuseFailAlloc_4268_, 3, v___x_4240_);
lean_ctor_set(v_reuseFailAlloc_4268_, 4, v_solverTimeBudgetMs_4228_);
lean_ctor_set(v_reuseFailAlloc_4268_, 5, v_roundBudget_4229_);
lean_ctor_set_uint8(v_reuseFailAlloc_4268_, sizeof(void*)*6, v_didChange_4227_);
v___x_4242_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = lean_st_ref_put(v___y_4208_, v___x_4242_);
v___x_4244_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Cegar_BitVec_0__Lean_Meta_Tactic_BVDecide_pushNewCnf(v___y_4196_, v___y_4199_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v___x_4245_; 
lean_dec_ref_known(v___x_4244_, 1);
v___x_4245_ = l_Lean_Meta_Tactic_BVDecide_CegarM_getSatSolver___redArg(v___y_4208_);
if (lean_obj_tag(v___x_4245_) == 0)
{
uint8_t v_invert_4246_; 
v_invert_4246_ = lean_ctor_get_uint8(v___y_4201_, sizeof(void*)*1);
if (v_invert_4246_ == 0)
{
lean_object* v_a_4247_; lean_object* v_gate_4248_; 
v_a_4247_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4247_);
lean_dec_ref_known(v___x_4245_, 1);
v_gate_4248_ = lean_ctor_get(v___y_4201_, 0);
lean_inc(v_gate_4248_);
lean_dec_ref(v___y_4201_);
v___y_4141_ = v___y_4217_;
v___y_4142_ = v___y_4194_;
v___y_4143_ = v___y_4197_;
v___y_4144_ = v___y_4198_;
v___y_4145_ = v___y_4212_;
v___y_4146_ = v___y_4211_;
v___y_4147_ = v___y_4208_;
v___y_4148_ = v_gate_4248_;
v___y_4149_ = v_a_4247_;
v___y_4150_ = v___y_4215_;
v___y_4151_ = v___y_4214_;
v___y_4152_ = v___y_4209_;
v___y_4153_ = v___y_4207_;
v___y_4154_ = v___y_4213_;
v___y_4155_ = v___y_4220_;
v___y_4156_ = v___y_4193_;
v___y_4157_ = v___y_4195_;
v___y_4158_ = v___y_4200_;
v___y_4159_ = v___y_4219_;
v___y_4160_ = v___y_4202_;
v___y_4161_ = v___y_4203_;
v___y_4162_ = v___y_4210_;
v___y_4163_ = v___y_4218_;
v___y_4164_ = v___y_4216_;
v___y_4165_ = v___y_4206_;
v___y_4166_ = v___y_4200_;
goto v___jp_4140_;
}
else
{
lean_object* v_a_4249_; lean_object* v_gate_4250_; uint8_t v___x_4251_; 
v_a_4249_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4245_, 1);
v_gate_4250_ = lean_ctor_get(v___y_4201_, 0);
lean_inc(v_gate_4250_);
lean_dec_ref(v___y_4201_);
v___x_4251_ = 0;
v___y_4141_ = v___y_4217_;
v___y_4142_ = v___y_4194_;
v___y_4143_ = v___y_4197_;
v___y_4144_ = v___y_4198_;
v___y_4145_ = v___y_4212_;
v___y_4146_ = v___y_4211_;
v___y_4147_ = v___y_4208_;
v___y_4148_ = v_gate_4250_;
v___y_4149_ = v_a_4249_;
v___y_4150_ = v___y_4215_;
v___y_4151_ = v___y_4214_;
v___y_4152_ = v___y_4209_;
v___y_4153_ = v___y_4207_;
v___y_4154_ = v___y_4213_;
v___y_4155_ = v___y_4220_;
v___y_4156_ = v___y_4193_;
v___y_4157_ = v___y_4195_;
v___y_4158_ = v___y_4200_;
v___y_4159_ = v___y_4219_;
v___y_4160_ = v___y_4202_;
v___y_4161_ = v___y_4203_;
v___y_4162_ = v___y_4210_;
v___y_4163_ = v___y_4218_;
v___y_4164_ = v___y_4216_;
v___y_4165_ = v___y_4206_;
v___y_4166_ = v___x_4251_;
goto v___jp_4140_;
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4201_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec(v___y_4194_);
v_a_4252_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4245_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4245_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4201_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec(v___y_4194_);
v_a_4260_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4244_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4244_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
}
}
}
}
v___jp_4278_:
{
if (lean_obj_tag(v___y_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v_toCold_4307_; lean_object* v_options_4308_; uint8_t v_hasTrace_4309_; 
v_a_4306_ = lean_ctor_get(v___y_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___y_4305_, 1);
v_toCold_4307_ = lean_ctor_get(v___y_4293_, 0);
v_options_4308_ = lean_ctor_get(v_toCold_4307_, 2);
v_hasTrace_4309_ = lean_ctor_get_uint8(v_options_4308_, sizeof(void*)*1);
if (v_hasTrace_4309_ == 0)
{
lean_object* v_cnf_4310_; 
v_cnf_4310_ = lean_ctor_get(v_a_4306_, 0);
lean_inc_ref(v_cnf_4310_);
v___y_4193_ = v___y_4289_;
v___y_4194_ = v___y_4279_;
v___y_4195_ = v___y_4291_;
v___y_4196_ = v___y_4280_;
v___y_4197_ = v___y_4282_;
v___y_4198_ = v___y_4281_;
v___y_4199_ = v_cnf_4310_;
v___y_4200_ = v___y_4292_;
v___y_4201_ = v___y_4297_;
v___y_4202_ = v___y_4299_;
v___y_4203_ = v___y_4302_;
v___y_4204_ = v___y_4287_;
v___y_4205_ = v_a_4306_;
v___y_4206_ = v___y_4304_;
v___y_4207_ = v___y_4300_;
v___y_4208_ = v___y_4284_;
v___y_4209_ = v___y_4294_;
v___y_4210_ = v___y_4283_;
v___y_4211_ = v___y_4288_;
v___y_4212_ = v___y_4285_;
v___y_4213_ = v___y_4296_;
v___y_4214_ = v___y_4290_;
v___y_4215_ = v___y_4286_;
v___y_4216_ = v___y_4301_;
v___y_4217_ = v___y_4303_;
v___y_4218_ = v___y_4298_;
v___y_4219_ = v___y_4293_;
v___y_4220_ = v___y_4295_;
goto v___jp_4192_;
}
else
{
lean_object* v_cnf_4311_; lean_object* v_inheritedTraceOptions_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; 
v_cnf_4311_ = lean_ctor_get(v_a_4306_, 0);
lean_inc_ref(v_cnf_4311_);
v_inheritedTraceOptions_4312_ = lean_ctor_get(v_toCold_4307_, 11);
v___x_4313_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4314_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4312_, v_options_4308_, v___x_4313_);
if (v___x_4314_ == 0)
{
v___y_4193_ = v___y_4289_;
v___y_4194_ = v___y_4279_;
v___y_4195_ = v___y_4291_;
v___y_4196_ = v___y_4280_;
v___y_4197_ = v___y_4282_;
v___y_4198_ = v___y_4281_;
v___y_4199_ = v_cnf_4311_;
v___y_4200_ = v___y_4292_;
v___y_4201_ = v___y_4297_;
v___y_4202_ = v___y_4299_;
v___y_4203_ = v___y_4302_;
v___y_4204_ = v___y_4287_;
v___y_4205_ = v_a_4306_;
v___y_4206_ = v___y_4304_;
v___y_4207_ = v___y_4300_;
v___y_4208_ = v___y_4284_;
v___y_4209_ = v___y_4294_;
v___y_4210_ = v___y_4283_;
v___y_4211_ = v___y_4288_;
v___y_4212_ = v___y_4285_;
v___y_4213_ = v___y_4296_;
v___y_4214_ = v___y_4290_;
v___y_4215_ = v___y_4286_;
v___y_4216_ = v___y_4301_;
v___y_4217_ = v___y_4303_;
v___y_4218_ = v___y_4298_;
v___y_4219_ = v___y_4293_;
v___y_4220_ = v___y_4295_;
goto v___jp_4192_;
}
else
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4315_ = lean_array_get_size(v_cnf_4311_);
v___x_4316_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__10));
v___x_4317_ = l_Nat_reprFast(v___x_4315_);
v___x_4318_ = lean_string_append(v___x_4316_, v___x_4317_);
lean_dec_ref(v___x_4317_);
v___x_4319_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__11));
v___x_4320_ = lean_string_append(v___x_4318_, v___x_4319_);
v___x_4321_ = lean_nat_sub(v___x_4315_, v___y_4280_);
v___x_4322_ = l_Nat_reprFast(v___x_4321_);
v___x_4323_ = lean_string_append(v___x_4320_, v___x_4322_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__12));
v___x_4325_ = lean_string_append(v___x_4323_, v___x_4324_);
v___x_4326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4325_);
v___x_4327_ = l_Lean_MessageData_ofFormat(v___x_4326_);
v___x_4328_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4277_, v___x_4327_, v___y_4303_, v___y_4298_, v___y_4293_, v___y_4295_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_dec_ref_known(v___x_4328_, 1);
v___y_4193_ = v___y_4289_;
v___y_4194_ = v___y_4279_;
v___y_4195_ = v___y_4291_;
v___y_4196_ = v___y_4280_;
v___y_4197_ = v___y_4282_;
v___y_4198_ = v___y_4281_;
v___y_4199_ = v_cnf_4311_;
v___y_4200_ = v___y_4292_;
v___y_4201_ = v___y_4297_;
v___y_4202_ = v___y_4299_;
v___y_4203_ = v___y_4302_;
v___y_4204_ = v___y_4287_;
v___y_4205_ = v_a_4306_;
v___y_4206_ = v___y_4304_;
v___y_4207_ = v___y_4300_;
v___y_4208_ = v___y_4284_;
v___y_4209_ = v___y_4294_;
v___y_4210_ = v___y_4283_;
v___y_4211_ = v___y_4288_;
v___y_4212_ = v___y_4285_;
v___y_4213_ = v___y_4296_;
v___y_4214_ = v___y_4290_;
v___y_4215_ = v___y_4286_;
v___y_4216_ = v___y_4301_;
v___y_4217_ = v___y_4303_;
v___y_4218_ = v___y_4298_;
v___y_4219_ = v___y_4293_;
v___y_4220_ = v___y_4295_;
goto v___jp_4192_;
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_dec_ref(v_cnf_4311_);
lean_dec(v_a_4306_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4297_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec(v___y_4279_);
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4328_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4328_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4297_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec(v___y_4279_);
v_a_4337_ = lean_ctor_get(v___y_4305_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___y_4305_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___y_4305_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___y_4305_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
v___jp_4345_:
{
lean_object* v___x_4377_; double v___x_4378_; double v___x_4379_; double v___x_4380_; double v___x_4381_; double v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4377_ = lean_io_mono_nanos_now();
v___x_4378_ = lean_float_of_nat(v___y_4375_);
v___x_4379_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4380_ = lean_float_div(v___x_4378_, v___x_4379_);
v___x_4381_ = lean_float_of_nat(v___x_4377_);
v___x_4382_ = lean_float_div(v___x_4381_, v___x_4379_);
v___x_4383_ = lean_box_float(v___x_4380_);
v___x_4384_ = lean_box_float(v___x_4382_);
v___x_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4383_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4386_, 0, v_a_4376_);
lean_ctor_set(v___x_4386_, 1, v___x_4385_);
lean_inc_ref(v___y_4369_);
lean_inc(v___y_4360_);
v___x_4387_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_4360_, v___y_4361_, v___y_4369_, v___y_4348_, v___y_4362_, v___y_4352_, v___f_3994_, v___x_4386_, v___y_4370_, v___y_4354_, v___y_4364_, v___y_4351_, v___y_4357_, v___y_4353_, v___y_4365_, v___y_4359_, v___y_4355_, v___y_4371_, v___y_4373_, v___y_4368_, v___y_4363_, v___y_4366_);
v___y_4279_ = v___y_4346_;
v___y_4280_ = v___y_4347_;
v___y_4281_ = v___y_4349_;
v___y_4282_ = v___y_4350_;
v___y_4283_ = v___y_4351_;
v___y_4284_ = v___y_4354_;
v___y_4285_ = v___y_4353_;
v___y_4286_ = v___y_4355_;
v___y_4287_ = v___y_4356_;
v___y_4288_ = v___y_4357_;
v___y_4289_ = v___y_4358_;
v___y_4290_ = v___y_4359_;
v___y_4291_ = v___y_4360_;
v___y_4292_ = v___y_4361_;
v___y_4293_ = v___y_4363_;
v___y_4294_ = v___y_4364_;
v___y_4295_ = v___y_4366_;
v___y_4296_ = v___y_4365_;
v___y_4297_ = v___y_4367_;
v___y_4298_ = v___y_4368_;
v___y_4299_ = v___y_4369_;
v___y_4300_ = v___y_4370_;
v___y_4301_ = v___y_4371_;
v___y_4302_ = v___y_4372_;
v___y_4303_ = v___y_4373_;
v___y_4304_ = v___y_4374_;
v___y_4305_ = v___x_4387_;
goto v___jp_4278_;
}
v___jp_4388_:
{
lean_object* v___x_4420_; double v___x_4421_; double v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4420_ = lean_io_get_num_heartbeats();
v___x_4421_ = lean_float_of_nat(v___y_4417_);
v___x_4422_ = lean_float_of_nat(v___x_4420_);
v___x_4423_ = lean_box_float(v___x_4421_);
v___x_4424_ = lean_box_float(v___x_4422_);
v___x_4425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
v___x_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4426_, 0, v_a_4419_);
lean_ctor_set(v___x_4426_, 1, v___x_4425_);
lean_inc_ref(v___y_4412_);
lean_inc(v___y_4403_);
v___x_4427_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__7(v___y_4403_, v___y_4404_, v___y_4412_, v___y_4391_, v___y_4405_, v___y_4395_, v___f_3994_, v___x_4426_, v___y_4413_, v___y_4397_, v___y_4407_, v___y_4394_, v___y_4400_, v___y_4396_, v___y_4408_, v___y_4402_, v___y_4398_, v___y_4414_, v___y_4416_, v___y_4411_, v___y_4406_, v___y_4409_);
v___y_4279_ = v___y_4389_;
v___y_4280_ = v___y_4390_;
v___y_4281_ = v___y_4392_;
v___y_4282_ = v___y_4393_;
v___y_4283_ = v___y_4394_;
v___y_4284_ = v___y_4397_;
v___y_4285_ = v___y_4396_;
v___y_4286_ = v___y_4398_;
v___y_4287_ = v___y_4399_;
v___y_4288_ = v___y_4400_;
v___y_4289_ = v___y_4401_;
v___y_4290_ = v___y_4402_;
v___y_4291_ = v___y_4403_;
v___y_4292_ = v___y_4404_;
v___y_4293_ = v___y_4406_;
v___y_4294_ = v___y_4407_;
v___y_4295_ = v___y_4409_;
v___y_4296_ = v___y_4408_;
v___y_4297_ = v___y_4410_;
v___y_4298_ = v___y_4411_;
v___y_4299_ = v___y_4412_;
v___y_4300_ = v___y_4413_;
v___y_4301_ = v___y_4414_;
v___y_4302_ = v___y_4415_;
v___y_4303_ = v___y_4416_;
v___y_4304_ = v___y_4418_;
v___y_4305_ = v___x_4427_;
goto v___jp_4278_;
}
v___jp_4428_:
{
lean_object* v___x_4459_; lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4514_; 
v___x_4459_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4450_);
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4462_ = v___x_4459_;
v_isShared_4463_ = v_isSharedCheck_4514_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4514_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; uint8_t v___x_4465_; 
v___x_4464_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4465_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4431_, v___x_4464_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4466_ = lean_io_mono_nanos_now();
v___x_4467_ = l_IO_lazyPure___redArg(v___y_4448_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_del_object(v___x_4462_);
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4467_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4467_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
lean_ctor_set_tag(v___x_4470_, 1);
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
v___y_4346_ = v___y_4429_;
v___y_4347_ = v___y_4430_;
v___y_4348_ = v___y_4431_;
v___y_4349_ = v___y_4432_;
v___y_4350_ = v___y_4433_;
v___y_4351_ = v___y_4434_;
v___y_4352_ = v_a_4460_;
v___y_4353_ = v___y_4436_;
v___y_4354_ = v___y_4437_;
v___y_4355_ = v___y_4435_;
v___y_4356_ = v___y_4439_;
v___y_4357_ = v___y_4438_;
v___y_4358_ = v___y_4441_;
v___y_4359_ = v___y_4440_;
v___y_4360_ = v___y_4442_;
v___y_4361_ = v___y_4443_;
v___y_4362_ = v___y_4444_;
v___y_4363_ = v___y_4445_;
v___y_4364_ = v___y_4446_;
v___y_4365_ = v___y_4449_;
v___y_4366_ = v___y_4450_;
v___y_4367_ = v___y_4451_;
v___y_4368_ = v___y_4452_;
v___y_4369_ = v___y_4453_;
v___y_4370_ = v___y_4455_;
v___y_4371_ = v___y_4454_;
v___y_4372_ = v___y_4456_;
v___y_4373_ = v___y_4457_;
v___y_4374_ = v___y_4458_;
v___y_4375_ = v___x_4466_;
v_a_4376_ = v___x_4473_;
goto v___jp_4345_;
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4489_; 
v_a_4476_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4478_ = v___x_4467_;
v_isShared_4479_ = v_isSharedCheck_4489_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4467_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4489_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4480_ = lean_io_error_to_string(v_a_4476_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set_tag(v___x_4478_, 3);
lean_ctor_set(v___x_4478_, 0, v___x_4480_);
v___x_4482_ = v___x_4478_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4483_ = l_Lean_MessageData_ofFormat(v___x_4482_);
lean_inc(v___y_4447_);
v___x_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___y_4447_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4484_);
v___x_4486_ = v___x_4462_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
v___y_4346_ = v___y_4429_;
v___y_4347_ = v___y_4430_;
v___y_4348_ = v___y_4431_;
v___y_4349_ = v___y_4432_;
v___y_4350_ = v___y_4433_;
v___y_4351_ = v___y_4434_;
v___y_4352_ = v_a_4460_;
v___y_4353_ = v___y_4436_;
v___y_4354_ = v___y_4437_;
v___y_4355_ = v___y_4435_;
v___y_4356_ = v___y_4439_;
v___y_4357_ = v___y_4438_;
v___y_4358_ = v___y_4441_;
v___y_4359_ = v___y_4440_;
v___y_4360_ = v___y_4442_;
v___y_4361_ = v___y_4443_;
v___y_4362_ = v___y_4444_;
v___y_4363_ = v___y_4445_;
v___y_4364_ = v___y_4446_;
v___y_4365_ = v___y_4449_;
v___y_4366_ = v___y_4450_;
v___y_4367_ = v___y_4451_;
v___y_4368_ = v___y_4452_;
v___y_4369_ = v___y_4453_;
v___y_4370_ = v___y_4455_;
v___y_4371_ = v___y_4454_;
v___y_4372_ = v___y_4456_;
v___y_4373_ = v___y_4457_;
v___y_4374_ = v___y_4458_;
v___y_4375_ = v___x_4466_;
v_a_4376_ = v___x_4486_;
goto v___jp_4345_;
}
}
}
}
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = lean_io_get_num_heartbeats();
v___x_4491_ = l_IO_lazyPure___redArg(v___y_4448_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_del_object(v___x_4462_);
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4491_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4491_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
lean_ctor_set_tag(v___x_4494_, 1);
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
v___y_4389_ = v___y_4429_;
v___y_4390_ = v___y_4430_;
v___y_4391_ = v___y_4431_;
v___y_4392_ = v___y_4432_;
v___y_4393_ = v___y_4433_;
v___y_4394_ = v___y_4434_;
v___y_4395_ = v_a_4460_;
v___y_4396_ = v___y_4436_;
v___y_4397_ = v___y_4437_;
v___y_4398_ = v___y_4435_;
v___y_4399_ = v___y_4439_;
v___y_4400_ = v___y_4438_;
v___y_4401_ = v___y_4441_;
v___y_4402_ = v___y_4440_;
v___y_4403_ = v___y_4442_;
v___y_4404_ = v___y_4443_;
v___y_4405_ = v___y_4444_;
v___y_4406_ = v___y_4445_;
v___y_4407_ = v___y_4446_;
v___y_4408_ = v___y_4449_;
v___y_4409_ = v___y_4450_;
v___y_4410_ = v___y_4451_;
v___y_4411_ = v___y_4452_;
v___y_4412_ = v___y_4453_;
v___y_4413_ = v___y_4455_;
v___y_4414_ = v___y_4454_;
v___y_4415_ = v___y_4456_;
v___y_4416_ = v___y_4457_;
v___y_4417_ = v___x_4490_;
v___y_4418_ = v___y_4458_;
v_a_4419_ = v___x_4497_;
goto v___jp_4388_;
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4513_; 
v_a_4500_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4502_ = v___x_4491_;
v_isShared_4503_ = v_isSharedCheck_4513_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4491_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4513_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; lean_object* v___x_4506_; 
v___x_4504_ = lean_io_error_to_string(v_a_4500_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set_tag(v___x_4502_, 3);
lean_ctor_set(v___x_4502_, 0, v___x_4504_);
v___x_4506_ = v___x_4502_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4507_ = l_Lean_MessageData_ofFormat(v___x_4506_);
lean_inc(v___y_4447_);
v___x_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___y_4447_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4508_);
v___x_4510_ = v___x_4462_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
v___y_4389_ = v___y_4429_;
v___y_4390_ = v___y_4430_;
v___y_4391_ = v___y_4431_;
v___y_4392_ = v___y_4432_;
v___y_4393_ = v___y_4433_;
v___y_4394_ = v___y_4434_;
v___y_4395_ = v_a_4460_;
v___y_4396_ = v___y_4436_;
v___y_4397_ = v___y_4437_;
v___y_4398_ = v___y_4435_;
v___y_4399_ = v___y_4439_;
v___y_4400_ = v___y_4438_;
v___y_4401_ = v___y_4441_;
v___y_4402_ = v___y_4440_;
v___y_4403_ = v___y_4442_;
v___y_4404_ = v___y_4443_;
v___y_4405_ = v___y_4444_;
v___y_4406_ = v___y_4445_;
v___y_4407_ = v___y_4446_;
v___y_4408_ = v___y_4449_;
v___y_4409_ = v___y_4450_;
v___y_4410_ = v___y_4451_;
v___y_4411_ = v___y_4452_;
v___y_4412_ = v___y_4453_;
v___y_4413_ = v___y_4455_;
v___y_4414_ = v___y_4454_;
v___y_4415_ = v___y_4456_;
v___y_4416_ = v___y_4457_;
v___y_4417_ = v___x_4490_;
v___y_4418_ = v___y_4458_;
v_a_4419_ = v___x_4510_;
goto v___jp_4388_;
}
}
}
}
}
}
}
v___jp_4515_:
{
lean_object* v_toCold_4542_; lean_object* v_options_4543_; lean_object* v_cnf_4544_; lean_object* v_ref_4545_; lean_object* v_inheritedTraceOptions_4546_; uint8_t v_hasTrace_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___f_4551_; lean_object* v___x_4552_; 
v_toCold_4542_ = lean_ctor_get(v___y_4540_, 0);
v_options_4543_ = lean_ctor_get(v_toCold_4542_, 2);
v_cnf_4544_ = lean_ctor_get(v___y_4518_, 0);
v_ref_4545_ = lean_ctor_get(v___y_4540_, 2);
v_inheritedTraceOptions_4546_ = lean_ctor_get(v_toCold_4542_, 11);
v_hasTrace_4547_ = lean_ctor_get_uint8(v_options_4543_, sizeof(void*)*1);
v___x_4548_ = lean_array_get_size(v_cnf_4544_);
v___x_4549_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_4550_ = l_Std_Sat_AIG_toCNF_State_cast___redArg(v___y_4523_, v___y_4518_);
v___f_4551_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__3___boxed), 5, 4);
lean_closure_set(v___f_4551_, 0, v___x_4274_);
lean_closure_set(v___f_4551_, 1, v___x_4549_);
lean_closure_set(v___f_4551_, 2, v___y_4516_);
lean_closure_set(v___f_4551_, 3, v___x_4550_);
v___x_4552_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__9));
if (v_hasTrace_4547_ == 0)
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_4551_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
v___y_4279_ = v___y_4519_;
v___y_4280_ = v___x_4548_;
v___y_4281_ = v___y_4523_;
v___y_4282_ = v___y_4522_;
v___y_4283_ = v___y_4531_;
v___y_4284_ = v___y_4529_;
v___y_4285_ = v___y_4533_;
v___y_4286_ = v___y_4536_;
v___y_4287_ = v___y_4526_;
v___y_4288_ = v___y_4532_;
v___y_4289_ = v___y_4517_;
v___y_4290_ = v___y_4535_;
v___y_4291_ = v___x_4552_;
v___y_4292_ = v___y_4524_;
v___y_4293_ = v___y_4540_;
v___y_4294_ = v___y_4530_;
v___y_4295_ = v___y_4541_;
v___y_4296_ = v___y_4534_;
v___y_4297_ = v___y_4520_;
v___y_4298_ = v___y_4539_;
v___y_4299_ = v___y_4521_;
v___y_4300_ = v___y_4528_;
v___y_4301_ = v___y_4537_;
v___y_4302_ = v___y_4525_;
v___y_4303_ = v___y_4538_;
v___y_4304_ = v___y_4527_;
v___y_4305_ = v___x_4553_;
goto v___jp_4278_;
}
else
{
lean_object* v___x_4554_; uint8_t v___x_4555_; 
v___x_4554_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__10);
v___x_4555_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4546_, v_options_4543_, v___x_4554_);
if (v___x_4555_ == 0)
{
lean_object* v___x_4556_; uint8_t v___x_4557_; 
v___x_4556_ = l_Lean_trace_profiler;
v___x_4557_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4543_, v___x_4556_);
if (v___x_4557_ == 0)
{
lean_object* v___x_4558_; 
v___x_4558_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__4(v___f_4551_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
v___y_4279_ = v___y_4519_;
v___y_4280_ = v___x_4548_;
v___y_4281_ = v___y_4523_;
v___y_4282_ = v___y_4522_;
v___y_4283_ = v___y_4531_;
v___y_4284_ = v___y_4529_;
v___y_4285_ = v___y_4533_;
v___y_4286_ = v___y_4536_;
v___y_4287_ = v___y_4526_;
v___y_4288_ = v___y_4532_;
v___y_4289_ = v___y_4517_;
v___y_4290_ = v___y_4535_;
v___y_4291_ = v___x_4552_;
v___y_4292_ = v___y_4524_;
v___y_4293_ = v___y_4540_;
v___y_4294_ = v___y_4530_;
v___y_4295_ = v___y_4541_;
v___y_4296_ = v___y_4534_;
v___y_4297_ = v___y_4520_;
v___y_4298_ = v___y_4539_;
v___y_4299_ = v___y_4521_;
v___y_4300_ = v___y_4528_;
v___y_4301_ = v___y_4537_;
v___y_4302_ = v___y_4525_;
v___y_4303_ = v___y_4538_;
v___y_4304_ = v___y_4527_;
v___y_4305_ = v___x_4558_;
goto v___jp_4278_;
}
else
{
v___y_4429_ = v___y_4519_;
v___y_4430_ = v___x_4548_;
v___y_4431_ = v_options_4543_;
v___y_4432_ = v___y_4523_;
v___y_4433_ = v___y_4522_;
v___y_4434_ = v___y_4531_;
v___y_4435_ = v___y_4536_;
v___y_4436_ = v___y_4533_;
v___y_4437_ = v___y_4529_;
v___y_4438_ = v___y_4532_;
v___y_4439_ = v___y_4526_;
v___y_4440_ = v___y_4535_;
v___y_4441_ = v___y_4517_;
v___y_4442_ = v___x_4552_;
v___y_4443_ = v___y_4524_;
v___y_4444_ = v___x_4555_;
v___y_4445_ = v___y_4540_;
v___y_4446_ = v___y_4530_;
v___y_4447_ = v_ref_4545_;
v___y_4448_ = v___f_4551_;
v___y_4449_ = v___y_4534_;
v___y_4450_ = v___y_4541_;
v___y_4451_ = v___y_4520_;
v___y_4452_ = v___y_4539_;
v___y_4453_ = v___y_4521_;
v___y_4454_ = v___y_4537_;
v___y_4455_ = v___y_4528_;
v___y_4456_ = v___y_4525_;
v___y_4457_ = v___y_4538_;
v___y_4458_ = v___y_4527_;
goto v___jp_4428_;
}
}
else
{
v___y_4429_ = v___y_4519_;
v___y_4430_ = v___x_4548_;
v___y_4431_ = v_options_4543_;
v___y_4432_ = v___y_4523_;
v___y_4433_ = v___y_4522_;
v___y_4434_ = v___y_4531_;
v___y_4435_ = v___y_4536_;
v___y_4436_ = v___y_4533_;
v___y_4437_ = v___y_4529_;
v___y_4438_ = v___y_4532_;
v___y_4439_ = v___y_4526_;
v___y_4440_ = v___y_4535_;
v___y_4441_ = v___y_4517_;
v___y_4442_ = v___x_4552_;
v___y_4443_ = v___y_4524_;
v___y_4444_ = v___x_4555_;
v___y_4445_ = v___y_4540_;
v___y_4446_ = v___y_4530_;
v___y_4447_ = v_ref_4545_;
v___y_4448_ = v___f_4551_;
v___y_4449_ = v___y_4534_;
v___y_4450_ = v___y_4541_;
v___y_4451_ = v___y_4520_;
v___y_4452_ = v___y_4539_;
v___y_4453_ = v___y_4521_;
v___y_4454_ = v___y_4537_;
v___y_4455_ = v___y_4528_;
v___y_4456_ = v___y_4525_;
v___y_4457_ = v___y_4538_;
v___y_4458_ = v___y_4527_;
goto v___jp_4428_;
}
}
}
v___jp_4559_:
{
lean_object* v_config_4587_; uint8_t v_graphviz_4588_; 
v_config_4587_ = lean_ctor_get(v___y_4561_, 5);
v_graphviz_4588_ = lean_ctor_get_uint8(v_config_4587_, sizeof(void*)*3 + 8);
if (v_graphviz_4588_ == 0)
{
lean_dec_ref(v___y_4568_);
v___y_4516_ = v___y_4560_;
v___y_4517_ = v___y_4561_;
v___y_4518_ = v___y_4562_;
v___y_4519_ = v___y_4563_;
v___y_4520_ = v___y_4564_;
v___y_4521_ = v___y_4567_;
v___y_4522_ = v___y_4566_;
v___y_4523_ = v___y_4565_;
v___y_4524_ = v___y_4569_;
v___y_4525_ = v___y_4570_;
v___y_4526_ = v___y_4571_;
v___y_4527_ = v___y_4572_;
v___y_4528_ = v___y_4573_;
v___y_4529_ = v___y_4574_;
v___y_4530_ = v___y_4575_;
v___y_4531_ = v___y_4576_;
v___y_4532_ = v___y_4577_;
v___y_4533_ = v___y_4578_;
v___y_4534_ = v___y_4579_;
v___y_4535_ = v___y_4580_;
v___y_4536_ = v___y_4581_;
v___y_4537_ = v___y_4582_;
v___y_4538_ = v___y_4583_;
v___y_4539_ = v___y_4584_;
v___y_4540_ = v___y_4585_;
v___y_4541_ = v___y_4586_;
goto v___jp_4515_;
}
else
{
lean_object* v_ref_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v_ref_4589_ = lean_ctor_get(v___y_4585_, 2);
v___x_4590_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__16);
v___x_4591_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8(v___y_4568_);
v___x_4592_ = l_IO_FS_writeFile(v___x_4590_, v___x_4591_);
lean_dec_ref(v___x_4591_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_dec_ref_known(v___x_4592_, 1);
v___y_4516_ = v___y_4560_;
v___y_4517_ = v___y_4561_;
v___y_4518_ = v___y_4562_;
v___y_4519_ = v___y_4563_;
v___y_4520_ = v___y_4564_;
v___y_4521_ = v___y_4567_;
v___y_4522_ = v___y_4566_;
v___y_4523_ = v___y_4565_;
v___y_4524_ = v___y_4569_;
v___y_4525_ = v___y_4570_;
v___y_4526_ = v___y_4571_;
v___y_4527_ = v___y_4572_;
v___y_4528_ = v___y_4573_;
v___y_4529_ = v___y_4574_;
v___y_4530_ = v___y_4575_;
v___y_4531_ = v___y_4576_;
v___y_4532_ = v___y_4577_;
v___y_4533_ = v___y_4578_;
v___y_4534_ = v___y_4579_;
v___y_4535_ = v___y_4580_;
v___y_4536_ = v___y_4581_;
v___y_4537_ = v___y_4582_;
v___y_4538_ = v___y_4583_;
v___y_4539_ = v___y_4584_;
v___y_4540_ = v___y_4585_;
v___y_4541_ = v___y_4586_;
goto v___jp_4515_;
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4604_; 
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec_ref(v___y_4560_);
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4595_ = v___x_4592_;
v_isShared_4596_ = v_isSharedCheck_4604_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4592_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4604_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4597_ = lean_io_error_to_string(v_a_4593_);
v___x_4598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4597_);
v___x_4599_ = l_Lean_MessageData_ofFormat(v___x_4598_);
lean_inc(v_ref_4589_);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v_ref_4589_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 0, v___x_4600_);
v___x_4602_ = v___x_4595_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
}
v___jp_4605_:
{
if (lean_obj_tag(v___y_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v_result_4630_; lean_object* v_aig_4631_; lean_object* v_toCold_4632_; lean_object* v_options_4633_; lean_object* v_cache_4634_; lean_object* v_ref_4635_; lean_object* v_decls_4636_; lean_object* v_inheritedTraceOptions_4637_; uint8_t v_hasTrace_4638_; lean_object* v___x_4639_; 
v_a_4629_ = lean_ctor_get(v___y_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref_known(v___y_4628_, 1);
v_result_4630_ = lean_ctor_get(v_a_4629_, 0);
lean_inc_ref(v_result_4630_);
v_aig_4631_ = lean_ctor_get(v_result_4630_, 0);
lean_inc_ref(v_aig_4631_);
v_toCold_4632_ = lean_ctor_get(v___y_4619_, 0);
v_options_4633_ = lean_ctor_get(v_toCold_4632_, 2);
v_cache_4634_ = lean_ctor_get(v_a_4629_, 1);
lean_inc_ref(v_cache_4634_);
lean_dec(v_a_4629_);
v_ref_4635_ = lean_ctor_get(v_result_4630_, 1);
lean_inc_ref(v_ref_4635_);
v_decls_4636_ = lean_ctor_get(v_aig_4631_, 0);
v_inheritedTraceOptions_4637_ = lean_ctor_get(v_toCold_4632_, 11);
v_hasTrace_4638_ = lean_ctor_get_uint8(v_options_4633_, sizeof(void*)*1);
v___x_4639_ = lean_array_get_size(v_decls_4636_);
if (v_hasTrace_4638_ == 0)
{
lean_dec(v___y_4608_);
lean_inc_ref(v_result_4630_);
v___y_4560_ = v_result_4630_;
v___y_4561_ = v___y_4606_;
v___y_4562_ = v___y_4616_;
v___y_4563_ = v___y_4607_;
v___y_4564_ = v_ref_4635_;
v___y_4565_ = v_aig_4631_;
v___y_4566_ = v___y_4609_;
v___y_4567_ = v___y_4618_;
v___y_4568_ = v_result_4630_;
v___y_4569_ = v___y_4611_;
v___y_4570_ = v___x_4639_;
v___y_4571_ = v_cache_4634_;
v___y_4572_ = v___y_4626_;
v___y_4573_ = v___y_4620_;
v___y_4574_ = v___y_4613_;
v___y_4575_ = v___y_4622_;
v___y_4576_ = v___y_4623_;
v___y_4577_ = v___y_4621_;
v___y_4578_ = v___y_4612_;
v___y_4579_ = v___y_4625_;
v___y_4580_ = v___y_4624_;
v___y_4581_ = v___y_4614_;
v___y_4582_ = v___y_4615_;
v___y_4583_ = v___y_4617_;
v___y_4584_ = v___y_4627_;
v___y_4585_ = v___y_4619_;
v___y_4586_ = v___y_4610_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4640_; uint8_t v___x_4641_; 
v___x_4640_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4641_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4637_, v_options_4633_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_dec(v___y_4608_);
lean_inc_ref(v_result_4630_);
v___y_4560_ = v_result_4630_;
v___y_4561_ = v___y_4606_;
v___y_4562_ = v___y_4616_;
v___y_4563_ = v___y_4607_;
v___y_4564_ = v_ref_4635_;
v___y_4565_ = v_aig_4631_;
v___y_4566_ = v___y_4609_;
v___y_4567_ = v___y_4618_;
v___y_4568_ = v_result_4630_;
v___y_4569_ = v___y_4611_;
v___y_4570_ = v___x_4639_;
v___y_4571_ = v_cache_4634_;
v___y_4572_ = v___y_4626_;
v___y_4573_ = v___y_4620_;
v___y_4574_ = v___y_4613_;
v___y_4575_ = v___y_4622_;
v___y_4576_ = v___y_4623_;
v___y_4577_ = v___y_4621_;
v___y_4578_ = v___y_4612_;
v___y_4579_ = v___y_4625_;
v___y_4580_ = v___y_4624_;
v___y_4581_ = v___y_4614_;
v___y_4582_ = v___y_4615_;
v___y_4583_ = v___y_4617_;
v___y_4584_ = v___y_4627_;
v___y_4585_ = v___y_4619_;
v___y_4586_ = v___y_4610_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4642_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__11));
v___x_4643_ = l_Nat_reprFast(v___x_4639_);
v___x_4644_ = lean_string_append(v___x_4642_, v___x_4643_);
lean_dec_ref(v___x_4643_);
v___x_4645_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__12));
v___x_4646_ = lean_string_append(v___x_4644_, v___x_4645_);
v___x_4647_ = lean_nat_sub(v___x_4639_, v___y_4608_);
lean_dec(v___y_4608_);
v___x_4648_ = l_Nat_reprFast(v___x_4647_);
v___x_4649_ = lean_string_append(v___x_4646_, v___x_4648_);
lean_dec_ref(v___x_4648_);
v___x_4650_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__13));
v___x_4651_ = lean_string_append(v___x_4649_, v___x_4650_);
v___x_4652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
v___x_4653_ = l_Lean_MessageData_ofFormat(v___x_4652_);
v___x_4654_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_4277_, v___x_4653_, v___y_4617_, v___y_4627_, v___y_4619_, v___y_4610_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_dec_ref_known(v___x_4654_, 1);
lean_inc_ref(v_result_4630_);
v___y_4560_ = v_result_4630_;
v___y_4561_ = v___y_4606_;
v___y_4562_ = v___y_4616_;
v___y_4563_ = v___y_4607_;
v___y_4564_ = v_ref_4635_;
v___y_4565_ = v_aig_4631_;
v___y_4566_ = v___y_4609_;
v___y_4567_ = v___y_4618_;
v___y_4568_ = v_result_4630_;
v___y_4569_ = v___y_4611_;
v___y_4570_ = v___x_4639_;
v___y_4571_ = v_cache_4634_;
v___y_4572_ = v___y_4626_;
v___y_4573_ = v___y_4620_;
v___y_4574_ = v___y_4613_;
v___y_4575_ = v___y_4622_;
v___y_4576_ = v___y_4623_;
v___y_4577_ = v___y_4621_;
v___y_4578_ = v___y_4612_;
v___y_4579_ = v___y_4625_;
v___y_4580_ = v___y_4624_;
v___y_4581_ = v___y_4614_;
v___y_4582_ = v___y_4615_;
v___y_4583_ = v___y_4617_;
v___y_4584_ = v___y_4627_;
v___y_4585_ = v___y_4619_;
v___y_4586_ = v___y_4610_;
goto v___jp_4559_;
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
lean_dec_ref(v_ref_4635_);
lean_dec_ref(v_cache_4634_);
lean_dec_ref(v_aig_4631_);
lean_dec_ref(v_result_4630_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4609_);
lean_dec(v___y_4607_);
v_a_4655_ = lean_ctor_get(v___x_4654_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4654_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4654_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec(v___y_4607_);
v_a_4663_ = lean_ctor_get(v___y_4628_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___y_4628_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___y_4628_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___y_4628_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
v___jp_4671_:
{
lean_object* v___x_4699_; double v___x_4700_; double v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4699_ = lean_io_get_num_heartbeats();
v___x_4700_ = lean_float_of_nat(v___y_4686_);
v___x_4701_ = lean_float_of_nat(v___x_4699_);
v___x_4702_ = lean_box_float(v___x_4700_);
v___x_4703_ = lean_box_float(v___x_4701_);
v___x_4704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4702_);
lean_ctor_set(v___x_4704_, 1, v___x_4703_);
v___x_4705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4705_, 0, v_a_4698_);
lean_ctor_set(v___x_4705_, 1, v___x_4704_);
lean_inc_ref(v___y_4688_);
v___x_4706_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4277_, v___y_4682_, v___y_4688_, v___y_4696_, v___y_4678_, v___y_4692_, v___f_4273_, v___x_4705_, v___y_4680_, v___y_4684_, v___y_4691_, v___y_4690_, v___y_4679_, v___y_4683_, v___y_4693_, v___y_4694_, v___y_4676_, v___y_4685_, v___y_4687_, v___y_4697_, v___y_4689_, v___y_4675_);
v___y_4606_ = v___y_4681_;
v___y_4607_ = v___y_4672_;
v___y_4608_ = v___y_4673_;
v___y_4609_ = v___y_4674_;
v___y_4610_ = v___y_4675_;
v___y_4611_ = v___y_4682_;
v___y_4612_ = v___y_4683_;
v___y_4613_ = v___y_4684_;
v___y_4614_ = v___y_4676_;
v___y_4615_ = v___y_4685_;
v___y_4616_ = v___y_4677_;
v___y_4617_ = v___y_4687_;
v___y_4618_ = v___y_4688_;
v___y_4619_ = v___y_4689_;
v___y_4620_ = v___y_4680_;
v___y_4621_ = v___y_4679_;
v___y_4622_ = v___y_4691_;
v___y_4623_ = v___y_4690_;
v___y_4624_ = v___y_4694_;
v___y_4625_ = v___y_4693_;
v___y_4626_ = v___y_4695_;
v___y_4627_ = v___y_4697_;
v___y_4628_ = v___x_4706_;
goto v___jp_4605_;
}
v___jp_4707_:
{
lean_object* v___x_4735_; double v___x_4736_; double v___x_4737_; double v___x_4738_; double v___x_4739_; double v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4735_ = lean_io_mono_nanos_now();
v___x_4736_ = lean_float_of_nat(v___y_4722_);
v___x_4737_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__16___closed__9);
v___x_4738_ = lean_float_div(v___x_4736_, v___x_4737_);
v___x_4739_ = lean_float_of_nat(v___x_4735_);
v___x_4740_ = lean_float_div(v___x_4739_, v___x_4737_);
v___x_4741_ = lean_box_float(v___x_4738_);
v___x_4742_ = lean_box_float(v___x_4740_);
v___x_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4741_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4744_, 0, v_a_4734_);
lean_ctor_set(v___x_4744_, 1, v___x_4743_);
lean_inc_ref(v___y_4724_);
v___x_4745_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__9(v_cls_4277_, v___y_4718_, v___y_4724_, v___y_4732_, v___y_4714_, v___y_4728_, v___f_4273_, v___x_4744_, v___y_4716_, v___y_4720_, v___y_4727_, v___y_4726_, v___y_4715_, v___y_4719_, v___y_4729_, v___y_4730_, v___y_4712_, v___y_4721_, v___y_4723_, v___y_4733_, v___y_4725_, v___y_4711_);
v___y_4606_ = v___y_4717_;
v___y_4607_ = v___y_4708_;
v___y_4608_ = v___y_4709_;
v___y_4609_ = v___y_4710_;
v___y_4610_ = v___y_4711_;
v___y_4611_ = v___y_4718_;
v___y_4612_ = v___y_4719_;
v___y_4613_ = v___y_4720_;
v___y_4614_ = v___y_4712_;
v___y_4615_ = v___y_4721_;
v___y_4616_ = v___y_4713_;
v___y_4617_ = v___y_4723_;
v___y_4618_ = v___y_4724_;
v___y_4619_ = v___y_4725_;
v___y_4620_ = v___y_4716_;
v___y_4621_ = v___y_4715_;
v___y_4622_ = v___y_4727_;
v___y_4623_ = v___y_4726_;
v___y_4624_ = v___y_4730_;
v___y_4625_ = v___y_4729_;
v___y_4626_ = v___y_4731_;
v___y_4627_ = v___y_4733_;
v___y_4628_ = v___x_4745_;
goto v___jp_4605_;
}
v___jp_4746_:
{
lean_object* v___x_4773_; lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4828_; 
v___x_4773_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__4___redArg(v___y_4750_);
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4776_ = v___x_4773_;
v_isShared_4777_ = v_isSharedCheck_4828_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4773_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4828_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4778_; uint8_t v___x_4779_; 
v___x_4778_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4779_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v___y_4772_, v___x_4778_);
if (v___x_4779_ == 0)
{
lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4780_ = lean_io_mono_nanos_now();
v___x_4781_ = l_IO_lazyPure___redArg(v___y_4751_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_del_object(v___x_4776_);
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4781_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4781_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
lean_ctor_set_tag(v___x_4784_, 1);
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
v___y_4708_ = v___y_4747_;
v___y_4709_ = v___y_4748_;
v___y_4710_ = v___y_4749_;
v___y_4711_ = v___y_4750_;
v___y_4712_ = v___y_4752_;
v___y_4713_ = v___y_4753_;
v___y_4714_ = v___y_4754_;
v___y_4715_ = v___y_4755_;
v___y_4716_ = v___y_4756_;
v___y_4717_ = v___y_4757_;
v___y_4718_ = v___y_4758_;
v___y_4719_ = v___y_4760_;
v___y_4720_ = v___y_4761_;
v___y_4721_ = v___y_4762_;
v___y_4722_ = v___x_4780_;
v___y_4723_ = v___y_4763_;
v___y_4724_ = v___y_4764_;
v___y_4725_ = v___y_4765_;
v___y_4726_ = v___y_4766_;
v___y_4727_ = v___y_4767_;
v___y_4728_ = v_a_4774_;
v___y_4729_ = v___y_4769_;
v___y_4730_ = v___y_4768_;
v___y_4731_ = v___y_4770_;
v___y_4732_ = v___y_4772_;
v___y_4733_ = v___y_4771_;
v_a_4734_ = v___x_4787_;
goto v___jp_4707_;
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4803_; 
v_a_4790_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4792_ = v___x_4781_;
v_isShared_4793_ = v_isSharedCheck_4803_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4781_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4803_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4796_; 
v___x_4794_ = lean_io_error_to_string(v_a_4790_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set_tag(v___x_4792_, 3);
lean_ctor_set(v___x_4792_, 0, v___x_4794_);
v___x_4796_ = v___x_4792_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4794_);
v___x_4796_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4800_; 
v___x_4797_ = l_Lean_MessageData_ofFormat(v___x_4796_);
lean_inc(v___y_4759_);
v___x_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___y_4759_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 0, v___x_4798_);
v___x_4800_ = v___x_4776_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
v___y_4708_ = v___y_4747_;
v___y_4709_ = v___y_4748_;
v___y_4710_ = v___y_4749_;
v___y_4711_ = v___y_4750_;
v___y_4712_ = v___y_4752_;
v___y_4713_ = v___y_4753_;
v___y_4714_ = v___y_4754_;
v___y_4715_ = v___y_4755_;
v___y_4716_ = v___y_4756_;
v___y_4717_ = v___y_4757_;
v___y_4718_ = v___y_4758_;
v___y_4719_ = v___y_4760_;
v___y_4720_ = v___y_4761_;
v___y_4721_ = v___y_4762_;
v___y_4722_ = v___x_4780_;
v___y_4723_ = v___y_4763_;
v___y_4724_ = v___y_4764_;
v___y_4725_ = v___y_4765_;
v___y_4726_ = v___y_4766_;
v___y_4727_ = v___y_4767_;
v___y_4728_ = v_a_4774_;
v___y_4729_ = v___y_4769_;
v___y_4730_ = v___y_4768_;
v___y_4731_ = v___y_4770_;
v___y_4732_ = v___y_4772_;
v___y_4733_ = v___y_4771_;
v_a_4734_ = v___x_4800_;
goto v___jp_4707_;
}
}
}
}
}
else
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = lean_io_get_num_heartbeats();
v___x_4805_ = l_IO_lazyPure___redArg(v___y_4751_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
lean_del_object(v___x_4776_);
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4805_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4805_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
lean_ctor_set_tag(v___x_4808_, 1);
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
v___y_4672_ = v___y_4747_;
v___y_4673_ = v___y_4748_;
v___y_4674_ = v___y_4749_;
v___y_4675_ = v___y_4750_;
v___y_4676_ = v___y_4752_;
v___y_4677_ = v___y_4753_;
v___y_4678_ = v___y_4754_;
v___y_4679_ = v___y_4755_;
v___y_4680_ = v___y_4756_;
v___y_4681_ = v___y_4757_;
v___y_4682_ = v___y_4758_;
v___y_4683_ = v___y_4760_;
v___y_4684_ = v___y_4761_;
v___y_4685_ = v___y_4762_;
v___y_4686_ = v___x_4804_;
v___y_4687_ = v___y_4763_;
v___y_4688_ = v___y_4764_;
v___y_4689_ = v___y_4765_;
v___y_4690_ = v___y_4766_;
v___y_4691_ = v___y_4767_;
v___y_4692_ = v_a_4774_;
v___y_4693_ = v___y_4769_;
v___y_4694_ = v___y_4768_;
v___y_4695_ = v___y_4770_;
v___y_4696_ = v___y_4772_;
v___y_4697_ = v___y_4771_;
v_a_4698_ = v___x_4811_;
goto v___jp_4671_;
}
}
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4827_; 
v_a_4814_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4816_ = v___x_4805_;
v_isShared_4817_ = v_isSharedCheck_4827_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4805_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4827_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4818_; lean_object* v___x_4820_; 
v___x_4818_ = lean_io_error_to_string(v_a_4814_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set_tag(v___x_4816_, 3);
lean_ctor_set(v___x_4816_, 0, v___x_4818_);
v___x_4820_ = v___x_4816_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4824_; 
v___x_4821_ = l_Lean_MessageData_ofFormat(v___x_4820_);
lean_inc(v___y_4759_);
v___x_4822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___y_4759_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 0, v___x_4822_);
v___x_4824_ = v___x_4776_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
v___y_4672_ = v___y_4747_;
v___y_4673_ = v___y_4748_;
v___y_4674_ = v___y_4749_;
v___y_4675_ = v___y_4750_;
v___y_4676_ = v___y_4752_;
v___y_4677_ = v___y_4753_;
v___y_4678_ = v___y_4754_;
v___y_4679_ = v___y_4755_;
v___y_4680_ = v___y_4756_;
v___y_4681_ = v___y_4757_;
v___y_4682_ = v___y_4758_;
v___y_4683_ = v___y_4760_;
v___y_4684_ = v___y_4761_;
v___y_4685_ = v___y_4762_;
v___y_4686_ = v___x_4804_;
v___y_4687_ = v___y_4763_;
v___y_4688_ = v___y_4764_;
v___y_4689_ = v___y_4765_;
v___y_4690_ = v___y_4766_;
v___y_4691_ = v___y_4767_;
v___y_4692_ = v_a_4774_;
v___y_4693_ = v___y_4769_;
v___y_4694_ = v___y_4768_;
v___y_4695_ = v___y_4770_;
v___y_4696_ = v___y_4772_;
v___y_4697_ = v___y_4771_;
v_a_4698_ = v___x_4824_;
goto v___jp_4671_;
}
}
}
}
}
}
}
v___jp_4829_:
{
lean_object* v___x_4845_; lean_object* v_satExpr_4846_; lean_object* v_bvExpr_4847_; lean_object* v___x_4848_; lean_object* v_theoryState_4849_; lean_object* v_bitvecState_4850_; lean_object* v___x_4851_; lean_object* v_theoryState_4852_; lean_object* v_satExpr_4853_; lean_object* v_hypQueue_4854_; lean_object* v_usedHyps_4855_; uint8_t v_didChange_4856_; lean_object* v_solverTimeBudgetMs_4857_; lean_object* v_roundBudget_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4899_; 
v___x_4845_ = lean_st_ref_get(v___y_4832_);
v_satExpr_4846_ = lean_ctor_get(v___x_4845_, 0);
lean_inc_ref(v_satExpr_4846_);
lean_dec(v___x_4845_);
v_bvExpr_4847_ = lean_ctor_get(v_satExpr_4846_, 0);
lean_inc_ref(v_bvExpr_4847_);
lean_dec_ref(v_satExpr_4846_);
v___x_4848_ = lean_st_ref_get(v___y_4832_);
v_theoryState_4849_ = lean_ctor_get(v___x_4848_, 3);
lean_inc_ref(v_theoryState_4849_);
lean_dec(v___x_4848_);
v_bitvecState_4850_ = lean_ctor_get(v_theoryState_4849_, 1);
lean_inc_ref(v_bitvecState_4850_);
lean_dec_ref(v_theoryState_4849_);
v___x_4851_ = lean_st_ref_take(v___y_4832_);
v_theoryState_4852_ = lean_ctor_get(v___x_4851_, 3);
v_satExpr_4853_ = lean_ctor_get(v___x_4851_, 0);
v_hypQueue_4854_ = lean_ctor_get(v___x_4851_, 1);
v_usedHyps_4855_ = lean_ctor_get(v___x_4851_, 2);
v_didChange_4856_ = lean_ctor_get_uint8(v___x_4851_, sizeof(void*)*6);
v_solverTimeBudgetMs_4857_ = lean_ctor_get(v___x_4851_, 4);
v_roundBudget_4858_ = lean_ctor_get(v___x_4851_, 5);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4860_ = v___x_4851_;
v_isShared_4861_ = v_isSharedCheck_4899_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_roundBudget_4858_);
lean_inc(v_solverTimeBudgetMs_4857_);
lean_inc(v_theoryState_4852_);
lean_inc(v_usedHyps_4855_);
lean_inc(v_hypQueue_4854_);
lean_inc(v_satExpr_4853_);
lean_dec(v___x_4851_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4899_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v_funState_4862_; lean_object* v_preprocessCaches_4863_; lean_object* v_satSolver_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4897_; 
v_funState_4862_ = lean_ctor_get(v_theoryState_4852_, 0);
v_preprocessCaches_4863_ = lean_ctor_get(v_theoryState_4852_, 2);
v_satSolver_4864_ = lean_ctor_get(v_theoryState_4852_, 3);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_theoryState_4852_);
if (v_isSharedCheck_4897_ == 0)
{
lean_object* v_unused_4898_; 
v_unused_4898_ = lean_ctor_get(v_theoryState_4852_, 1);
lean_dec(v_unused_4898_);
v___x_4866_ = v_theoryState_4852_;
v_isShared_4867_ = v_isSharedCheck_4897_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_satSolver_4864_);
lean_inc(v_preprocessCaches_4863_);
lean_inc(v_funState_4862_);
lean_dec(v_theoryState_4852_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4897_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4872_; 
v___x_4868_ = lean_unsigned_to_nat(0u);
v___x_4869_ = lean_unsigned_to_nat(16u);
v___x_4870_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__15);
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 1, v___x_4870_);
v___x_4872_ = v___x_4866_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_funState_4862_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v___x_4870_);
lean_ctor_set(v_reuseFailAlloc_4896_, 2, v_preprocessCaches_4863_);
lean_ctor_set(v_reuseFailAlloc_4896_, 3, v_satSolver_4864_);
v___x_4872_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
lean_object* v___x_4874_; 
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 3, v___x_4872_);
v___x_4874_ = v___x_4860_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_satExpr_4853_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v_hypQueue_4854_);
lean_ctor_set(v_reuseFailAlloc_4895_, 2, v_usedHyps_4855_);
lean_ctor_set(v_reuseFailAlloc_4895_, 3, v___x_4872_);
lean_ctor_set(v_reuseFailAlloc_4895_, 4, v_solverTimeBudgetMs_4857_);
lean_ctor_set(v_reuseFailAlloc_4895_, 5, v_roundBudget_4858_);
lean_ctor_set_uint8(v_reuseFailAlloc_4895_, sizeof(void*)*6, v_didChange_4856_);
v___x_4874_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
lean_object* v___x_4875_; lean_object* v_aig_4876_; lean_object* v_toCold_4877_; lean_object* v_options_4878_; lean_object* v_blastCache_4879_; lean_object* v_cnfCache_4880_; lean_object* v_decls_4881_; lean_object* v_ref_4882_; lean_object* v_inheritedTraceOptions_4883_; uint8_t v_hasTrace_4884_; lean_object* v___f_4885_; lean_object* v___x_4886_; uint8_t v___x_4887_; lean_object* v___x_4888_; 
v___x_4875_ = lean_st_ref_put(v___y_4832_, v___x_4874_);
v_aig_4876_ = lean_ctor_get(v_bitvecState_4850_, 0);
lean_inc_ref(v_aig_4876_);
v_toCold_4877_ = lean_ctor_get(v___y_4843_, 0);
v_options_4878_ = lean_ctor_get(v_toCold_4877_, 2);
v_blastCache_4879_ = lean_ctor_get(v_bitvecState_4850_, 1);
lean_inc_ref(v_blastCache_4879_);
v_cnfCache_4880_ = lean_ctor_get(v_bitvecState_4850_, 2);
lean_inc_ref(v_cnfCache_4880_);
lean_dec_ref(v_bitvecState_4850_);
v_decls_4881_ = lean_ctor_get(v_aig_4876_, 0);
lean_inc_ref(v_decls_4881_);
v_ref_4882_ = lean_ctor_get(v___y_4843_, 2);
v_inheritedTraceOptions_4883_ = lean_ctor_get(v_toCold_4877_, 11);
v_hasTrace_4884_ = lean_ctor_get_uint8(v_options_4878_, sizeof(void*)*1);
v___f_4885_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__5), 4, 3);
lean_closure_set(v___f_4885_, 0, v_aig_4876_);
lean_closure_set(v___f_4885_, 1, v_bvExpr_4847_);
lean_closure_set(v___f_4885_, 2, v_blastCache_4879_);
v___x_4886_ = lean_array_get_size(v_decls_4881_);
lean_dec_ref(v_decls_4881_);
v___x_4887_ = 1;
v___x_4888_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8___closed__0));
if (v_hasTrace_4884_ == 0)
{
lean_object* v___x_4889_; 
v___x_4889_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_4885_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
v___y_4606_ = v_ctx_4830_;
v___y_4607_ = v___x_4869_;
v___y_4608_ = v___x_4886_;
v___y_4609_ = v___x_4868_;
v___y_4610_ = v___y_4844_;
v___y_4611_ = v___x_4887_;
v___y_4612_ = v___y_4836_;
v___y_4613_ = v___y_4832_;
v___y_4614_ = v___y_4839_;
v___y_4615_ = v___y_4840_;
v___y_4616_ = v_cnfCache_4880_;
v___y_4617_ = v___y_4841_;
v___y_4618_ = v___x_4888_;
v___y_4619_ = v___y_4843_;
v___y_4620_ = v___y_4831_;
v___y_4621_ = v___y_4835_;
v___y_4622_ = v___y_4833_;
v___y_4623_ = v___y_4834_;
v___y_4624_ = v___y_4838_;
v___y_4625_ = v___y_4837_;
v___y_4626_ = v___x_4870_;
v___y_4627_ = v___y_4842_;
v___y_4628_ = v___x_4889_;
goto v___jp_4605_;
}
else
{
lean_object* v___x_4890_; uint8_t v___x_4891_; 
v___x_4890_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___closed__8);
v___x_4891_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4883_, v_options_4878_, v___x_4890_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; uint8_t v___x_4893_; 
v___x_4892_ = l_Lean_trace_profiler;
v___x_4893_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__5(v_options_4878_, v___x_4892_);
if (v___x_4893_ == 0)
{
lean_object* v___x_4894_; 
v___x_4894_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___lam__6(v___f_4885_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
v___y_4606_ = v_ctx_4830_;
v___y_4607_ = v___x_4869_;
v___y_4608_ = v___x_4886_;
v___y_4609_ = v___x_4868_;
v___y_4610_ = v___y_4844_;
v___y_4611_ = v___x_4887_;
v___y_4612_ = v___y_4836_;
v___y_4613_ = v___y_4832_;
v___y_4614_ = v___y_4839_;
v___y_4615_ = v___y_4840_;
v___y_4616_ = v_cnfCache_4880_;
v___y_4617_ = v___y_4841_;
v___y_4618_ = v___x_4888_;
v___y_4619_ = v___y_4843_;
v___y_4620_ = v___y_4831_;
v___y_4621_ = v___y_4835_;
v___y_4622_ = v___y_4833_;
v___y_4623_ = v___y_4834_;
v___y_4624_ = v___y_4838_;
v___y_4625_ = v___y_4837_;
v___y_4626_ = v___x_4870_;
v___y_4627_ = v___y_4842_;
v___y_4628_ = v___x_4894_;
goto v___jp_4605_;
}
else
{
v___y_4747_ = v___x_4869_;
v___y_4748_ = v___x_4886_;
v___y_4749_ = v___x_4868_;
v___y_4750_ = v___y_4844_;
v___y_4751_ = v___f_4885_;
v___y_4752_ = v___y_4839_;
v___y_4753_ = v_cnfCache_4880_;
v___y_4754_ = v___x_4891_;
v___y_4755_ = v___y_4835_;
v___y_4756_ = v___y_4831_;
v___y_4757_ = v_ctx_4830_;
v___y_4758_ = v___x_4887_;
v___y_4759_ = v_ref_4882_;
v___y_4760_ = v___y_4836_;
v___y_4761_ = v___y_4832_;
v___y_4762_ = v___y_4840_;
v___y_4763_ = v___y_4841_;
v___y_4764_ = v___x_4888_;
v___y_4765_ = v___y_4843_;
v___y_4766_ = v___y_4834_;
v___y_4767_ = v___y_4833_;
v___y_4768_ = v___y_4838_;
v___y_4769_ = v___y_4837_;
v___y_4770_ = v___x_4870_;
v___y_4771_ = v___y_4842_;
v___y_4772_ = v_options_4878_;
goto v___jp_4746_;
}
}
else
{
v___y_4747_ = v___x_4869_;
v___y_4748_ = v___x_4886_;
v___y_4749_ = v___x_4868_;
v___y_4750_ = v___y_4844_;
v___y_4751_ = v___f_4885_;
v___y_4752_ = v___y_4839_;
v___y_4753_ = v_cnfCache_4880_;
v___y_4754_ = v___x_4891_;
v___y_4755_ = v___y_4835_;
v___y_4756_ = v___y_4831_;
v___y_4757_ = v_ctx_4830_;
v___y_4758_ = v___x_4887_;
v___y_4759_ = v_ref_4882_;
v___y_4760_ = v___y_4836_;
v___y_4761_ = v___y_4832_;
v___y_4762_ = v___y_4840_;
v___y_4763_ = v___y_4841_;
v___y_4764_ = v___x_4888_;
v___y_4765_ = v___y_4843_;
v___y_4766_ = v___y_4834_;
v___y_4767_ = v___y_4833_;
v___y_4768_ = v___y_4838_;
v___y_4769_ = v___y_4837_;
v___y_4770_ = v___x_4870_;
v___y_4771_ = v___y_4842_;
v___y_4772_ = v_options_4878_;
goto v___jp_4746_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3808_ = stack[0].m_obj;
lean_object* v_a_3809_ = stack[1].m_obj;
lean_object* v_a_3810_ = stack[2].m_obj;
lean_object* v_a_3811_ = stack[3].m_obj;
lean_object* v_a_3812_ = stack[4].m_obj;
lean_object* v_a_3813_ = stack[5].m_obj;
lean_object* v_a_3814_ = stack[6].m_obj;
lean_object* v_a_3815_ = stack[7].m_obj;
lean_object* v_a_3816_ = stack[8].m_obj;
lean_object* v_a_3817_ = stack[9].m_obj;
lean_object* v_a_3818_ = stack[10].m_obj;
lean_object* v_a_3819_ = stack[11].m_obj;
lean_object* v_a_3820_ = stack[12].m_obj;
lean_object* v_a_3821_ = stack[13].m_obj;
lean_object* v_res_5440_;
v_res_5440_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_);
stack->m_obj
 = v_res_5440_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec___boxed(lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_){
_start:
{
lean_object* v_res_5456_; 
v_res_5456_ = l_Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec(v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_);
lean_dec(v_a_5454_);
lean_dec_ref(v_a_5453_);
lean_dec(v_a_5452_);
lean_dec_ref(v_a_5451_);
lean_dec(v_a_5450_);
lean_dec_ref(v_a_5449_);
lean_dec(v_a_5448_);
lean_dec_ref(v_a_5447_);
lean_dec(v_a_5446_);
lean_dec(v_a_5445_);
lean_dec_ref(v_a_5444_);
lean_dec(v_a_5443_);
lean_dec(v_a_5442_);
lean_dec_ref(v_a_5441_);
return v_res_5456_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2(lean_object* v_cls_5457_, lean_object* v_msg_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v___x_5474_; 
v___x_5474_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___redArg(v_cls_5457_, v_msg_5458_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_);
return v___x_5474_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_5457_ = stack[0].m_obj;
lean_object* v_msg_5458_ = stack[1].m_obj;
lean_object* v___y_5459_ = stack[2].m_obj;
lean_object* v___y_5460_ = stack[3].m_obj;
lean_object* v___y_5461_ = stack[4].m_obj;
lean_object* v___y_5462_ = stack[5].m_obj;
lean_object* v___y_5463_ = stack[6].m_obj;
lean_object* v___y_5464_ = stack[7].m_obj;
lean_object* v___y_5465_ = stack[8].m_obj;
lean_object* v___y_5466_ = stack[9].m_obj;
lean_object* v___y_5467_ = stack[10].m_obj;
lean_object* v___y_5468_ = stack[11].m_obj;
lean_object* v___y_5469_ = stack[12].m_obj;
lean_object* v___y_5470_ = stack[13].m_obj;
lean_object* v___y_5471_ = stack[14].m_obj;
lean_object* v___y_5472_ = stack[15].m_obj;
lean_object* v_res_5475_;
v_res_5475_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2(v_cls_5457_, v_msg_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_);
stack->m_obj
 = v_res_5475_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2___boxed(lean_object** _args){
lean_object* v_cls_5476_ = _args[0];
lean_object* v_msg_5477_ = _args[1];
lean_object* v___y_5478_ = _args[2];
lean_object* v___y_5479_ = _args[3];
lean_object* v___y_5480_ = _args[4];
lean_object* v___y_5481_ = _args[5];
lean_object* v___y_5482_ = _args[6];
lean_object* v___y_5483_ = _args[7];
lean_object* v___y_5484_ = _args[8];
lean_object* v___y_5485_ = _args[9];
lean_object* v___y_5486_ = _args[10];
lean_object* v___y_5487_ = _args[11];
lean_object* v___y_5488_ = _args[12];
lean_object* v___y_5489_ = _args[13];
lean_object* v___y_5490_ = _args[14];
lean_object* v___y_5491_ = _args[15];
lean_object* v___y_5492_ = _args[16];
_start:
{
lean_object* v_res_5493_; 
v_res_5493_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__2(v_cls_5476_, v_msg_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_);
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
lean_dec(v___y_5487_);
lean_dec_ref(v___y_5486_);
lean_dec(v___y_5485_);
lean_dec_ref(v___y_5484_);
lean_dec(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec_ref(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
return v_res_5493_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3(lean_object* v_00_u03b1_5494_, lean_object* v_msg_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_){
_start:
{
lean_object* v___x_5511_; 
v___x_5511_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___redArg(v_msg_5495_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_);
return v___x_5511_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5495_ = stack[1].m_obj;
lean_object* v___y_5496_ = stack[2].m_obj;
lean_object* v___y_5497_ = stack[3].m_obj;
lean_object* v___y_5498_ = stack[4].m_obj;
lean_object* v___y_5499_ = stack[5].m_obj;
lean_object* v___y_5500_ = stack[6].m_obj;
lean_object* v___y_5501_ = stack[7].m_obj;
lean_object* v___y_5502_ = stack[8].m_obj;
lean_object* v___y_5503_ = stack[9].m_obj;
lean_object* v___y_5504_ = stack[10].m_obj;
lean_object* v___y_5505_ = stack[11].m_obj;
lean_object* v___y_5506_ = stack[12].m_obj;
lean_object* v___y_5507_ = stack[13].m_obj;
lean_object* v___y_5508_ = stack[14].m_obj;
lean_object* v___y_5509_ = stack[15].m_obj;
lean_object* v_res_5512_;
v_res_5512_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3(lean_box(0), v_msg_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_);
stack->m_obj
 = v_res_5512_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3___boxed(lean_object** _args){
lean_object* v_00_u03b1_5513_ = _args[0];
lean_object* v_msg_5514_ = _args[1];
lean_object* v___y_5515_ = _args[2];
lean_object* v___y_5516_ = _args[3];
lean_object* v___y_5517_ = _args[4];
lean_object* v___y_5518_ = _args[5];
lean_object* v___y_5519_ = _args[6];
lean_object* v___y_5520_ = _args[7];
lean_object* v___y_5521_ = _args[8];
lean_object* v___y_5522_ = _args[9];
lean_object* v___y_5523_ = _args[10];
lean_object* v___y_5524_ = _args[11];
lean_object* v___y_5525_ = _args[12];
lean_object* v___y_5526_ = _args[13];
lean_object* v___y_5527_ = _args[14];
lean_object* v___y_5528_ = _args[15];
lean_object* v___y_5529_ = _args[16];
_start:
{
lean_object* v_res_5530_; 
v_res_5530_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__3(v_00_u03b1_5513_, v_msg_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_);
lean_dec(v___y_5528_);
lean_dec_ref(v___y_5527_);
lean_dec(v___y_5526_);
lean_dec_ref(v___y_5525_);
lean_dec(v___y_5524_);
lean_dec_ref(v___y_5523_);
lean_dec(v___y_5522_);
lean_dec_ref(v___y_5521_);
lean_dec(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
return v_res_5530_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9(lean_object* v_00_u03b1_5531_, lean_object* v_x_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_){
_start:
{
lean_object* v___x_5548_; 
v___x_5548_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___redArg(v_x_5532_);
return v___x_5548_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5532_ = stack[1].m_obj;
lean_object* v___y_5533_ = stack[2].m_obj;
lean_object* v___y_5534_ = stack[3].m_obj;
lean_object* v___y_5535_ = stack[4].m_obj;
lean_object* v___y_5536_ = stack[5].m_obj;
lean_object* v___y_5537_ = stack[6].m_obj;
lean_object* v___y_5538_ = stack[7].m_obj;
lean_object* v___y_5539_ = stack[8].m_obj;
lean_object* v___y_5540_ = stack[9].m_obj;
lean_object* v___y_5541_ = stack[10].m_obj;
lean_object* v___y_5542_ = stack[11].m_obj;
lean_object* v___y_5543_ = stack[12].m_obj;
lean_object* v___y_5544_ = stack[13].m_obj;
lean_object* v___y_5545_ = stack[14].m_obj;
lean_object* v___y_5546_ = stack[15].m_obj;
lean_object* v_res_5549_;
v_res_5549_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9(lean_box(0), v_x_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
stack->m_obj
 = v_res_5549_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_00_u03b1_5550_ = _args[0];
lean_object* v_x_5551_ = _args[1];
lean_object* v___y_5552_ = _args[2];
lean_object* v___y_5553_ = _args[3];
lean_object* v___y_5554_ = _args[4];
lean_object* v___y_5555_ = _args[5];
lean_object* v___y_5556_ = _args[6];
lean_object* v___y_5557_ = _args[7];
lean_object* v___y_5558_ = _args[8];
lean_object* v___y_5559_ = _args[9];
lean_object* v___y_5560_ = _args[10];
lean_object* v___y_5561_ = _args[11];
lean_object* v___y_5562_ = _args[12];
lean_object* v___y_5563_ = _args[13];
lean_object* v___y_5564_ = _args[14];
lean_object* v___y_5565_ = _args[15];
lean_object* v___y_5566_ = _args[16];
_start:
{
lean_object* v_res_5567_; 
v_res_5567_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__9(v_00_u03b1_5550_, v_x_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
lean_dec(v___y_5565_);
lean_dec_ref(v___y_5564_);
lean_dec(v___y_5563_);
lean_dec_ref(v___y_5562_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5559_);
lean_dec_ref(v___y_5558_);
lean_dec(v___y_5557_);
lean_dec(v___y_5556_);
lean_dec_ref(v___y_5555_);
lean_dec(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
return v_res_5567_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8(lean_object* v_oldTraces_5568_, lean_object* v_data_5569_, lean_object* v_ref_5570_, lean_object* v_msg_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_){
_start:
{
lean_object* v___x_5587_; 
v___x_5587_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___redArg(v_oldTraces_5568_, v_data_5569_, v_ref_5570_, v_msg_5571_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
return v___x_5587_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_5568_ = stack[0].m_obj;
lean_object* v_data_5569_ = stack[1].m_obj;
lean_object* v_ref_5570_ = stack[2].m_obj;
lean_object* v_msg_5571_ = stack[3].m_obj;
lean_object* v___y_5572_ = stack[4].m_obj;
lean_object* v___y_5573_ = stack[5].m_obj;
lean_object* v___y_5574_ = stack[6].m_obj;
lean_object* v___y_5575_ = stack[7].m_obj;
lean_object* v___y_5576_ = stack[8].m_obj;
lean_object* v___y_5577_ = stack[9].m_obj;
lean_object* v___y_5578_ = stack[10].m_obj;
lean_object* v___y_5579_ = stack[11].m_obj;
lean_object* v___y_5580_ = stack[12].m_obj;
lean_object* v___y_5581_ = stack[13].m_obj;
lean_object* v___y_5582_ = stack[14].m_obj;
lean_object* v___y_5583_ = stack[15].m_obj;
lean_object* v___y_5584_ = stack[16].m_obj;
lean_object* v___y_5585_ = stack[17].m_obj;
lean_object* v_res_5588_;
v_res_5588_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8(v_oldTraces_5568_, v_data_5569_, v_ref_5570_, v_msg_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
stack->m_obj
 = v_res_5588_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_5589_ = _args[0];
lean_object* v_data_5590_ = _args[1];
lean_object* v_ref_5591_ = _args[2];
lean_object* v_msg_5592_ = _args[3];
lean_object* v___y_5593_ = _args[4];
lean_object* v___y_5594_ = _args[5];
lean_object* v___y_5595_ = _args[6];
lean_object* v___y_5596_ = _args[7];
lean_object* v___y_5597_ = _args[8];
lean_object* v___y_5598_ = _args[9];
lean_object* v___y_5599_ = _args[10];
lean_object* v___y_5600_ = _args[11];
lean_object* v___y_5601_ = _args[12];
lean_object* v___y_5602_ = _args[13];
lean_object* v___y_5603_ = _args[14];
lean_object* v___y_5604_ = _args[15];
lean_object* v___y_5605_ = _args[16];
lean_object* v___y_5606_ = _args[17];
lean_object* v___y_5607_ = _args[18];
_start:
{
lean_object* v_res_5608_; 
v_res_5608_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__6_spec__8(v_oldTraces_5589_, v_data_5590_, v_ref_5591_, v_msg_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec(v___y_5598_);
lean_dec(v___y_5597_);
lean_dec_ref(v___y_5596_);
lean_dec(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
return v_res_5608_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16(lean_object* v_acc_5609_, lean_object* v_decls_5610_, lean_object* v_hinv_5611_, lean_object* v_idx_5612_, lean_object* v_hidx_5613_, lean_object* v_a_5614_){
_start:
{
lean_object* v___x_5615_; 
v___x_5615_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___redArg(v_acc_5609_, v_decls_5610_, v_idx_5612_, v_a_5614_);
return v___x_5615_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16___boxed(lean_object* v_acc_5616_, lean_object* v_decls_5617_, lean_object* v_hinv_5618_, lean_object* v_idx_5619_, lean_object* v_hidx_5620_, lean_object* v_a_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16(v_acc_5616_, v_decls_5617_, v_hinv_5618_, v_idx_5619_, v_hidx_5620_, v_a_5621_);
lean_dec_ref(v_decls_5617_);
return v_res_5622_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18(lean_object* v___x_5623_, lean_object* v_00_u03b2_5624_, lean_object* v_m_5625_, lean_object* v_a_5626_){
_start:
{
uint8_t v___x_5627_; 
v___x_5627_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___redArg(v___x_5623_, v_m_5625_, v_a_5626_);
return v___x_5627_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5623_ = stack[0].m_obj;
lean_object* v_m_5625_ = stack[2].m_obj;
lean_object* v_a_5626_ = stack[3].m_obj;
uint8_t v_res_5628_;
v_res_5628_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18(v___x_5623_, lean_box(0), v_m_5625_, v_a_5626_);
stack->m_num = v_res_5628_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18___boxed(lean_object* v___x_5629_, lean_object* v_00_u03b2_5630_, lean_object* v_m_5631_, lean_object* v_a_5632_){
_start:
{
uint8_t v_res_5633_; lean_object* v_r_5634_; 
v_res_5633_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18(v___x_5629_, v_00_u03b2_5630_, v_m_5631_, v_a_5632_);
lean_dec(v_a_5632_);
lean_dec_ref(v_m_5631_);
lean_dec(v___x_5629_);
v_r_5634_ = lean_box(v_res_5633_);
return v_r_5634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19(lean_object* v___x_5635_, lean_object* v_00_u03b2_5636_, lean_object* v_m_5637_, lean_object* v_a_5638_, lean_object* v_b_5639_){
_start:
{
lean_object* v___x_5640_; 
v___x_5640_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___redArg(v___x_5635_, v_m_5637_, v_a_5638_, v_b_5639_);
return v___x_5640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19___boxed(lean_object* v___x_5641_, lean_object* v_00_u03b2_5642_, lean_object* v_m_5643_, lean_object* v_a_5644_, lean_object* v_b_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19(v___x_5641_, v_00_u03b2_5642_, v_m_5643_, v_a_5644_, v_b_5645_);
lean_dec(v___x_5641_);
return v_res_5646_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23(lean_object* v___x_5647_, lean_object* v_00_u03b2_5648_, lean_object* v_a_5649_, lean_object* v_x_5650_){
_start:
{
uint8_t v___x_5651_; 
v___x_5651_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___redArg(v_a_5649_, v_x_5650_);
return v___x_5651_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5647_ = stack[0].m_obj;
lean_object* v_a_5649_ = stack[2].m_obj;
lean_object* v_x_5650_ = stack[3].m_obj;
uint8_t v_res_5652_;
v_res_5652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23(v___x_5647_, lean_box(0), v_a_5649_, v_x_5650_);
stack->m_num = v_res_5652_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23___boxed(lean_object* v___x_5653_, lean_object* v_00_u03b2_5654_, lean_object* v_a_5655_, lean_object* v_x_5656_){
_start:
{
uint8_t v_res_5657_; lean_object* v_r_5658_; 
v_res_5657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__18_spec__23(v___x_5653_, v_00_u03b2_5654_, v_a_5655_, v_x_5656_);
lean_dec(v_x_5656_);
lean_dec(v_a_5655_);
lean_dec(v___x_5653_);
v_r_5658_ = lean_box(v_res_5657_);
return v_r_5658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25(lean_object* v___x_5659_, lean_object* v_00_u03b2_5660_, lean_object* v_data_5661_){
_start:
{
lean_object* v___x_5662_; 
v___x_5662_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___redArg(v___x_5659_, v_data_5661_);
return v___x_5662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25___boxed(lean_object* v___x_5663_, lean_object* v_00_u03b2_5664_, lean_object* v_data_5665_){
_start:
{
lean_object* v_res_5666_; 
v_res_5666_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25(v___x_5663_, v_00_u03b2_5664_, v_data_5665_);
lean_dec(v___x_5663_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28(lean_object* v___x_5667_, lean_object* v_00_u03b2_5668_, lean_object* v_i_5669_, lean_object* v_source_5670_, lean_object* v_target_5671_){
_start:
{
lean_object* v___x_5672_; 
v___x_5672_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___redArg(v_i_5669_, v_source_5670_, v_target_5671_);
return v___x_5672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28___boxed(lean_object* v___x_5673_, lean_object* v_00_u03b2_5674_, lean_object* v_i_5675_, lean_object* v_source_5676_, lean_object* v_target_5677_){
_start:
{
lean_object* v_res_5678_; 
v_res_5678_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28(v___x_5673_, v_00_u03b2_5674_, v_i_5675_, v_source_5676_, v_target_5677_);
lean_dec(v___x_5673_);
return v_res_5678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29(lean_object* v_00_u03b2_5679_, lean_object* v_x_5680_, lean_object* v_x_5681_){
_start:
{
lean_object* v___x_5682_; 
v___x_5682_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_Cegar_checkBitVec_spec__8_spec__16_spec__19_spec__25_spec__28_spec__29___redArg(v_x_5680_, v_x_5681_);
return v___x_5682_;
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
