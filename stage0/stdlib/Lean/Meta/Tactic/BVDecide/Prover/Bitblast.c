// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Bitblast
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Basic public import Lean.Meta.Tactic.BVDecide.TacticContext import Lean.Meta.Native
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toGraphviz_invEdgeStyle(uint8_t);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_IO_lazyPure___redArg(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_nativeEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_runExternal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
lean_object* l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toCNF_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_byte_array_push(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "extract_closed"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(157, 223, 55, 216, 54, 195, 10, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Compiling proof certificate term"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Compiling and evaluating reflection proof term"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Compiling expr term"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "BVLogicalExpr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__13_value),LEAN_SCALAR_PTR_LITERAL(33, 50, 202, 5, 86, 233, 189, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unsat_of_verifyBVExpr_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 119, .m_capacity = 119, .m_length = 118, .m_data = "Tactic `bv_decide` failed: The LRAT certificate could not be verified; evaluating the following term returned `false`:"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "verifyBVExpr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__19_value),LEAN_SCALAR_PTR_LITERAL(98, 197, 94, 16, 136, 54, 174, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15_value),LEAN_SCALAR_PTR_LITERAL(39, 247, 82, 233, 7, 29, 35, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__25_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Obtaining external proof certificate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Converting AIG to CNF"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Bitblasting BVLogicalExpr to AIG"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___boxed(lean_object*);
static const lean_array_object l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Preparing LRAT reflection term"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -> "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " [label=\""};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__1 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__1_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\", shape=box];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__3_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__4 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__4_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__5 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__5_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\", shape=doublecircle];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__6 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__6_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 21, .m_data = " ∧\",shape=trapezium];"};
static const lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__7 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__7_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0;
static lean_once_cell_t l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Digraph AIG {"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__2 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__2_value;
static const lean_string_object l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__3 = (const lean_object*)&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "SAT solver found a counter example."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "SAT solver found a proof."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "aig.gv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9___boxed(lean_object**);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed, .m_arity = 14, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed, .m_arity = 14, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed, .m_arity = 14, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__4_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "AIG has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " nodes."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___boxed, .m_arity = 14, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
else
{
lean_object* v_val_7_; 
v_val_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_7_) == 3)
{
lean_object* v_v_8_; 
v_v_8_ = lean_ctor_get(v_val_7_, 0);
lean_inc(v_v_8_);
lean_dec_ref_known(v_val_7_, 1);
return v_v_8_;
}
else
{
lean_dec(v_val_7_);
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_9_, v_opt_10_);
lean_dec_ref(v_opt_10_);
lean_dec_ref(v_opts_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(lean_object* v_o_15_, lean_object* v_k_16_, uint8_t v_v_17_){
_start:
{
lean_object* v_map_18_; uint8_t v_hasTrace_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_33_; 
v_map_18_ = lean_ctor_get(v_o_15_, 0);
v_hasTrace_19_ = lean_ctor_get_uint8(v_o_15_, sizeof(void*)*1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_o_15_);
if (v_isSharedCheck_33_ == 0)
{
v___x_21_ = v_o_15_;
v_isShared_22_ = v_isSharedCheck_33_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_map_18_);
lean_dec(v_o_15_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_33_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_23_, 0, v_v_17_);
lean_inc(v_k_16_);
v___x_24_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_16_, v___x_23_, v_map_18_);
if (v_hasTrace_19_ == 0)
{
lean_object* v___x_25_; uint8_t v___x_26_; lean_object* v___x_28_; 
v___x_25_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_26_ = l_Lean_Name_isPrefixOf(v___x_25_, v_k_16_);
lean_dec(v_k_16_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_28_ = v___x_21_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_24_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*1, v___x_26_);
return v___x_28_;
}
}
else
{
lean_object* v___x_31_; 
lean_dec(v_k_16_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_31_ = v___x_21_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_32_, sizeof(void*)*1, v_hasTrace_19_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___boxed(lean_object* v_o_34_, lean_object* v_k_35_, lean_object* v_v_36_){
_start:
{
uint8_t v_v_boxed_37_; lean_object* v_res_38_; 
v_v_boxed_37_ = lean_unbox(v_v_36_);
v_res_38_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_o_34_, v_k_35_, v_v_boxed_37_);
return v_res_38_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_39_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__0);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__1);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(lean_object* v_name_49_, lean_object* v_value_50_, lean_object* v_type_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_toCold_55_; lean_object* v_currRecDepth_56_; lean_object* v_ref_57_; uint8_t v_suppressElabErrors_58_; uint8_t v_checkDeprecated_59_; uint8_t v_isRecordingDeps_60_; lean_object* v_fileName_61_; lean_object* v_fileMap_62_; lean_object* v_options_63_; lean_object* v_currNamespace_64_; lean_object* v_openDecls_65_; lean_object* v_initHeartbeats_66_; lean_object* v_maxHeartbeats_67_; lean_object* v_quotContext_68_; lean_object* v_currMacroScope_69_; lean_object* v_cancelTk_x3f_70_; lean_object* v_inheritedTraceOptions_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; uint8_t v___x_80_; lean_object* v___y_82_; uint16_t v___y_83_; lean_object* v_fileName_84_; lean_object* v_fileMap_85_; lean_object* v_currNamespace_86_; lean_object* v_openDecls_87_; lean_object* v_initHeartbeats_88_; lean_object* v_maxHeartbeats_89_; lean_object* v_quotContext_90_; lean_object* v_currMacroScope_91_; lean_object* v_cancelTk_x3f_92_; lean_object* v_inheritedTraceOptions_93_; lean_object* v_currRecDepth_94_; lean_object* v_ref_95_; uint8_t v_suppressElabErrors_96_; uint8_t v_checkDeprecated_97_; uint8_t v_isRecordingDeps_98_; lean_object* v___y_99_; lean_object* v___y_106_; uint8_t v___y_107_; uint16_t v___y_108_; lean_object* v___y_131_; 
v_toCold_55_ = lean_ctor_get(v_a_52_, 0);
v_currRecDepth_56_ = lean_ctor_get(v_a_52_, 1);
v_ref_57_ = lean_ctor_get(v_a_52_, 2);
v_suppressElabErrors_58_ = lean_ctor_get_uint8(v_a_52_, sizeof(void*)*3 + 2);
v_checkDeprecated_59_ = lean_ctor_get_uint8(v_a_52_, sizeof(void*)*3 + 3);
v_isRecordingDeps_60_ = lean_ctor_get_uint8(v_a_52_, sizeof(void*)*3 + 4);
v_fileName_61_ = lean_ctor_get(v_toCold_55_, 0);
v_fileMap_62_ = lean_ctor_get(v_toCold_55_, 1);
v_options_63_ = lean_ctor_get(v_toCold_55_, 2);
v_currNamespace_64_ = lean_ctor_get(v_toCold_55_, 4);
v_openDecls_65_ = lean_ctor_get(v_toCold_55_, 5);
v_initHeartbeats_66_ = lean_ctor_get(v_toCold_55_, 6);
v_maxHeartbeats_67_ = lean_ctor_get(v_toCold_55_, 7);
v_quotContext_68_ = lean_ctor_get(v_toCold_55_, 8);
v_currMacroScope_69_ = lean_ctor_get(v_toCold_55_, 9);
v_cancelTk_x3f_70_ = lean_ctor_get(v_toCold_55_, 10);
v_inheritedTraceOptions_71_ = lean_ctor_get(v_toCold_55_, 11);
v___x_72_ = lean_box(0);
lean_inc(v_name_49_);
v___x_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_73_, 0, v_name_49_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
lean_ctor_set(v___x_73_, 2, v_type_51_);
v___x_74_ = lean_box(1);
v___x_75_ = 1;
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v_name_49_);
lean_ctor_set(v___x_76_, 1, v___x_72_);
v___x_77_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_77_, 0, v___x_73_);
lean_ctor_set(v___x_77_, 1, v_value_50_);
lean_ctor_set(v___x_77_, 2, v___x_74_);
lean_ctor_set(v___x_77_, 3, v___x_76_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*4, v___x_75_);
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
v___x_79_ = 1;
v___x_80_ = 0;
if (v_isRecordingDeps_60_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5));
lean_inc_ref(v_options_63_);
v___x_141_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_63_, v___x_140_, v_isRecordingDeps_60_);
v___y_131_ = v___x_141_;
goto v___jp_130_;
}
else
{
lean_object* v___x_142_; 
lean_inc_ref(v_options_63_);
v___x_142_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_63_);
v___y_131_ = v___x_142_;
goto v___jp_130_;
}
v___jp_81_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = l_Lean_maxRecDepth;
v___x_101_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v___y_82_, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_102_, 0, v_fileName_84_);
lean_ctor_set(v___x_102_, 1, v_fileMap_85_);
lean_ctor_set(v___x_102_, 2, v___y_82_);
lean_ctor_set(v___x_102_, 3, v___x_101_);
lean_ctor_set(v___x_102_, 4, v_currNamespace_86_);
lean_ctor_set(v___x_102_, 5, v_openDecls_87_);
lean_ctor_set(v___x_102_, 6, v_initHeartbeats_88_);
lean_ctor_set(v___x_102_, 7, v_maxHeartbeats_89_);
lean_ctor_set(v___x_102_, 8, v_quotContext_90_);
lean_ctor_set(v___x_102_, 9, v_currMacroScope_91_);
lean_ctor_set(v___x_102_, 10, v_cancelTk_x3f_92_);
lean_ctor_set(v___x_102_, 11, v_inheritedTraceOptions_93_);
lean_inc(v_ref_95_);
lean_inc(v_currRecDepth_94_);
v___x_103_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_currRecDepth_94_);
lean_ctor_set(v___x_103_, 2, v_ref_95_);
lean_ctor_set_uint16(v___x_103_, sizeof(void*)*3, v___y_83_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*3 + 2, v_suppressElabErrors_96_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*3 + 3, v_checkDeprecated_97_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*3 + 4, v_isRecordingDeps_98_);
v___x_104_ = l_Lean_addAndCompile(v___x_78_, v___x_79_, v___x_80_, v___x_103_, v___y_99_);
lean_dec_ref_known(v___x_103_, 3);
return v___x_104_;
}
v___jp_105_:
{
lean_object* v___x_109_; lean_object* v_env_110_; lean_object* v_nextMacroScope_111_; lean_object* v_ngen_112_; lean_object* v_auxDeclNGen_113_; lean_object* v_traceState_114_; lean_object* v_recordedDeps_115_; lean_object* v_messages_116_; lean_object* v_infoState_117_; lean_object* v_snapshotTasks_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v___x_109_ = lean_st_ref_take(v_a_53_);
v_env_110_ = lean_ctor_get(v___x_109_, 0);
v_nextMacroScope_111_ = lean_ctor_get(v___x_109_, 1);
v_ngen_112_ = lean_ctor_get(v___x_109_, 2);
v_auxDeclNGen_113_ = lean_ctor_get(v___x_109_, 3);
v_traceState_114_ = lean_ctor_get(v___x_109_, 4);
v_recordedDeps_115_ = lean_ctor_get(v___x_109_, 6);
v_messages_116_ = lean_ctor_get(v___x_109_, 7);
v_infoState_117_ = lean_ctor_get(v___x_109_, 8);
v_snapshotTasks_118_ = lean_ctor_get(v___x_109_, 9);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v___x_109_, 5);
lean_dec(v_unused_129_);
v___x_120_ = v___x_109_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snapshotTasks_118_);
lean_inc(v_infoState_117_);
lean_inc(v_messages_116_);
lean_inc(v_recordedDeps_115_);
lean_inc(v_traceState_114_);
lean_inc(v_auxDeclNGen_113_);
lean_inc(v_ngen_112_);
lean_inc(v_nextMacroScope_111_);
lean_inc(v_env_110_);
lean_dec(v___x_109_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_122_ = l_Lean_Kernel_enableDiag(v_env_110_, v___y_107_);
v___x_123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 5, v___x_123_);
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_125_ = v___x_120_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_nextMacroScope_111_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_ngen_112_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_auxDeclNGen_113_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v_traceState_114_);
lean_ctor_set(v_reuseFailAlloc_127_, 5, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_127_, 6, v_recordedDeps_115_);
lean_ctor_set(v_reuseFailAlloc_127_, 7, v_messages_116_);
lean_ctor_set(v_reuseFailAlloc_127_, 8, v_infoState_117_);
lean_ctor_set(v_reuseFailAlloc_127_, 9, v_snapshotTasks_118_);
v___x_125_ = v_reuseFailAlloc_127_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; 
v___x_126_ = lean_st_ref_put(v_a_53_, v___x_125_);
lean_inc_ref(v_inheritedTraceOptions_71_);
lean_inc(v_cancelTk_x3f_70_);
lean_inc(v_currMacroScope_69_);
lean_inc(v_quotContext_68_);
lean_inc(v_maxHeartbeats_67_);
lean_inc(v_initHeartbeats_66_);
lean_inc(v_openDecls_65_);
lean_inc(v_currNamespace_64_);
lean_inc_ref(v_fileMap_62_);
lean_inc_ref(v_fileName_61_);
v___y_82_ = v___y_106_;
v___y_83_ = v___y_108_;
v_fileName_84_ = v_fileName_61_;
v_fileMap_85_ = v_fileMap_62_;
v_currNamespace_86_ = v_currNamespace_64_;
v_openDecls_87_ = v_openDecls_65_;
v_initHeartbeats_88_ = v_initHeartbeats_66_;
v_maxHeartbeats_89_ = v_maxHeartbeats_67_;
v_quotContext_90_ = v_quotContext_68_;
v_currMacroScope_91_ = v_currMacroScope_69_;
v_cancelTk_x3f_92_ = v_cancelTk_x3f_70_;
v_inheritedTraceOptions_93_ = v_inheritedTraceOptions_71_;
v_currRecDepth_94_ = v_currRecDepth_56_;
v_ref_95_ = v_ref_57_;
v_suppressElabErrors_96_ = v_suppressElabErrors_58_;
v_checkDeprecated_97_ = v_checkDeprecated_59_;
v_isRecordingDeps_98_ = v_isRecordingDeps_60_;
v___y_99_ = v_a_53_;
goto v___jp_81_;
}
}
}
v___jp_130_:
{
uint16_t v___x_132_; lean_object* v___x_133_; lean_object* v_env_134_; uint8_t v___x_135_; uint16_t v___x_136_; uint16_t v___x_137_; uint16_t v___x_138_; uint8_t v___x_139_; 
v___x_132_ = l_Lean_OptionFlags_ofOptions(v___y_131_);
v___x_133_ = lean_st_ref_get(v_a_53_);
v_env_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc_ref(v_env_134_);
lean_dec(v___x_133_);
v___x_135_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_134_);
lean_dec_ref(v_env_134_);
v___x_136_ = 512;
v___x_137_ = lean_uint16_land(v___x_132_, v___x_136_);
v___x_138_ = 0;
v___x_139_ = lean_uint16_dec_eq(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
if (v___x_135_ == 0)
{
v___y_106_ = v___y_131_;
v___y_107_ = v___x_79_;
v___y_108_ = v___x_132_;
goto v___jp_105_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_71_);
lean_inc(v_cancelTk_x3f_70_);
lean_inc(v_currMacroScope_69_);
lean_inc(v_quotContext_68_);
lean_inc(v_maxHeartbeats_67_);
lean_inc(v_initHeartbeats_66_);
lean_inc(v_openDecls_65_);
lean_inc(v_currNamespace_64_);
lean_inc_ref(v_fileMap_62_);
lean_inc_ref(v_fileName_61_);
v___y_82_ = v___y_131_;
v___y_83_ = v___x_132_;
v_fileName_84_ = v_fileName_61_;
v_fileMap_85_ = v_fileMap_62_;
v_currNamespace_86_ = v_currNamespace_64_;
v_openDecls_87_ = v_openDecls_65_;
v_initHeartbeats_88_ = v_initHeartbeats_66_;
v_maxHeartbeats_89_ = v_maxHeartbeats_67_;
v_quotContext_90_ = v_quotContext_68_;
v_currMacroScope_91_ = v_currMacroScope_69_;
v_cancelTk_x3f_92_ = v_cancelTk_x3f_70_;
v_inheritedTraceOptions_93_ = v_inheritedTraceOptions_71_;
v_currRecDepth_94_ = v_currRecDepth_56_;
v_ref_95_ = v_ref_57_;
v_suppressElabErrors_96_ = v_suppressElabErrors_58_;
v_checkDeprecated_97_ = v_checkDeprecated_59_;
v_isRecordingDeps_98_ = v_isRecordingDeps_60_;
v___y_99_ = v_a_53_;
goto v___jp_81_;
}
}
else
{
if (v___x_135_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_71_);
lean_inc(v_cancelTk_x3f_70_);
lean_inc(v_currMacroScope_69_);
lean_inc(v_quotContext_68_);
lean_inc(v_maxHeartbeats_67_);
lean_inc(v_initHeartbeats_66_);
lean_inc(v_openDecls_65_);
lean_inc(v_currNamespace_64_);
lean_inc_ref(v_fileMap_62_);
lean_inc_ref(v_fileName_61_);
v___y_82_ = v___y_131_;
v___y_83_ = v___x_132_;
v_fileName_84_ = v_fileName_61_;
v_fileMap_85_ = v_fileMap_62_;
v_currNamespace_86_ = v_currNamespace_64_;
v_openDecls_87_ = v_openDecls_65_;
v_initHeartbeats_88_ = v_initHeartbeats_66_;
v_maxHeartbeats_89_ = v_maxHeartbeats_67_;
v_quotContext_90_ = v_quotContext_68_;
v_currMacroScope_91_ = v_currMacroScope_69_;
v_cancelTk_x3f_92_ = v_cancelTk_x3f_70_;
v_inheritedTraceOptions_93_ = v_inheritedTraceOptions_71_;
v_currRecDepth_94_ = v_currRecDepth_56_;
v_ref_95_ = v_ref_57_;
v_suppressElabErrors_96_ = v_suppressElabErrors_58_;
v_checkDeprecated_97_ = v_checkDeprecated_59_;
v_isRecordingDeps_98_ = v_isRecordingDeps_60_;
v___y_99_ = v_a_53_;
goto v___jp_81_;
}
else
{
v___y_106_ = v___y_131_;
v___y_107_ = v___x_80_;
v___y_108_ = v___x_132_;
goto v___jp_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___boxed(lean_object* v_name_143_, lean_object* v_value_144_, lean_object* v_type_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_name_143_, v_value_144_, v_type_145_, v_a_146_, v_a_147_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
return v_res_149_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_unsigned_to_nat(32u);
v___x_151_ = lean_mk_empty_array_with_capacity(v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_153_ = ((size_t)5ULL);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_unsigned_to_nat(32u);
v___x_156_ = lean_mk_empty_array_with_capacity(v___x_155_);
v___x_157_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0);
v___x_158_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v___x_154_);
lean_ctor_set(v___x_158_, 3, v___x_154_);
lean_ctor_set_usize(v___x_158_, 4, v___x_153_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; lean_object* v_traceState_162_; lean_object* v_traces_163_; lean_object* v___x_164_; lean_object* v_traceState_165_; lean_object* v_env_166_; lean_object* v_nextMacroScope_167_; lean_object* v_ngen_168_; lean_object* v_auxDeclNGen_169_; lean_object* v_cache_170_; lean_object* v_recordedDeps_171_; lean_object* v_messages_172_; lean_object* v_infoState_173_; lean_object* v_snapshotTasks_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_193_; 
v___x_161_ = lean_st_ref_get(v___y_159_);
v_traceState_162_ = lean_ctor_get(v___x_161_, 4);
lean_inc_ref(v_traceState_162_);
lean_dec(v___x_161_);
v_traces_163_ = lean_ctor_get(v_traceState_162_, 0);
lean_inc_ref(v_traces_163_);
lean_dec_ref(v_traceState_162_);
v___x_164_ = lean_st_ref_take(v___y_159_);
v_traceState_165_ = lean_ctor_get(v___x_164_, 4);
v_env_166_ = lean_ctor_get(v___x_164_, 0);
v_nextMacroScope_167_ = lean_ctor_get(v___x_164_, 1);
v_ngen_168_ = lean_ctor_get(v___x_164_, 2);
v_auxDeclNGen_169_ = lean_ctor_get(v___x_164_, 3);
v_cache_170_ = lean_ctor_get(v___x_164_, 5);
v_recordedDeps_171_ = lean_ctor_get(v___x_164_, 6);
v_messages_172_ = lean_ctor_get(v___x_164_, 7);
v_infoState_173_ = lean_ctor_get(v___x_164_, 8);
v_snapshotTasks_174_ = lean_ctor_get(v___x_164_, 9);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_193_ == 0)
{
v___x_176_ = v___x_164_;
v_isShared_177_ = v_isSharedCheck_193_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_snapshotTasks_174_);
lean_inc(v_infoState_173_);
lean_inc(v_messages_172_);
lean_inc(v_recordedDeps_171_);
lean_inc(v_cache_170_);
lean_inc(v_traceState_165_);
lean_inc(v_auxDeclNGen_169_);
lean_inc(v_ngen_168_);
lean_inc(v_nextMacroScope_167_);
lean_inc(v_env_166_);
lean_dec(v___x_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_193_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
uint64_t v_tid_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_191_; 
v_tid_178_ = lean_ctor_get_uint64(v_traceState_165_, sizeof(void*)*1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_traceState_165_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v_traceState_165_, 0);
lean_dec(v_unused_192_);
v___x_180_ = v_traceState_165_;
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
else
{
lean_dec(v_traceState_165_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_182_);
v___x_184_ = v___x_180_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_182_);
lean_ctor_set_uint64(v_reuseFailAlloc_190_, sizeof(void*)*1, v_tid_178_);
v___x_184_ = v_reuseFailAlloc_190_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_184_);
v___x_186_ = v___x_176_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_env_166_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_nextMacroScope_167_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v_ngen_168_);
lean_ctor_set(v_reuseFailAlloc_189_, 3, v_auxDeclNGen_169_);
lean_ctor_set(v_reuseFailAlloc_189_, 4, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_189_, 5, v_cache_170_);
lean_ctor_set(v_reuseFailAlloc_189_, 6, v_recordedDeps_171_);
lean_ctor_set(v_reuseFailAlloc_189_, 7, v_messages_172_);
lean_ctor_set(v_reuseFailAlloc_189_, 8, v_infoState_173_);
lean_ctor_set(v_reuseFailAlloc_189_, 9, v_snapshotTasks_174_);
v___x_186_ = v_reuseFailAlloc_189_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_st_ref_put(v___y_159_, v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_traces_163_);
return v___x_188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___boxed(lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_194_);
lean_dec(v___y_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___boxed(lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_208_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_opts_209_, lean_object* v_opt_210_){
_start:
{
lean_object* v_name_211_; lean_object* v_defValue_212_; lean_object* v_map_213_; lean_object* v___x_214_; 
v_name_211_ = lean_ctor_get(v_opt_210_, 0);
v_defValue_212_ = lean_ctor_get(v_opt_210_, 1);
v_map_213_ = lean_ctor_get(v_opts_209_, 0);
v___x_214_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_213_, v_name_211_);
if (lean_obj_tag(v___x_214_) == 0)
{
uint8_t v___x_215_; 
v___x_215_ = lean_unbox(v_defValue_212_);
return v___x_215_;
}
else
{
lean_object* v_val_216_; 
v_val_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_214_, 1);
if (lean_obj_tag(v_val_216_) == 1)
{
uint8_t v_v_217_; 
v_v_217_ = lean_ctor_get_uint8(v_val_216_, 0);
lean_dec_ref_known(v_val_216_, 0);
return v_v_217_;
}
else
{
uint8_t v___x_218_; 
lean_dec(v_val_216_);
v___x_218_ = lean_unbox(v_defValue_212_);
return v___x_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_opts_219_, lean_object* v_opt_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_219_, v_opt_220_);
lean_dec_ref(v_opt_220_);
lean_dec_ref(v_opts_219_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_227_ = l_Lean_MessageData_ofFormat(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec_ref(v_x_236_);
return v_res_242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_247_ = l_Lean_MessageData_ofFormat(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec_ref(v_x_256_);
return v_res_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_267_ = l_Lean_MessageData_ofFormat(v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec_ref(v_x_276_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v_x_283_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v_x_283_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v_x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 1);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_a_293_ = lean_ctor_get(v_x_283_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v_x_283_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v_x_283_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 0);
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg___boxed(lean_object* v_x_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_301_);
return v_res_303_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(lean_object* v_e_304_){
_start:
{
if (lean_obj_tag(v_e_304_) == 0)
{
uint8_t v___x_305_; 
v___x_305_ = 2;
return v___x_305_;
}
else
{
uint8_t v___x_306_; 
v___x_306_ = 0;
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8___boxed(lean_object* v_e_307_){
_start:
{
uint8_t v_res_308_; lean_object* v_r_309_; 
v_res_308_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_e_307_);
lean_dec_ref(v_e_307_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(size_t v_sz_310_, size_t v_i_311_, lean_object* v_bs_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = lean_usize_dec_lt(v_i_311_, v_sz_310_);
if (v___x_313_ == 0)
{
return v_bs_312_;
}
else
{
lean_object* v_v_314_; lean_object* v_msg_315_; lean_object* v___x_316_; lean_object* v_bs_x27_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v_v_314_ = lean_array_uget_borrowed(v_bs_312_, v_i_311_);
v_msg_315_ = lean_ctor_get(v_v_314_, 1);
lean_inc_ref(v_msg_315_);
v___x_316_ = lean_unsigned_to_nat(0u);
v_bs_x27_317_ = lean_array_uset(v_bs_312_, v_i_311_, v___x_316_);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_add(v_i_311_, v___x_318_);
v___x_320_ = lean_array_uset(v_bs_x27_317_, v_i_311_, v_msg_315_);
v_i_311_ = v___x_319_;
v_bs_312_ = v___x_320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_322_, lean_object* v_i_323_, lean_object* v_bs_324_){
_start:
{
size_t v_sz_boxed_325_; size_t v_i_boxed_326_; lean_object* v_res_327_; 
v_sz_boxed_325_ = lean_unbox_usize(v_sz_322_);
lean_dec(v_sz_322_);
v_i_boxed_326_ = lean_unbox_usize(v_i_323_);
lean_dec(v_i_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_boxed_325_, v_i_boxed_326_, v_bs_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(lean_object* v_msgData_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; lean_object* v_env_335_; uint8_t v___x_336_; lean_object* v_env_337_; lean_object* v___x_338_; lean_object* v_toCold_339_; lean_object* v_mctx_340_; lean_object* v_lctx_341_; lean_object* v_options_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_334_ = lean_st_ref_get(v___y_332_);
v_env_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc_ref(v_env_335_);
lean_dec(v___x_334_);
v___x_336_ = 0;
v_env_337_ = l_Lean_Environment_setRecordingDeps(v_env_335_, v___x_336_);
v___x_338_ = lean_st_ref_get(v___y_330_);
v_toCold_339_ = lean_ctor_get(v___y_331_, 0);
v_mctx_340_ = lean_ctor_get(v___x_338_, 0);
lean_inc_ref(v_mctx_340_);
lean_dec(v___x_338_);
v_lctx_341_ = lean_ctor_get(v___y_329_, 2);
v_options_342_ = lean_ctor_get(v_toCold_339_, 2);
lean_inc_ref(v_options_342_);
lean_inc_ref(v_lctx_341_);
v___x_343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_343_, 0, v_env_337_);
lean_ctor_set(v___x_343_, 1, v_mctx_340_);
lean_ctor_set(v___x_343_, 2, v_lctx_341_);
lean_ctor_set(v___x_343_, 3, v_options_342_);
v___x_344_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_msgData_328_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6___boxed(lean_object* v_msgData_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msgData_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(lean_object* v_oldTraces_353_, lean_object* v_data_354_, lean_object* v_ref_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_toCold_362_; lean_object* v_currRecDepth_363_; lean_object* v_ref_364_; uint16_t v_optionFlags_365_; uint8_t v_suppressElabErrors_366_; uint8_t v_checkDeprecated_367_; uint8_t v_isRecordingDeps_368_; lean_object* v_ref_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_traceState_372_; lean_object* v_traces_373_; lean_object* v___x_374_; size_t v_sz_375_; size_t v___x_376_; lean_object* v___x_377_; lean_object* v_msg_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_418_; 
v_toCold_362_ = lean_ctor_get(v___y_359_, 0);
v_currRecDepth_363_ = lean_ctor_get(v___y_359_, 1);
v_ref_364_ = lean_ctor_get(v___y_359_, 2);
v_optionFlags_365_ = lean_ctor_get_uint16(v___y_359_, sizeof(void*)*3);
v_suppressElabErrors_366_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*3 + 2);
v_checkDeprecated_367_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*3 + 3);
v_isRecordingDeps_368_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*3 + 4);
v_ref_369_ = l_Lean_replaceRef(v_ref_355_, v_ref_364_);
lean_inc(v_currRecDepth_363_);
lean_inc_ref(v_toCold_362_);
v___x_370_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_370_, 0, v_toCold_362_);
lean_ctor_set(v___x_370_, 1, v_currRecDepth_363_);
lean_ctor_set(v___x_370_, 2, v_ref_369_);
lean_ctor_set_uint16(v___x_370_, sizeof(void*)*3, v_optionFlags_365_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*3 + 2, v_suppressElabErrors_366_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*3 + 3, v_checkDeprecated_367_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*3 + 4, v_isRecordingDeps_368_);
v___x_371_ = lean_st_ref_get(v___y_360_);
v_traceState_372_ = lean_ctor_get(v___x_371_, 4);
lean_inc_ref(v_traceState_372_);
lean_dec(v___x_371_);
v_traces_373_ = lean_ctor_get(v_traceState_372_, 0);
lean_inc_ref(v_traces_373_);
lean_dec_ref(v_traceState_372_);
v___x_374_ = l_Lean_PersistentArray_toArray___redArg(v_traces_373_);
lean_dec_ref(v_traces_373_);
v_sz_375_ = lean_array_size(v___x_374_);
v___x_376_ = ((size_t)0ULL);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_375_, v___x_376_, v___x_374_);
v_msg_378_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_378_, 0, v_data_354_);
lean_ctor_set(v_msg_378_, 1, v_msg_356_);
lean_ctor_set(v_msg_378_, 2, v___x_377_);
v___x_379_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_378_, v___y_357_, v___y_358_, v___x_370_, v___y_360_);
lean_dec_ref_known(v___x_370_, 3);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_418_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_418_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_418_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v_traceState_385_; lean_object* v_env_386_; lean_object* v_nextMacroScope_387_; lean_object* v_ngen_388_; lean_object* v_auxDeclNGen_389_; lean_object* v_cache_390_; lean_object* v_recordedDeps_391_; lean_object* v_messages_392_; lean_object* v_infoState_393_; lean_object* v_snapshotTasks_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_417_; 
v___x_384_ = lean_st_ref_take(v___y_360_);
v_traceState_385_ = lean_ctor_get(v___x_384_, 4);
v_env_386_ = lean_ctor_get(v___x_384_, 0);
v_nextMacroScope_387_ = lean_ctor_get(v___x_384_, 1);
v_ngen_388_ = lean_ctor_get(v___x_384_, 2);
v_auxDeclNGen_389_ = lean_ctor_get(v___x_384_, 3);
v_cache_390_ = lean_ctor_get(v___x_384_, 5);
v_recordedDeps_391_ = lean_ctor_get(v___x_384_, 6);
v_messages_392_ = lean_ctor_get(v___x_384_, 7);
v_infoState_393_ = lean_ctor_get(v___x_384_, 8);
v_snapshotTasks_394_ = lean_ctor_get(v___x_384_, 9);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_417_ == 0)
{
v___x_396_ = v___x_384_;
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_snapshotTasks_394_);
lean_inc(v_infoState_393_);
lean_inc(v_messages_392_);
lean_inc(v_recordedDeps_391_);
lean_inc(v_cache_390_);
lean_inc(v_traceState_385_);
lean_inc(v_auxDeclNGen_389_);
lean_inc(v_ngen_388_);
lean_inc(v_nextMacroScope_387_);
lean_inc(v_env_386_);
lean_dec(v___x_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_417_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint64_t v_tid_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_415_; 
v_tid_398_ = lean_ctor_get_uint64(v_traceState_385_, sizeof(void*)*1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_traceState_385_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v_traceState_385_, 0);
lean_dec(v_unused_416_);
v___x_400_ = v_traceState_385_;
v_isShared_401_ = v_isSharedCheck_415_;
goto v_resetjp_399_;
}
else
{
lean_dec(v_traceState_385_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_415_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_402_ = lean_box(0);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_ref_355_);
lean_ctor_set(v___x_403_, 1, v_a_380_);
v___x_404_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_353_, v___x_403_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_404_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_404_);
lean_ctor_set_uint64(v_reuseFailAlloc_414_, sizeof(void*)*1, v_tid_398_);
v___x_406_ = v_reuseFailAlloc_414_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_408_; 
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 4, v___x_406_);
v___x_408_ = v___x_396_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_env_386_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_nextMacroScope_387_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_ngen_388_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_auxDeclNGen_389_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_cache_390_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_recordedDeps_391_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_messages_392_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_infoState_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 9, v_snapshotTasks_394_);
v___x_408_ = v_reuseFailAlloc_413_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_st_ref_put(v___y_360_, v___x_408_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_402_);
v___x_411_ = v___x_382_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_402_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2___boxed(lean_object* v_oldTraces_419_, lean_object* v_data_420_, lean_object* v_ref_421_, lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_419_, v_data_420_, v_ref_421_, v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0(void){
_start:
{
lean_object* v___x_429_; double v___x_430_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_float_of_nat(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3(void){
_start:
{
lean_object* v___x_434_; double v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(1000u);
v___x_435_ = lean_float_of_nat(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(lean_object* v_cls_436_, uint8_t v_collapsed_437_, lean_object* v_tag_438_, lean_object* v_opts_439_, uint8_t v_clsEnabled_440_, lean_object* v_oldTraces_441_, lean_object* v_msg_442_, lean_object* v_resStartStop_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v_data_454_; lean_object* v_fst_457_; lean_object* v_snd_458_; lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___y_462_; lean_object* v_a_463_; uint8_t v___y_478_; double v___y_510_; 
v_fst_449_ = lean_ctor_get(v_resStartStop_443_, 0);
lean_inc(v_fst_449_);
v_snd_450_ = lean_ctor_get(v_resStartStop_443_, 1);
lean_inc(v_snd_450_);
lean_dec_ref(v_resStartStop_443_);
v_fst_457_ = lean_ctor_get(v_snd_450_, 0);
lean_inc(v_fst_457_);
v_snd_458_ = lean_ctor_get(v_snd_450_, 1);
lean_inc(v_snd_458_);
lean_dec(v_snd_450_);
v___x_459_ = l_Lean_trace_profiler;
v___x_460_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_439_, v___x_459_);
if (v___x_460_ == 0)
{
v___y_478_ = v___x_460_;
goto v___jp_477_;
}
else
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = l_Lean_trace_profiler_useHeartbeats;
v___x_516_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_439_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; double v___x_519_; double v___x_520_; double v___x_521_; 
v___x_517_ = l_Lean_trace_profiler_threshold;
v___x_518_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_439_, v___x_517_);
v___x_519_ = lean_float_of_nat(v___x_518_);
v___x_520_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_521_ = lean_float_div(v___x_519_, v___x_520_);
v___y_510_ = v___x_521_;
goto v___jp_509_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; double v___x_524_; 
v___x_522_ = l_Lean_trace_profiler_threshold;
v___x_523_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_439_, v___x_522_);
v___x_524_ = lean_float_of_nat(v___x_523_);
v___y_510_ = v___x_524_;
goto v___jp_509_;
}
}
v___jp_451_:
{
lean_object* v___x_455_; 
lean_inc(v___y_453_);
v___x_455_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_441_, v_data_454_, v___y_453_, v___y_452_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; 
lean_dec_ref_known(v___x_455_, 1);
v___x_456_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_449_);
return v___x_456_;
}
else
{
lean_dec(v_fst_449_);
return v___x_455_;
}
}
v___jp_461_:
{
uint8_t v_result_464_; lean_object* v___x_465_; lean_object* v___x_466_; double v___x_467_; lean_object* v_data_468_; 
v_result_464_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_fst_449_);
v___x_465_ = lean_box(v_result_464_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
v___x_467_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_438_);
lean_inc_ref(v___x_466_);
lean_inc(v_cls_436_);
v_data_468_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_468_, 0, v_cls_436_);
lean_ctor_set(v_data_468_, 1, v___x_466_);
lean_ctor_set(v_data_468_, 2, v_tag_438_);
lean_ctor_set_float(v_data_468_, sizeof(void*)*3, v___x_467_);
lean_ctor_set_float(v_data_468_, sizeof(void*)*3 + 8, v___x_467_);
lean_ctor_set_uint8(v_data_468_, sizeof(void*)*3 + 16, v_collapsed_437_);
if (v___x_460_ == 0)
{
lean_dec_ref_known(v___x_466_, 1);
lean_dec(v_snd_458_);
lean_dec(v_fst_457_);
lean_dec_ref(v_tag_438_);
lean_dec(v_cls_436_);
v___y_452_ = v_a_463_;
v___y_453_ = v___y_462_;
v_data_454_ = v_data_468_;
goto v___jp_451_;
}
else
{
lean_object* v_data_469_; double v___x_470_; double v___x_471_; 
lean_dec_ref_known(v_data_468_, 3);
v_data_469_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_469_, 0, v_cls_436_);
lean_ctor_set(v_data_469_, 1, v___x_466_);
lean_ctor_set(v_data_469_, 2, v_tag_438_);
v___x_470_ = lean_unbox_float(v_fst_457_);
lean_dec(v_fst_457_);
lean_ctor_set_float(v_data_469_, sizeof(void*)*3, v___x_470_);
v___x_471_ = lean_unbox_float(v_snd_458_);
lean_dec(v_snd_458_);
lean_ctor_set_float(v_data_469_, sizeof(void*)*3 + 8, v___x_471_);
lean_ctor_set_uint8(v_data_469_, sizeof(void*)*3 + 16, v_collapsed_437_);
v___y_452_ = v_a_463_;
v___y_453_ = v___y_462_;
v_data_454_ = v_data_469_;
goto v___jp_451_;
}
}
v___jp_472_:
{
lean_object* v_ref_473_; lean_object* v___x_474_; 
v_ref_473_ = lean_ctor_get(v___y_446_, 2);
lean_inc(v___y_447_);
lean_inc_ref(v___y_446_);
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
lean_inc(v_fst_449_);
v___x_474_ = lean_apply_6(v_msg_442_, v_fst_449_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, lean_box(0));
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___y_462_ = v_ref_473_;
v_a_463_ = v_a_475_;
goto v___jp_461_;
}
else
{
lean_object* v___x_476_; 
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_462_ = v_ref_473_;
v_a_463_ = v___x_476_;
goto v___jp_461_;
}
}
v___jp_477_:
{
if (v_clsEnabled_440_ == 0)
{
if (v___y_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_traceState_480_; lean_object* v_env_481_; lean_object* v_nextMacroScope_482_; lean_object* v_ngen_483_; lean_object* v_auxDeclNGen_484_; lean_object* v_cache_485_; lean_object* v_recordedDeps_486_; lean_object* v_messages_487_; lean_object* v_infoState_488_; lean_object* v_snapshotTasks_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_snd_458_);
lean_dec(v_fst_457_);
lean_dec_ref(v_msg_442_);
lean_dec_ref(v_tag_438_);
lean_dec(v_cls_436_);
v___x_479_ = lean_st_ref_take(v___y_447_);
v_traceState_480_ = lean_ctor_get(v___x_479_, 4);
v_env_481_ = lean_ctor_get(v___x_479_, 0);
v_nextMacroScope_482_ = lean_ctor_get(v___x_479_, 1);
v_ngen_483_ = lean_ctor_get(v___x_479_, 2);
v_auxDeclNGen_484_ = lean_ctor_get(v___x_479_, 3);
v_cache_485_ = lean_ctor_get(v___x_479_, 5);
v_recordedDeps_486_ = lean_ctor_get(v___x_479_, 6);
v_messages_487_ = lean_ctor_get(v___x_479_, 7);
v_infoState_488_ = lean_ctor_get(v___x_479_, 8);
v_snapshotTasks_489_ = lean_ctor_get(v___x_479_, 9);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_508_ == 0)
{
v___x_491_ = v___x_479_;
v_isShared_492_ = v_isSharedCheck_508_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_snapshotTasks_489_);
lean_inc(v_infoState_488_);
lean_inc(v_messages_487_);
lean_inc(v_recordedDeps_486_);
lean_inc(v_cache_485_);
lean_inc(v_traceState_480_);
lean_inc(v_auxDeclNGen_484_);
lean_inc(v_ngen_483_);
lean_inc(v_nextMacroScope_482_);
lean_inc(v_env_481_);
lean_dec(v___x_479_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_508_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
uint64_t v_tid_493_; lean_object* v_traces_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_507_; 
v_tid_493_ = lean_ctor_get_uint64(v_traceState_480_, sizeof(void*)*1);
v_traces_494_ = lean_ctor_get(v_traceState_480_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_traceState_480_);
if (v_isSharedCheck_507_ == 0)
{
v___x_496_ = v_traceState_480_;
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_traces_494_);
lean_dec(v_traceState_480_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_441_, v_traces_494_);
lean_dec_ref(v_traces_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_498_);
lean_ctor_set_uint64(v_reuseFailAlloc_506_, sizeof(void*)*1, v_tid_493_);
v___x_500_ = v_reuseFailAlloc_506_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 4, v___x_500_);
v___x_502_ = v___x_491_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_env_481_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_nextMacroScope_482_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_ngen_483_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_auxDeclNGen_484_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_505_, 5, v_cache_485_);
lean_ctor_set(v_reuseFailAlloc_505_, 6, v_recordedDeps_486_);
lean_ctor_set(v_reuseFailAlloc_505_, 7, v_messages_487_);
lean_ctor_set(v_reuseFailAlloc_505_, 8, v_infoState_488_);
lean_ctor_set(v_reuseFailAlloc_505_, 9, v_snapshotTasks_489_);
v___x_502_ = v_reuseFailAlloc_505_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_st_ref_put(v___y_447_, v___x_502_);
v___x_504_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_449_);
return v___x_504_;
}
}
}
}
}
else
{
goto v___jp_472_;
}
}
else
{
goto v___jp_472_;
}
}
v___jp_509_:
{
double v___x_511_; double v___x_512_; double v___x_513_; uint8_t v___x_514_; 
v___x_511_ = lean_unbox_float(v_snd_458_);
v___x_512_ = lean_unbox_float(v_fst_457_);
v___x_513_ = lean_float_sub(v___x_511_, v___x_512_);
v___x_514_ = lean_float_decLt(v___y_510_, v___x_513_);
v___y_478_ = v___x_514_;
goto v___jp_477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___boxed(lean_object* v_cls_525_, lean_object* v_collapsed_526_, lean_object* v_tag_527_, lean_object* v_opts_528_, lean_object* v_clsEnabled_529_, lean_object* v_oldTraces_530_, lean_object* v_msg_531_, lean_object* v_resStartStop_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
uint8_t v_collapsed_boxed_538_; uint8_t v_clsEnabled_boxed_539_; lean_object* v_res_540_; 
v_collapsed_boxed_538_ = lean_unbox(v_collapsed_526_);
v_clsEnabled_boxed_539_ = lean_unbox(v_clsEnabled_529_);
v_res_540_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v_cls_525_, v_collapsed_boxed_538_, v_tag_527_, v_opts_528_, v_clsEnabled_boxed_539_, v_oldTraces_530_, v_msg_531_, v_resStartStop_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec_ref(v_opts_528_);
return v_res_540_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(lean_object* v_e_541_){
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
lean_object* v_a_543_; uint8_t v___x_544_; 
v_a_543_ = lean_ctor_get(v_e_541_, 0);
v___x_544_ = l_Lean_Expr_hasSyntheticSorry(v_a_543_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = 0;
return v___x_545_;
}
else
{
uint8_t v___x_546_; 
v___x_546_ = 1;
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4___boxed(lean_object* v_e_547_){
_start:
{
uint8_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_e_547_);
lean_dec_ref(v_e_547_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_cls_550_, uint8_t v_collapsed_551_, lean_object* v_tag_552_, lean_object* v_opts_553_, uint8_t v_clsEnabled_554_, lean_object* v_oldTraces_555_, lean_object* v_msg_556_, lean_object* v_resStartStop_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v_data_568_; lean_object* v_fst_579_; lean_object* v_snd_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___y_584_; lean_object* v_a_585_; uint8_t v___y_600_; double v___y_632_; 
v_fst_563_ = lean_ctor_get(v_resStartStop_557_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v_resStartStop_557_, 1);
lean_inc(v_snd_564_);
lean_dec_ref(v_resStartStop_557_);
v_fst_579_ = lean_ctor_get(v_snd_564_, 0);
lean_inc(v_fst_579_);
v_snd_580_ = lean_ctor_get(v_snd_564_, 1);
lean_inc(v_snd_580_);
lean_dec(v_snd_564_);
v___x_581_ = l_Lean_trace_profiler;
v___x_582_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_553_, v___x_581_);
if (v___x_582_ == 0)
{
v___y_600_ = v___x_582_;
goto v___jp_599_;
}
else
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = l_Lean_trace_profiler_useHeartbeats;
v___x_638_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_553_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; double v___x_641_; double v___x_642_; double v___x_643_; 
v___x_639_ = l_Lean_trace_profiler_threshold;
v___x_640_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_553_, v___x_639_);
v___x_641_ = lean_float_of_nat(v___x_640_);
v___x_642_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_643_ = lean_float_div(v___x_641_, v___x_642_);
v___y_632_ = v___x_643_;
goto v___jp_631_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; double v___x_646_; 
v___x_644_ = l_Lean_trace_profiler_threshold;
v___x_645_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_553_, v___x_644_);
v___x_646_ = lean_float_of_nat(v___x_645_);
v___y_632_ = v___x_646_;
goto v___jp_631_;
}
}
v___jp_565_:
{
lean_object* v___x_569_; 
lean_inc(v___y_567_);
v___x_569_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_555_, v_data_568_, v___y_567_, v___y_566_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_570_; 
lean_dec_ref_known(v___x_569_, 1);
v___x_570_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_563_);
return v___x_570_;
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_fst_563_);
v_a_571_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_569_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
v___jp_583_:
{
uint8_t v_result_586_; lean_object* v___x_587_; lean_object* v___x_588_; double v___x_589_; lean_object* v_data_590_; 
v_result_586_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_fst_563_);
v___x_587_ = lean_box(v_result_586_);
v___x_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
v___x_589_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_552_);
lean_inc_ref(v___x_588_);
lean_inc(v_cls_550_);
v_data_590_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_590_, 0, v_cls_550_);
lean_ctor_set(v_data_590_, 1, v___x_588_);
lean_ctor_set(v_data_590_, 2, v_tag_552_);
lean_ctor_set_float(v_data_590_, sizeof(void*)*3, v___x_589_);
lean_ctor_set_float(v_data_590_, sizeof(void*)*3 + 8, v___x_589_);
lean_ctor_set_uint8(v_data_590_, sizeof(void*)*3 + 16, v_collapsed_551_);
if (v___x_582_ == 0)
{
lean_dec_ref_known(v___x_588_, 1);
lean_dec(v_snd_580_);
lean_dec(v_fst_579_);
lean_dec_ref(v_tag_552_);
lean_dec(v_cls_550_);
v___y_566_ = v_a_585_;
v___y_567_ = v___y_584_;
v_data_568_ = v_data_590_;
goto v___jp_565_;
}
else
{
lean_object* v_data_591_; double v___x_592_; double v___x_593_; 
lean_dec_ref_known(v_data_590_, 3);
v_data_591_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_591_, 0, v_cls_550_);
lean_ctor_set(v_data_591_, 1, v___x_588_);
lean_ctor_set(v_data_591_, 2, v_tag_552_);
v___x_592_ = lean_unbox_float(v_fst_579_);
lean_dec(v_fst_579_);
lean_ctor_set_float(v_data_591_, sizeof(void*)*3, v___x_592_);
v___x_593_ = lean_unbox_float(v_snd_580_);
lean_dec(v_snd_580_);
lean_ctor_set_float(v_data_591_, sizeof(void*)*3 + 8, v___x_593_);
lean_ctor_set_uint8(v_data_591_, sizeof(void*)*3 + 16, v_collapsed_551_);
v___y_566_ = v_a_585_;
v___y_567_ = v___y_584_;
v_data_568_ = v_data_591_;
goto v___jp_565_;
}
}
v___jp_594_:
{
lean_object* v_ref_595_; lean_object* v___x_596_; 
v_ref_595_ = lean_ctor_get(v___y_560_, 2);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v_fst_563_);
v___x_596_ = lean_apply_6(v_msg_556_, v_fst_563_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, lean_box(0));
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___y_584_ = v_ref_595_;
v_a_585_ = v_a_597_;
goto v___jp_583_;
}
else
{
lean_object* v___x_598_; 
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_584_ = v_ref_595_;
v_a_585_ = v___x_598_;
goto v___jp_583_;
}
}
v___jp_599_:
{
if (v_clsEnabled_554_ == 0)
{
if (v___y_600_ == 0)
{
lean_object* v___x_601_; lean_object* v_traceState_602_; lean_object* v_env_603_; lean_object* v_nextMacroScope_604_; lean_object* v_ngen_605_; lean_object* v_auxDeclNGen_606_; lean_object* v_cache_607_; lean_object* v_recordedDeps_608_; lean_object* v_messages_609_; lean_object* v_infoState_610_; lean_object* v_snapshotTasks_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_630_; 
lean_dec(v_snd_580_);
lean_dec(v_fst_579_);
lean_dec_ref(v_msg_556_);
lean_dec_ref(v_tag_552_);
lean_dec(v_cls_550_);
v___x_601_ = lean_st_ref_take(v___y_561_);
v_traceState_602_ = lean_ctor_get(v___x_601_, 4);
v_env_603_ = lean_ctor_get(v___x_601_, 0);
v_nextMacroScope_604_ = lean_ctor_get(v___x_601_, 1);
v_ngen_605_ = lean_ctor_get(v___x_601_, 2);
v_auxDeclNGen_606_ = lean_ctor_get(v___x_601_, 3);
v_cache_607_ = lean_ctor_get(v___x_601_, 5);
v_recordedDeps_608_ = lean_ctor_get(v___x_601_, 6);
v_messages_609_ = lean_ctor_get(v___x_601_, 7);
v_infoState_610_ = lean_ctor_get(v___x_601_, 8);
v_snapshotTasks_611_ = lean_ctor_get(v___x_601_, 9);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_630_ == 0)
{
v___x_613_ = v___x_601_;
v_isShared_614_ = v_isSharedCheck_630_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snapshotTasks_611_);
lean_inc(v_infoState_610_);
lean_inc(v_messages_609_);
lean_inc(v_recordedDeps_608_);
lean_inc(v_cache_607_);
lean_inc(v_traceState_602_);
lean_inc(v_auxDeclNGen_606_);
lean_inc(v_ngen_605_);
lean_inc(v_nextMacroScope_604_);
lean_inc(v_env_603_);
lean_dec(v___x_601_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_630_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint64_t v_tid_615_; lean_object* v_traces_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_629_; 
v_tid_615_ = lean_ctor_get_uint64(v_traceState_602_, sizeof(void*)*1);
v_traces_616_ = lean_ctor_get(v_traceState_602_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_traceState_602_);
if (v_isSharedCheck_629_ == 0)
{
v___x_618_ = v_traceState_602_;
v_isShared_619_ = v_isSharedCheck_629_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_traces_616_);
lean_dec(v_traceState_602_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_629_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_555_, v_traces_616_);
lean_dec_ref(v_traces_616_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_620_);
lean_ctor_set_uint64(v_reuseFailAlloc_628_, sizeof(void*)*1, v_tid_615_);
v___x_622_ = v_reuseFailAlloc_628_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v___x_622_);
v___x_624_ = v___x_613_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_env_603_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_nextMacroScope_604_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_ngen_605_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_auxDeclNGen_606_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v_cache_607_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_recordedDeps_608_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_messages_609_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v_infoState_610_);
lean_ctor_set(v_reuseFailAlloc_627_, 9, v_snapshotTasks_611_);
v___x_624_ = v_reuseFailAlloc_627_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_st_ref_put(v___y_561_, v___x_624_);
v___x_626_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_563_);
return v___x_626_;
}
}
}
}
}
else
{
goto v___jp_594_;
}
}
else
{
goto v___jp_594_;
}
}
v___jp_631_:
{
double v___x_633_; double v___x_634_; double v___x_635_; uint8_t v___x_636_; 
v___x_633_ = lean_unbox_float(v_snd_580_);
v___x_634_ = lean_unbox_float(v_fst_579_);
v___x_635_ = lean_float_sub(v___x_633_, v___x_634_);
v___x_636_ = lean_float_decLt(v___y_632_, v___x_635_);
v___y_600_ = v___x_636_;
goto v___jp_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_cls_647_, lean_object* v_collapsed_648_, lean_object* v_tag_649_, lean_object* v_opts_650_, lean_object* v_clsEnabled_651_, lean_object* v_oldTraces_652_, lean_object* v_msg_653_, lean_object* v_resStartStop_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
uint8_t v_collapsed_boxed_660_; uint8_t v_clsEnabled_boxed_661_; lean_object* v_res_662_; 
v_collapsed_boxed_660_ = lean_unbox(v_collapsed_648_);
v_clsEnabled_boxed_661_ = lean_unbox(v_clsEnabled_651_);
v_res_662_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_cls_647_, v_collapsed_boxed_660_, v_tag_649_, v_opts_650_, v_clsEnabled_boxed_661_, v_oldTraces_652_, v_msg_653_, v_resStartStop_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec_ref(v_opts_650_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(lean_object* v_msg_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_ref_669_; lean_object* v___x_670_; lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_ref_669_ = lean_ctor_get(v___y_666_, 2);
v___x_670_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
lean_inc(v_ref_669_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_ref_669_);
lean_ctor_set(v___x_675_, 1, v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 1);
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg___boxed(lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_box(0);
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_706_ = l_Lean_mkConst(v___x_705_, v___x_704_);
return v___x_706_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_708_; double v___x_709_; 
v___x_708_ = lean_unsigned_to_nat(1000000000u);
v___x_709_ = lean_float_of_nat(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_716_ = l_Lean_stringToMessageData(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_box(0);
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_727_ = l_Lean_mkConst(v___x_726_, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_box(0);
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_736_ = l_Lean_mkConst(v___x_735_, v___x_734_);
return v___x_736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_738_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_739_ = l_Lean_Name_append(v___x_738_, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_box(0);
v___x_744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_745_ = l_Lean_mkConst(v___x_744_, v___x_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_747_, lean_object* v_ctx_748_, lean_object* v_reflectionResult_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_satExpr_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_1130_; 
v_satExpr_755_ = lean_ctor_get(v_reflectionResult_749_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_reflectionResult_749_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v_reflectionResult_749_, 1);
lean_dec(v_unused_1131_);
v___x_757_ = v_reflectionResult_749_;
v_isShared_758_ = v_isSharedCheck_1130_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_satExpr_755_);
lean_dec(v_reflectionResult_749_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_1130_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_toCold_759_; lean_object* v_options_760_; lean_object* v_exprDef_761_; lean_object* v_certDef_762_; lean_object* v_expr_763_; lean_object* v_ref_764_; lean_object* v_inheritedTraceOptions_765_; uint8_t v_hasTrace_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; uint8_t v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v_a_782_; lean_object* v___y_797_; uint8_t v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v_a_801_; lean_object* v___y_804_; uint8_t v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v_a_808_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v_a_815_; lean_object* v___y_825_; uint8_t v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v_a_829_; lean_object* v___y_832_; uint8_t v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v_a_836_; lean_object* v___y_839_; lean_object* v___y_840_; uint8_t v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_891_; uint8_t v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v_a_966_; uint8_t v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v_a_983_; uint8_t v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_1038_; 
v_toCold_759_ = lean_ctor_get(v_a_752_, 0);
v_options_760_ = lean_ctor_get(v_toCold_759_, 2);
v_exprDef_761_ = lean_ctor_get(v_ctx_748_, 0);
lean_inc(v_exprDef_761_);
v_certDef_762_ = lean_ctor_get(v_ctx_748_, 1);
lean_inc(v_certDef_762_);
lean_dec_ref(v_ctx_748_);
v_expr_763_ = lean_ctor_get(v_satExpr_755_, 2);
lean_inc_ref(v_expr_763_);
lean_dec_ref(v_satExpr_755_);
v_ref_764_ = lean_ctor_get(v_a_752_, 2);
v_inheritedTraceOptions_765_ = lean_ctor_get(v_toCold_759_, 11);
v_hasTrace_766_ = lean_ctor_get_uint8(v_options_760_, sizeof(void*)*1);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_773_ = lean_box(0);
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_775_ = 1;
v___x_776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_766_ == 0)
{
lean_object* v___x_1055_; 
lean_inc(v_exprDef_761_);
v___x_1055_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_761_, v_expr_763_, v___x_774_, v_a_752_, v_a_753_);
v___y_1038_ = v___x_1055_;
goto v___jp_1037_;
}
else
{
lean_object* v___f_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v_a_1062_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v_a_1077_; 
v___f_1056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1058_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_765_, v_options_760_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = l_Lean_trace_profiler;
v___x_1128_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_760_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_inc(v_exprDef_761_);
v___x_1129_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_761_, v_expr_763_, v___x_774_, v_a_752_, v_a_753_);
v___y_1038_ = v___x_1129_;
goto v___jp_1037_;
}
else
{
goto v___jp_1086_;
}
}
else
{
goto v___jp_1086_;
}
v___jp_1059_:
{
lean_object* v___x_1063_; double v___x_1064_; double v___x_1065_; double v___x_1066_; double v___x_1067_; double v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1063_ = lean_io_mono_nanos_now();
v___x_1064_ = lean_float_of_nat(v___y_1061_);
v___x_1065_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1066_ = lean_float_div(v___x_1064_, v___x_1065_);
v___x_1067_ = lean_float_of_nat(v___x_1063_);
v___x_1068_ = lean_float_div(v___x_1067_, v___x_1065_);
v___x_1069_ = lean_box_float(v___x_1066_);
v___x_1070_ = lean_box_float(v___x_1068_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_a_1062_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_768_, v___x_775_, v___x_776_, v_options_760_, v___x_1058_, v___y_1060_, v___f_1056_, v___x_1072_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
v___y_1038_ = v___x_1073_;
goto v___jp_1037_;
}
v___jp_1074_:
{
lean_object* v___x_1078_; double v___x_1079_; double v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1078_ = lean_io_get_num_heartbeats();
v___x_1079_ = lean_float_of_nat(v___y_1075_);
v___x_1080_ = lean_float_of_nat(v___x_1078_);
v___x_1081_ = lean_box_float(v___x_1079_);
v___x_1082_ = lean_box_float(v___x_1080_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_a_1077_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_768_, v___x_775_, v___x_776_, v_options_760_, v___x_1058_, v___y_1076_, v___f_1056_, v___x_1084_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
v___y_1038_ = v___x_1085_;
goto v___jp_1037_;
}
v___jp_1086_:
{
lean_object* v___x_1087_; lean_object* v_a_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1087_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_753_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref(v___x_1087_);
v___x_1089_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1090_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_760_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_761_);
v___x_1092_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_761_, v_expr_763_, v___x_774_, v_a_752_, v_a_753_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v___y_1060_ = v_a_1088_;
v___y_1061_ = v___x_1091_;
v_a_1062_ = v___x_1098_;
goto v___jp_1059_;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 0);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v___y_1060_ = v_a_1088_;
v___y_1061_ = v___x_1091_;
v_a_1062_ = v___x_1106_;
goto v___jp_1059_;
}
}
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_761_);
v___x_1110_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_761_, v_expr_763_, v___x_774_, v_a_752_, v_a_753_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 1);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v___y_1075_ = v___x_1109_;
v___y_1076_ = v_a_1088_;
v_a_1077_ = v___x_1116_;
goto v___jp_1074_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
v_a_1119_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1110_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1110_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 0);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v___y_1075_ = v___x_1109_;
v___y_1076_ = v_a_1088_;
v_a_1077_ = v___x_1124_;
goto v___jp_1074_;
}
}
}
}
}
}
v___jp_777_:
{
lean_object* v___x_783_; double v___x_784_; double v___x_785_; double v___x_786_; double v___x_787_; double v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_783_ = lean_io_mono_nanos_now();
v___x_784_ = lean_float_of_nat(v___y_780_);
v___x_785_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_786_ = lean_float_div(v___x_784_, v___x_785_);
v___x_787_ = lean_float_of_nat(v___x_783_);
v___x_788_ = lean_float_div(v___x_787_, v___x_785_);
v___x_789_ = lean_box_float(v___x_786_);
v___x_790_ = lean_box_float(v___x_788_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_790_);
lean_ctor_set(v___x_757_, 0, v___x_789_);
v___x_792_ = v___x_757_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_795_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_a_782_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_768_, v___x_775_, v___x_776_, v___y_779_, v___y_778_, v___y_781_, v___f_770_, v___x_793_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_794_;
}
}
v___jp_796_:
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v_a_801_);
v___y_778_ = v___y_798_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_799_;
v___y_781_ = v___y_800_;
v_a_782_ = v___x_802_;
goto v___jp_777_;
}
v___jp_803_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_a_808_);
v___y_778_ = v___y_805_;
v___y_779_ = v___y_804_;
v___y_780_ = v___y_806_;
v___y_781_ = v___y_807_;
v_a_782_ = v___x_809_;
goto v___jp_777_;
}
v___jp_810_:
{
lean_object* v___x_816_; double v___x_817_; double v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_816_ = lean_io_get_num_heartbeats();
v___x_817_ = lean_float_of_nat(v___y_813_);
v___x_818_ = lean_float_of_nat(v___x_816_);
v___x_819_ = lean_box_float(v___x_817_);
v___x_820_ = lean_box_float(v___x_818_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v_a_815_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_768_, v___x_775_, v___x_776_, v___y_812_, v___y_811_, v___y_814_, v___f_770_, v___x_822_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_823_;
}
v___jp_824_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_a_829_);
v___y_811_ = v___y_826_;
v___y_812_ = v___y_825_;
v___y_813_ = v___y_827_;
v___y_814_ = v___y_828_;
v_a_815_ = v___x_830_;
goto v___jp_810_;
}
v___jp_831_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v_a_836_);
v___y_811_ = v___y_833_;
v___y_812_ = v___y_832_;
v___y_813_ = v___y_834_;
v___y_814_ = v___y_835_;
v_a_815_ = v___x_837_;
goto v___jp_810_;
}
v___jp_838_:
{
lean_object* v___x_846_; lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_889_; 
v___x_846_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_753_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_889_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_889_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_889_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = l_Lean_trace_profiler_useHeartbeats;
v___x_852_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_842_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = lean_io_mono_nanos_now();
v___x_854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_839_);
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 1);
lean_ctor_set(v___x_849_, 0, v___y_839_);
v___x_856_ = v___x_849_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___y_839_);
v___x_856_ = v_reuseFailAlloc_870_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; 
lean_inc_ref(v___y_844_);
v___x_857_ = l_Lean_Meta_nativeEqTrue(v___x_854_, v___y_844_, v___x_856_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec_ref(v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
if (lean_obj_tag(v_a_858_) == 0)
{
lean_object* v_prf_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v___y_844_);
v_prf_859_ = lean_ctor_get(v_a_858_, 0);
lean_inc_ref(v_prf_859_);
lean_dec_ref_known(v_a_858_, 1);
v___x_860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_845_);
v___x_861_ = l_Lean_Name_mkStr5(v___x_771_, v___x_767_, v___x_772_, v___y_845_, v___x_860_);
v___x_862_ = l_Lean_mkConst(v___x_861_, v___x_773_);
v___x_863_ = l_Lean_mkApp3(v___x_862_, v___y_843_, v___y_840_, v_prf_859_);
v___y_804_ = v___y_842_;
v___y_805_ = v___y_841_;
v___y_806_ = v___x_853_;
v___y_807_ = v_a_847_;
v_a_808_ = v___x_863_;
goto v___jp_803_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_a_868_; 
lean_dec_ref(v___y_843_);
lean_dec_ref(v___y_840_);
v___x_864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_865_ = l_Lean_indentExpr(v___y_844_);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_866_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v___y_797_ = v___y_842_;
v___y_798_ = v___y_841_;
v___y_799_ = v___x_853_;
v___y_800_ = v_a_847_;
v_a_801_ = v_a_868_;
goto v___jp_796_;
}
}
else
{
lean_object* v_a_869_; 
lean_dec_ref(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec_ref(v___y_840_);
v_a_869_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_857_, 1);
v___y_797_ = v___y_842_;
v___y_798_ = v___y_841_;
v___y_799_ = v___x_853_;
v___y_800_ = v_a_847_;
v_a_801_ = v_a_869_;
goto v___jp_796_;
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_del_object(v___x_757_);
v___x_871_ = lean_io_get_num_heartbeats();
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_839_);
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 1);
lean_ctor_set(v___x_849_, 0, v___y_839_);
v___x_874_ = v___x_849_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___y_839_);
v___x_874_ = v_reuseFailAlloc_888_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; 
lean_inc_ref(v___y_844_);
v___x_875_ = l_Lean_Meta_nativeEqTrue(v___x_872_, v___y_844_, v___x_874_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec_ref(v___x_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_875_, 1);
if (lean_obj_tag(v_a_876_) == 0)
{
lean_object* v_prf_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref(v___y_844_);
v_prf_877_ = lean_ctor_get(v_a_876_, 0);
lean_inc_ref(v_prf_877_);
lean_dec_ref_known(v_a_876_, 1);
v___x_878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_845_);
v___x_879_ = l_Lean_Name_mkStr5(v___x_771_, v___x_767_, v___x_772_, v___y_845_, v___x_878_);
v___x_880_ = l_Lean_mkConst(v___x_879_, v___x_773_);
v___x_881_ = l_Lean_mkApp3(v___x_880_, v___y_843_, v___y_840_, v_prf_877_);
v___y_832_ = v___y_842_;
v___y_833_ = v___y_841_;
v___y_834_ = v___x_871_;
v___y_835_ = v_a_847_;
v_a_836_ = v___x_881_;
goto v___jp_831_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_a_886_; 
lean_dec_ref(v___y_843_);
lean_dec_ref(v___y_840_);
v___x_882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_883_ = l_Lean_indentExpr(v___y_844_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_884_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v___x_885_);
v___y_825_ = v___y_842_;
v___y_826_ = v___y_841_;
v___y_827_ = v___x_871_;
v___y_828_ = v_a_847_;
v_a_829_ = v_a_886_;
goto v___jp_824_;
}
}
else
{
lean_object* v_a_887_; 
lean_dec_ref(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec_ref(v___y_840_);
v_a_887_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_875_, 1);
v___y_825_ = v___y_842_;
v___y_826_ = v___y_841_;
v___y_827_ = v___x_871_;
v___y_828_ = v_a_847_;
v_a_829_ = v_a_887_;
goto v___jp_824_;
}
}
}
}
}
v___jp_890_:
{
if (lean_obj_tag(v___y_891_) == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref_known(v___y_891_, 1);
v___x_892_ = l_Lean_mkConst(v_exprDef_761_, v___x_773_);
v___x_893_ = l_Lean_mkConst(v_certDef_762_, v___x_773_);
v___x_894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_895_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_893_);
lean_inc_ref(v___x_892_);
v___x_896_ = l_Lean_mkAppB(v___x_895_, v___x_892_, v___x_893_);
if (v_hasTrace_766_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_del_object(v___x_757_);
v___x_897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_764_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_ref_764_);
lean_inc_ref(v___x_896_);
v___x_899_ = l_Lean_Meta_nativeEqTrue(v___x_897_, v___x_896_, v___x_898_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec_ref_known(v___x_898_, 1);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_914_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_914_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_914_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
if (lean_obj_tag(v_a_900_) == 0)
{
lean_object* v_prf_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
lean_dec_ref(v___x_896_);
v_prf_904_ = lean_ctor_get(v_a_900_, 0);
lean_inc_ref(v_prf_904_);
lean_dec_ref_known(v_a_900_, 1);
v___x_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_906_ = l_Lean_mkApp3(v___x_905_, v___x_892_, v___x_893_, v_prf_904_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_906_);
v___x_908_ = v___x_902_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_del_object(v___x_902_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_892_);
v___x_910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_911_ = l_Lean_indentExpr(v___x_896_);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_912_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_913_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_892_);
v_a_915_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_899_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_899_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_924_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_765_, v_options_760_, v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = l_Lean_trace_profiler;
v___x_926_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_760_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_del_object(v___x_757_);
v___x_927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_764_);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v_ref_764_);
lean_inc_ref(v___x_896_);
v___x_929_ = l_Lean_Meta_nativeEqTrue(v___x_927_, v___x_896_, v___x_928_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec_ref_known(v___x_928_, 1);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_944_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_944_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_944_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_944_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
if (lean_obj_tag(v_a_930_) == 0)
{
lean_object* v_prf_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec_ref(v___x_896_);
v_prf_934_ = lean_ctor_get(v_a_930_, 0);
lean_inc_ref(v_prf_934_);
lean_dec_ref_known(v_a_930_, 1);
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_936_ = l_Lean_mkApp3(v___x_935_, v___x_892_, v___x_893_, v_prf_934_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_936_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_del_object(v___x_932_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_892_);
v___x_940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_941_ = l_Lean_indentExpr(v___x_896_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_942_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_943_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_892_);
v_a_945_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_929_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_929_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
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
return v___x_950_;
}
}
}
}
else
{
v___y_839_ = v_ref_764_;
v___y_840_ = v___x_893_;
v___y_841_ = v___x_924_;
v___y_842_ = v_options_760_;
v___y_843_ = v___x_892_;
v___y_844_ = v___x_896_;
v___y_845_ = v___x_894_;
goto v___jp_838_;
}
}
else
{
v___y_839_ = v_ref_764_;
v___y_840_ = v___x_893_;
v___y_841_ = v___x_924_;
v___y_842_ = v_options_760_;
v___y_843_ = v___x_892_;
v___y_844_ = v___x_896_;
v___y_845_ = v___x_894_;
goto v___jp_838_;
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_certDef_762_);
lean_dec(v_exprDef_761_);
lean_del_object(v___x_757_);
v_a_953_ = lean_ctor_get(v___y_891_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___y_891_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___y_891_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___y_891_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
v___jp_961_:
{
lean_object* v___x_967_; double v___x_968_; double v___x_969_; double v___x_970_; double v___x_971_; double v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_967_ = lean_io_mono_nanos_now();
v___x_968_ = lean_float_of_nat(v___y_964_);
v___x_969_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_970_ = lean_float_div(v___x_968_, v___x_969_);
v___x_971_ = lean_float_of_nat(v___x_967_);
v___x_972_ = lean_float_div(v___x_971_, v___x_969_);
v___x_973_ = lean_box_float(v___x_970_);
v___x_974_ = lean_box_float(v___x_972_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v_a_966_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_768_, v___x_775_, v___x_776_, v___y_963_, v___y_962_, v___y_965_, v___f_769_, v___x_976_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
v___y_891_ = v___x_977_;
goto v___jp_890_;
}
v___jp_978_:
{
lean_object* v___x_984_; double v___x_985_; double v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_984_ = lean_io_get_num_heartbeats();
v___x_985_ = lean_float_of_nat(v___y_980_);
v___x_986_ = lean_float_of_nat(v___x_984_);
v___x_987_ = lean_box_float(v___x_985_);
v___x_988_ = lean_box_float(v___x_986_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v_a_983_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_768_, v___x_775_, v___x_776_, v___y_981_, v___y_979_, v___y_982_, v___f_769_, v___x_990_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
v___y_891_ = v___x_991_;
goto v___jp_890_;
}
v___jp_992_:
{
lean_object* v___x_997_; lean_object* v_a_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_997_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_753_);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
v___x_999_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1000_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_995_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_762_);
v___x_1002_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_762_, v___y_996_, v___y_994_, v_a_752_, v_a_753_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 1);
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
v___y_962_ = v___y_993_;
v___y_963_ = v___y_995_;
v___y_964_ = v___x_1001_;
v___y_965_ = v_a_998_;
v_a_966_ = v___x_1008_;
goto v___jp_961_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 0);
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
v___y_962_ = v___y_993_;
v___y_963_ = v___y_995_;
v___y_964_ = v___x_1001_;
v___y_965_ = v_a_998_;
v_a_966_ = v___x_1016_;
goto v___jp_961_;
}
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_762_);
v___x_1020_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_762_, v___y_996_, v___y_994_, v_a_752_, v_a_753_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
v___y_979_ = v___y_993_;
v___y_980_ = v___x_1019_;
v___y_981_ = v___y_995_;
v___y_982_ = v_a_998_;
v_a_983_ = v___x_1026_;
goto v___jp_978_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
v_a_1029_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1020_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1020_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 0);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
v___y_979_ = v___y_993_;
v___y_980_ = v___x_1019_;
v___y_981_ = v___y_995_;
v___y_982_ = v_a_998_;
v_a_983_ = v___x_1034_;
goto v___jp_978_;
}
}
}
}
}
v___jp_1037_:
{
if (lean_obj_tag(v___y_1038_) == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec_ref_known(v___y_1038_, 1);
v___x_1039_ = l_Lean_mkStrLit(v_cert_747_);
v___x_1040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_766_ == 0)
{
lean_object* v___x_1041_; 
lean_inc(v_certDef_762_);
v___x_1041_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_762_, v___x_1039_, v___x_1040_, v_a_752_, v_a_753_);
v___y_891_ = v___x_1041_;
goto v___jp_890_;
}
else
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1043_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_765_, v_options_760_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = l_Lean_trace_profiler;
v___x_1045_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_760_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_inc(v_certDef_762_);
v___x_1046_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_762_, v___x_1039_, v___x_1040_, v_a_752_, v_a_753_);
v___y_891_ = v___x_1046_;
goto v___jp_890_;
}
else
{
v___y_993_ = v___x_1043_;
v___y_994_ = v___x_1040_;
v___y_995_ = v_options_760_;
v___y_996_ = v___x_1039_;
goto v___jp_992_;
}
}
else
{
v___y_993_ = v___x_1043_;
v___y_994_ = v___x_1040_;
v___y_995_ = v_options_760_;
v___y_996_ = v___x_1039_;
goto v___jp_992_;
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_certDef_762_);
lean_dec(v_exprDef_761_);
lean_del_object(v___x_757_);
lean_dec_ref(v_cert_747_);
v_a_1047_ = lean_ctor_get(v___y_1038_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___y_1038_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___y_1038_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___y_1038_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
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
return v___x_1052_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1132_, lean_object* v_ctx_1133_, lean_object* v_reflectionResult_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1132_, v_ctx_1133_, v_reflectionResult_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_object* v_00_u03b1_1141_, lean_object* v_x_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_1142_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(v_00_u03b1_1149_, v_x_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_00_u03b1_1157_, lean_object* v_msg_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_msg_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_00_u03b1_1165_, v_msg_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v_traceState_1176_; lean_object* v_traces_1177_; lean_object* v___x_1178_; lean_object* v_traceState_1179_; lean_object* v_env_1180_; lean_object* v_nextMacroScope_1181_; lean_object* v_ngen_1182_; lean_object* v_auxDeclNGen_1183_; lean_object* v_cache_1184_; lean_object* v_recordedDeps_1185_; lean_object* v_messages_1186_; lean_object* v_infoState_1187_; lean_object* v_snapshotTasks_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1209_; 
v___x_1175_ = lean_st_ref_get(v___y_1173_);
v_traceState_1176_ = lean_ctor_get(v___x_1175_, 4);
lean_inc_ref(v_traceState_1176_);
lean_dec(v___x_1175_);
v_traces_1177_ = lean_ctor_get(v_traceState_1176_, 0);
lean_inc_ref(v_traces_1177_);
lean_dec_ref(v_traceState_1176_);
v___x_1178_ = lean_st_ref_take(v___y_1173_);
v_traceState_1179_ = lean_ctor_get(v___x_1178_, 4);
v_env_1180_ = lean_ctor_get(v___x_1178_, 0);
v_nextMacroScope_1181_ = lean_ctor_get(v___x_1178_, 1);
v_ngen_1182_ = lean_ctor_get(v___x_1178_, 2);
v_auxDeclNGen_1183_ = lean_ctor_get(v___x_1178_, 3);
v_cache_1184_ = lean_ctor_get(v___x_1178_, 5);
v_recordedDeps_1185_ = lean_ctor_get(v___x_1178_, 6);
v_messages_1186_ = lean_ctor_get(v___x_1178_, 7);
v_infoState_1187_ = lean_ctor_get(v___x_1178_, 8);
v_snapshotTasks_1188_ = lean_ctor_get(v___x_1178_, 9);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1190_ = v___x_1178_;
v_isShared_1191_ = v_isSharedCheck_1209_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snapshotTasks_1188_);
lean_inc(v_infoState_1187_);
lean_inc(v_messages_1186_);
lean_inc(v_recordedDeps_1185_);
lean_inc(v_cache_1184_);
lean_inc(v_traceState_1179_);
lean_inc(v_auxDeclNGen_1183_);
lean_inc(v_ngen_1182_);
lean_inc(v_nextMacroScope_1181_);
lean_inc(v_env_1180_);
lean_dec(v___x_1178_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1209_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
uint64_t v_tid_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1207_; 
v_tid_1192_ = lean_ctor_get_uint64(v_traceState_1179_, sizeof(void*)*1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_traceState_1179_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_traceState_1179_, 0);
lean_dec(v_unused_1208_);
v___x_1194_ = v_traceState_1179_;
v_isShared_1195_ = v_isSharedCheck_1207_;
goto v_resetjp_1193_;
}
else
{
lean_dec(v_traceState_1179_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1207_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1196_ = lean_unsigned_to_nat(32u);
v___x_1197_ = lean_mk_empty_array_with_capacity(v___x_1196_);
lean_dec_ref(v___x_1197_);
v___x_1198_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1198_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1198_);
lean_ctor_set_uint64(v_reuseFailAlloc_1206_, sizeof(void*)*1, v_tid_1192_);
v___x_1200_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 4, v___x_1200_);
v___x_1202_ = v___x_1190_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_env_1180_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_nextMacroScope_1181_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_ngen_1182_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_auxDeclNGen_1183_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1205_, 5, v_cache_1184_);
lean_ctor_set(v_reuseFailAlloc_1205_, 6, v_recordedDeps_1185_);
lean_ctor_set(v_reuseFailAlloc_1205_, 7, v_messages_1186_);
lean_ctor_set(v_reuseFailAlloc_1205_, 8, v_infoState_1187_);
lean_ctor_set(v_reuseFailAlloc_1205_, 9, v_snapshotTasks_1188_);
v___x_1202_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_st_ref_put(v___y_1173_, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v_traces_1177_);
return v___x_1204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg___boxed(lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1210_);
lean_dec(v___y_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
return v_res_1240_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1));
v___x_1245_ = l_Lean_MessageData_ofFormat(v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_x_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed(lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v_x_1262_);
return v_res_1276_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1281_ = l_Lean_MessageData_ofFormat(v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v_x_1298_);
return v_res_1312_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1317_ = l_Lean_MessageData_ofFormat(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v_x_1334_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_bvExpr_1349_, lean_object* v_x_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v___f_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_ref_1365_; lean_object* v___x_1366_; 
v_ref_1365_ = lean_ctor_get(v___y_1362_, 2);
v___x_1366_ = l_IO_lazyPure___redArg(v___f_1352_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1386_; 
v_a_1375_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1377_ = v___x_1366_;
v_isShared_1378_ = v_isSharedCheck_1386_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1366_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1386_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1379_ = lean_io_error_to_string(v_a_1375_);
v___x_1380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
v___x_1381_ = l_Lean_MessageData_ofFormat(v___x_1380_);
lean_inc(v_ref_1365_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_ref_1365_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1382_);
v___x_1384_ = v___x_1377_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v___f_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v_x_1401_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_x_1401_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v_x_1401_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v_x_1401_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 1);
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v_x_1401_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1401_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v_x_1401_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v_x_1401_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 0);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg___boxed(lean_object* v_x_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(lean_object* v_e_1422_){
_start:
{
if (lean_obj_tag(v_e_1422_) == 0)
{
uint8_t v___x_1423_; 
v___x_1423_ = 2;
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = 0;
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19___boxed(lean_object* v_e_1425_){
_start:
{
uint8_t v_res_1426_; lean_object* v_r_1427_; 
v_res_1426_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_e_1425_);
lean_dec_ref(v_e_1425_);
v_r_1427_ = lean_box(v_res_1426_);
return v_r_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(lean_object* v_oldTraces_1428_, lean_object* v_data_1429_, lean_object* v_ref_1430_, lean_object* v_msg_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_toCold_1437_; lean_object* v_currRecDepth_1438_; lean_object* v_ref_1439_; uint16_t v_optionFlags_1440_; uint8_t v_suppressElabErrors_1441_; uint8_t v_checkDeprecated_1442_; uint8_t v_isRecordingDeps_1443_; lean_object* v_ref_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_traceState_1447_; lean_object* v_traces_1448_; lean_object* v___x_1449_; size_t v_sz_1450_; size_t v___x_1451_; lean_object* v___x_1452_; lean_object* v_msg_1453_; lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1493_; 
v_toCold_1437_ = lean_ctor_get(v___y_1434_, 0);
v_currRecDepth_1438_ = lean_ctor_get(v___y_1434_, 1);
v_ref_1439_ = lean_ctor_get(v___y_1434_, 2);
v_optionFlags_1440_ = lean_ctor_get_uint16(v___y_1434_, sizeof(void*)*3);
v_suppressElabErrors_1441_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 2);
v_checkDeprecated_1442_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1443_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*3 + 4);
v_ref_1444_ = l_Lean_replaceRef(v_ref_1430_, v_ref_1439_);
lean_inc(v_currRecDepth_1438_);
lean_inc_ref(v_toCold_1437_);
v___x_1445_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1445_, 0, v_toCold_1437_);
lean_ctor_set(v___x_1445_, 1, v_currRecDepth_1438_);
lean_ctor_set(v___x_1445_, 2, v_ref_1444_);
lean_ctor_set_uint16(v___x_1445_, sizeof(void*)*3, v_optionFlags_1440_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*3 + 2, v_suppressElabErrors_1441_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*3 + 3, v_checkDeprecated_1442_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*3 + 4, v_isRecordingDeps_1443_);
v___x_1446_ = lean_st_ref_get(v___y_1435_);
v_traceState_1447_ = lean_ctor_get(v___x_1446_, 4);
lean_inc_ref(v_traceState_1447_);
lean_dec(v___x_1446_);
v_traces_1448_ = lean_ctor_get(v_traceState_1447_, 0);
lean_inc_ref(v_traces_1448_);
lean_dec_ref(v_traceState_1447_);
v___x_1449_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1448_);
lean_dec_ref(v_traces_1448_);
v_sz_1450_ = lean_array_size(v___x_1449_);
v___x_1451_ = ((size_t)0ULL);
v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_1450_, v___x_1451_, v___x_1449_);
v_msg_1453_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1453_, 0, v_data_1429_);
lean_ctor_set(v_msg_1453_, 1, v_msg_1431_);
lean_ctor_set(v_msg_1453_, 2, v___x_1452_);
v___x_1454_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_1453_, v___y_1432_, v___y_1433_, v___x_1445_, v___y_1435_);
lean_dec_ref_known(v___x_1445_, 3);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1493_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1493_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v_traceState_1460_; lean_object* v_env_1461_; lean_object* v_nextMacroScope_1462_; lean_object* v_ngen_1463_; lean_object* v_auxDeclNGen_1464_; lean_object* v_cache_1465_; lean_object* v_recordedDeps_1466_; lean_object* v_messages_1467_; lean_object* v_infoState_1468_; lean_object* v_snapshotTasks_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1492_; 
v___x_1459_ = lean_st_ref_take(v___y_1435_);
v_traceState_1460_ = lean_ctor_get(v___x_1459_, 4);
v_env_1461_ = lean_ctor_get(v___x_1459_, 0);
v_nextMacroScope_1462_ = lean_ctor_get(v___x_1459_, 1);
v_ngen_1463_ = lean_ctor_get(v___x_1459_, 2);
v_auxDeclNGen_1464_ = lean_ctor_get(v___x_1459_, 3);
v_cache_1465_ = lean_ctor_get(v___x_1459_, 5);
v_recordedDeps_1466_ = lean_ctor_get(v___x_1459_, 6);
v_messages_1467_ = lean_ctor_get(v___x_1459_, 7);
v_infoState_1468_ = lean_ctor_get(v___x_1459_, 8);
v_snapshotTasks_1469_ = lean_ctor_get(v___x_1459_, 9);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1471_ = v___x_1459_;
v_isShared_1472_ = v_isSharedCheck_1492_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_snapshotTasks_1469_);
lean_inc(v_infoState_1468_);
lean_inc(v_messages_1467_);
lean_inc(v_recordedDeps_1466_);
lean_inc(v_cache_1465_);
lean_inc(v_traceState_1460_);
lean_inc(v_auxDeclNGen_1464_);
lean_inc(v_ngen_1463_);
lean_inc(v_nextMacroScope_1462_);
lean_inc(v_env_1461_);
lean_dec(v___x_1459_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1492_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
uint64_t v_tid_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1490_; 
v_tid_1473_ = lean_ctor_get_uint64(v_traceState_1460_, sizeof(void*)*1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_traceState_1460_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; 
v_unused_1491_ = lean_ctor_get(v_traceState_1460_, 0);
lean_dec(v_unused_1491_);
v___x_1475_ = v_traceState_1460_;
v_isShared_1476_ = v_isSharedCheck_1490_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v_traceState_1460_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1490_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_ref_1430_);
lean_ctor_set(v___x_1478_, 1, v_a_1455_);
v___x_1479_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1428_, v___x_1478_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1479_);
v___x_1481_ = v___x_1475_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1479_);
lean_ctor_set_uint64(v_reuseFailAlloc_1489_, sizeof(void*)*1, v_tid_1473_);
v___x_1481_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v___x_1481_);
v___x_1483_ = v___x_1471_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_env_1461_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_nextMacroScope_1462_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_ngen_1463_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_auxDeclNGen_1464_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1488_, 5, v_cache_1465_);
lean_ctor_set(v_reuseFailAlloc_1488_, 6, v_recordedDeps_1466_);
lean_ctor_set(v_reuseFailAlloc_1488_, 7, v_messages_1467_);
lean_ctor_set(v_reuseFailAlloc_1488_, 8, v_infoState_1468_);
lean_ctor_set(v_reuseFailAlloc_1488_, 9, v_snapshotTasks_1469_);
v___x_1483_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = lean_st_ref_put(v___y_1435_, v___x_1483_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1477_);
v___x_1486_ = v___x_1457_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1477_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg___boxed(lean_object* v_oldTraces_1494_, lean_object* v_data_1495_, lean_object* v_ref_1496_, lean_object* v_msg_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1494_, v_data_1495_, v_ref_1496_, v_msg_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(lean_object* v_cls_1504_, uint8_t v_collapsed_1505_, lean_object* v_tag_1506_, lean_object* v_opts_1507_, uint8_t v_clsEnabled_1508_, lean_object* v_oldTraces_1509_, lean_object* v_msg_1510_, lean_object* v_resStartStop_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v_data_1530_; lean_object* v_fst_1541_; lean_object* v_snd_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; lean_object* v___y_1546_; lean_object* v_a_1547_; uint8_t v___y_1562_; double v___y_1594_; 
v_fst_1525_ = lean_ctor_get(v_resStartStop_1511_, 0);
lean_inc(v_fst_1525_);
v_snd_1526_ = lean_ctor_get(v_resStartStop_1511_, 1);
lean_inc(v_snd_1526_);
lean_dec_ref(v_resStartStop_1511_);
v_fst_1541_ = lean_ctor_get(v_snd_1526_, 0);
lean_inc(v_fst_1541_);
v_snd_1542_ = lean_ctor_get(v_snd_1526_, 1);
lean_inc(v_snd_1542_);
lean_dec(v_snd_1526_);
v___x_1543_ = l_Lean_trace_profiler;
v___x_1544_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1507_, v___x_1543_);
if (v___x_1544_ == 0)
{
v___y_1562_ = v___x_1544_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1599_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1600_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1507_, v___x_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; double v___x_1603_; double v___x_1604_; double v___x_1605_; 
v___x_1601_ = l_Lean_trace_profiler_threshold;
v___x_1602_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1507_, v___x_1601_);
v___x_1603_ = lean_float_of_nat(v___x_1602_);
v___x_1604_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_1605_ = lean_float_div(v___x_1603_, v___x_1604_);
v___y_1594_ = v___x_1605_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; double v___x_1608_; 
v___x_1606_ = l_Lean_trace_profiler_threshold;
v___x_1607_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1507_, v___x_1606_);
v___x_1608_ = lean_float_of_nat(v___x_1607_);
v___y_1594_ = v___x_1608_;
goto v___jp_1593_;
}
}
v___jp_1527_:
{
lean_object* v___x_1531_; 
lean_inc(v___y_1528_);
v___x_1531_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1509_, v_data_1530_, v___y_1528_, v___y_1529_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; 
lean_dec_ref_known(v___x_1531_, 1);
v___x_1532_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_1525_);
return v___x_1532_;
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_fst_1525_);
v_a_1533_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1531_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1531_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
v___jp_1545_:
{
uint8_t v_result_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; double v___x_1551_; lean_object* v_data_1552_; 
v_result_1548_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_fst_1525_);
v___x_1549_ = lean_box(v_result_1548_);
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
v___x_1551_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_1506_);
lean_inc_ref(v___x_1550_);
lean_inc(v_cls_1504_);
v_data_1552_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1552_, 0, v_cls_1504_);
lean_ctor_set(v_data_1552_, 1, v___x_1550_);
lean_ctor_set(v_data_1552_, 2, v_tag_1506_);
lean_ctor_set_float(v_data_1552_, sizeof(void*)*3, v___x_1551_);
lean_ctor_set_float(v_data_1552_, sizeof(void*)*3 + 8, v___x_1551_);
lean_ctor_set_uint8(v_data_1552_, sizeof(void*)*3 + 16, v_collapsed_1505_);
if (v___x_1544_ == 0)
{
lean_dec_ref_known(v___x_1550_, 1);
lean_dec(v_snd_1542_);
lean_dec(v_fst_1541_);
lean_dec_ref(v_tag_1506_);
lean_dec(v_cls_1504_);
v___y_1528_ = v___y_1546_;
v___y_1529_ = v_a_1547_;
v_data_1530_ = v_data_1552_;
goto v___jp_1527_;
}
else
{
lean_object* v_data_1553_; double v___x_1554_; double v___x_1555_; 
lean_dec_ref_known(v_data_1552_, 3);
v_data_1553_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1553_, 0, v_cls_1504_);
lean_ctor_set(v_data_1553_, 1, v___x_1550_);
lean_ctor_set(v_data_1553_, 2, v_tag_1506_);
v___x_1554_ = lean_unbox_float(v_fst_1541_);
lean_dec(v_fst_1541_);
lean_ctor_set_float(v_data_1553_, sizeof(void*)*3, v___x_1554_);
v___x_1555_ = lean_unbox_float(v_snd_1542_);
lean_dec(v_snd_1542_);
lean_ctor_set_float(v_data_1553_, sizeof(void*)*3 + 8, v___x_1555_);
lean_ctor_set_uint8(v_data_1553_, sizeof(void*)*3 + 16, v_collapsed_1505_);
v___y_1528_ = v___y_1546_;
v___y_1529_ = v_a_1547_;
v_data_1530_ = v_data_1553_;
goto v___jp_1527_;
}
}
v___jp_1556_:
{
lean_object* v_ref_1557_; lean_object* v___x_1558_; 
v_ref_1557_ = lean_ctor_get(v___y_1522_, 2);
lean_inc(v___y_1523_);
lean_inc_ref(v___y_1522_);
lean_inc(v___y_1521_);
lean_inc_ref(v___y_1520_);
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc_ref(v___y_1513_);
lean_inc(v___y_1512_);
lean_inc(v_fst_1525_);
v___x_1558_ = lean_apply_14(v_msg_1510_, v_fst_1525_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, lean_box(0));
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___y_1546_ = v_ref_1557_;
v_a_1547_ = v_a_1559_;
goto v___jp_1545_;
}
else
{
lean_object* v___x_1560_; 
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_1546_ = v_ref_1557_;
v_a_1547_ = v___x_1560_;
goto v___jp_1545_;
}
}
v___jp_1561_:
{
if (v_clsEnabled_1508_ == 0)
{
if (v___y_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v_traceState_1564_; lean_object* v_env_1565_; lean_object* v_nextMacroScope_1566_; lean_object* v_ngen_1567_; lean_object* v_auxDeclNGen_1568_; lean_object* v_cache_1569_; lean_object* v_recordedDeps_1570_; lean_object* v_messages_1571_; lean_object* v_infoState_1572_; lean_object* v_snapshotTasks_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_snd_1542_);
lean_dec(v_fst_1541_);
lean_dec_ref(v_msg_1510_);
lean_dec_ref(v_tag_1506_);
lean_dec(v_cls_1504_);
v___x_1563_ = lean_st_ref_take(v___y_1523_);
v_traceState_1564_ = lean_ctor_get(v___x_1563_, 4);
v_env_1565_ = lean_ctor_get(v___x_1563_, 0);
v_nextMacroScope_1566_ = lean_ctor_get(v___x_1563_, 1);
v_ngen_1567_ = lean_ctor_get(v___x_1563_, 2);
v_auxDeclNGen_1568_ = lean_ctor_get(v___x_1563_, 3);
v_cache_1569_ = lean_ctor_get(v___x_1563_, 5);
v_recordedDeps_1570_ = lean_ctor_get(v___x_1563_, 6);
v_messages_1571_ = lean_ctor_get(v___x_1563_, 7);
v_infoState_1572_ = lean_ctor_get(v___x_1563_, 8);
v_snapshotTasks_1573_ = lean_ctor_get(v___x_1563_, 9);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1575_ = v___x_1563_;
v_isShared_1576_ = v_isSharedCheck_1592_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_snapshotTasks_1573_);
lean_inc(v_infoState_1572_);
lean_inc(v_messages_1571_);
lean_inc(v_recordedDeps_1570_);
lean_inc(v_cache_1569_);
lean_inc(v_traceState_1564_);
lean_inc(v_auxDeclNGen_1568_);
lean_inc(v_ngen_1567_);
lean_inc(v_nextMacroScope_1566_);
lean_inc(v_env_1565_);
lean_dec(v___x_1563_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1592_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
uint64_t v_tid_1577_; lean_object* v_traces_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1591_; 
v_tid_1577_ = lean_ctor_get_uint64(v_traceState_1564_, sizeof(void*)*1);
v_traces_1578_ = lean_ctor_get(v_traceState_1564_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_traceState_1564_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1580_ = v_traceState_1564_;
v_isShared_1581_ = v_isSharedCheck_1591_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_traces_1578_);
lean_dec(v_traceState_1564_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1591_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1509_, v_traces_1578_);
lean_dec_ref(v_traces_1578_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1582_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1582_);
lean_ctor_set_uint64(v_reuseFailAlloc_1590_, sizeof(void*)*1, v_tid_1577_);
v___x_1584_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 4, v___x_1584_);
v___x_1586_ = v___x_1575_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_env_1565_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_nextMacroScope_1566_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_ngen_1567_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_auxDeclNGen_1568_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1589_, 5, v_cache_1569_);
lean_ctor_set(v_reuseFailAlloc_1589_, 6, v_recordedDeps_1570_);
lean_ctor_set(v_reuseFailAlloc_1589_, 7, v_messages_1571_);
lean_ctor_set(v_reuseFailAlloc_1589_, 8, v_infoState_1572_);
lean_ctor_set(v_reuseFailAlloc_1589_, 9, v_snapshotTasks_1573_);
v___x_1586_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_st_ref_put(v___y_1523_, v___x_1586_);
v___x_1588_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_1525_);
return v___x_1588_;
}
}
}
}
}
else
{
goto v___jp_1556_;
}
}
else
{
goto v___jp_1556_;
}
}
v___jp_1593_:
{
double v___x_1595_; double v___x_1596_; double v___x_1597_; uint8_t v___x_1598_; 
v___x_1595_ = lean_unbox_float(v_snd_1542_);
v___x_1596_ = lean_unbox_float(v_fst_1541_);
v___x_1597_ = lean_float_sub(v___x_1595_, v___x_1596_);
v___x_1598_ = lean_float_decLt(v___y_1594_, v___x_1597_);
v___y_1562_ = v___x_1598_;
goto v___jp_1561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8___boxed(lean_object** _args){
lean_object* v_cls_1609_ = _args[0];
lean_object* v_collapsed_1610_ = _args[1];
lean_object* v_tag_1611_ = _args[2];
lean_object* v_opts_1612_ = _args[3];
lean_object* v_clsEnabled_1613_ = _args[4];
lean_object* v_oldTraces_1614_ = _args[5];
lean_object* v_msg_1615_ = _args[6];
lean_object* v_resStartStop_1616_ = _args[7];
lean_object* v___y_1617_ = _args[8];
lean_object* v___y_1618_ = _args[9];
lean_object* v___y_1619_ = _args[10];
lean_object* v___y_1620_ = _args[11];
lean_object* v___y_1621_ = _args[12];
lean_object* v___y_1622_ = _args[13];
lean_object* v___y_1623_ = _args[14];
lean_object* v___y_1624_ = _args[15];
lean_object* v___y_1625_ = _args[16];
lean_object* v___y_1626_ = _args[17];
lean_object* v___y_1627_ = _args[18];
lean_object* v___y_1628_ = _args[19];
lean_object* v___y_1629_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_1630_; uint8_t v_clsEnabled_boxed_1631_; lean_object* v_res_1632_; 
v_collapsed_boxed_1630_ = lean_unbox(v_collapsed_1610_);
v_clsEnabled_boxed_1631_ = lean_unbox(v_clsEnabled_1613_);
v_res_1632_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1609_, v_collapsed_boxed_1630_, v_tag_1611_, v_opts_1612_, v_clsEnabled_boxed_1631_, v_oldTraces_1614_, v_msg_1615_, v_resStartStop_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v_opts_1612_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(lean_object* v___f_1633_, lean_object* v_cls_1634_, uint8_t v___x_1635_, lean_object* v___x_1636_, lean_object* v___f_1637_, lean_object* v___f_1638_, lean_object* v_opts_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___y_1654_; lean_object* v___y_1655_; uint8_t v___y_1656_; lean_object* v_a_1657_; lean_object* v___y_1667_; uint8_t v___y_1668_; lean_object* v___y_1669_; lean_object* v_a_1670_; uint8_t v_hasTrace_1682_; 
v_hasTrace_1682_ = lean_ctor_get_uint8(v_opts_1639_, sizeof(void*)*1);
if (v_hasTrace_1682_ == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref(v___f_1638_);
lean_dec_ref(v___f_1637_);
lean_dec_ref(v___x_1636_);
lean_dec(v_cls_1634_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
lean_inc(v___y_1649_);
lean_inc_ref(v___y_1648_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
v___x_1683_ = lean_apply_12(v___f_1633_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, lean_box(0));
return v___x_1683_;
}
else
{
lean_object* v_toCold_1684_; lean_object* v_ref_1685_; uint8_t v___y_1687_; uint8_t v_a_1745_; lean_object* v_options_1749_; uint8_t v_hasTrace_1750_; 
v_toCold_1684_ = lean_ctor_get(v___y_1650_, 0);
v_ref_1685_ = lean_ctor_get(v___y_1650_, 2);
v_options_1749_ = lean_ctor_get(v_toCold_1684_, 2);
v_hasTrace_1750_ = lean_ctor_get_uint8(v_options_1749_, sizeof(void*)*1);
if (v_hasTrace_1750_ == 0)
{
v_a_1745_ = v_hasTrace_1750_;
goto v___jp_1744_;
}
else
{
lean_object* v_inheritedTraceOptions_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_inheritedTraceOptions_1751_ = lean_ctor_get(v_toCold_1684_, 11);
v___x_1752_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v_cls_1634_);
v___x_1753_ = l_Lean_Name_append(v___x_1752_, v_cls_1634_);
v___x_1754_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1751_, v_options_1749_, v___x_1753_);
lean_dec(v___x_1753_);
if (v___x_1754_ == 0)
{
v_a_1745_ = v___x_1754_;
goto v___jp_1744_;
}
else
{
lean_dec_ref(v___f_1633_);
v___y_1687_ = v___x_1754_;
goto v___jp_1686_;
}
}
v___jp_1686_:
{
lean_object* v___x_1688_; lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1743_; 
v___x_1688_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1651_);
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1743_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1743_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1694_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1639_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_io_mono_nanos_now();
v___x_1696_ = l_IO_lazyPure___redArg(v___f_1638_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_del_object(v___x_1691_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set_tag(v___x_1699_, 1);
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
v___y_1667_ = v_a_1689_;
v___y_1668_ = v___y_1687_;
v___y_1669_ = v___x_1695_;
v_a_1670_ = v___x_1702_;
goto v___jp_1666_;
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1718_; 
v_a_1705_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1707_ = v___x_1696_;
v_isShared_1708_ = v_isSharedCheck_1718_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1696_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1718_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_io_error_to_string(v_a_1705_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 3);
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1712_ = l_Lean_MessageData_ofFormat(v___x_1711_);
lean_inc(v_ref_1685_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_ref_1685_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1713_);
v___x_1715_ = v___x_1691_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
v___y_1667_ = v_a_1689_;
v___y_1668_ = v___y_1687_;
v___y_1669_ = v___x_1695_;
v_a_1670_ = v___x_1715_;
goto v___jp_1666_;
}
}
}
}
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_io_get_num_heartbeats();
v___x_1720_ = l_IO_lazyPure___redArg(v___f_1638_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_del_object(v___x_1691_);
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 1);
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
v___y_1654_ = v_a_1689_;
v___y_1655_ = v___x_1719_;
v___y_1656_ = v___y_1687_;
v_a_1657_ = v___x_1726_;
goto v___jp_1653_;
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1742_; 
v_a_1729_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1731_ = v___x_1720_;
v_isShared_1732_ = v_isSharedCheck_1742_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1720_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1742_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_io_error_to_string(v_a_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set_tag(v___x_1731_, 3);
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1736_ = l_Lean_MessageData_ofFormat(v___x_1735_);
lean_inc(v_ref_1685_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_ref_1685_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1737_);
v___x_1739_ = v___x_1691_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
v___y_1654_ = v_a_1689_;
v___y_1655_ = v___x_1719_;
v___y_1656_ = v___y_1687_;
v_a_1657_ = v___x_1739_;
goto v___jp_1653_;
}
}
}
}
}
}
}
v___jp_1744_:
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = l_Lean_trace_profiler;
v___x_1747_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1639_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_dec_ref(v___f_1638_);
lean_dec_ref(v___f_1637_);
lean_dec_ref(v___x_1636_);
lean_dec(v_cls_1634_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
lean_inc(v___y_1649_);
lean_inc_ref(v___y_1648_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
v___x_1748_ = lean_apply_12(v___f_1633_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, lean_box(0));
return v___x_1748_;
}
else
{
lean_dec_ref(v___f_1633_);
v___y_1687_ = v_a_1745_;
goto v___jp_1686_;
}
}
}
v___jp_1653_:
{
lean_object* v___x_1658_; double v___x_1659_; double v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1658_ = lean_io_get_num_heartbeats();
v___x_1659_ = lean_float_of_nat(v___y_1655_);
v___x_1660_ = lean_float_of_nat(v___x_1658_);
v___x_1661_ = lean_box_float(v___x_1659_);
v___x_1662_ = lean_box_float(v___x_1660_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_a_1657_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1634_, v___x_1635_, v___x_1636_, v_opts_1639_, v___y_1656_, v___y_1654_, v___f_1637_, v___x_1664_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
return v___x_1665_;
}
v___jp_1666_:
{
lean_object* v___x_1671_; double v___x_1672_; double v___x_1673_; double v___x_1674_; double v___x_1675_; double v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1671_ = lean_io_mono_nanos_now();
v___x_1672_ = lean_float_of_nat(v___y_1669_);
v___x_1673_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1674_ = lean_float_div(v___x_1672_, v___x_1673_);
v___x_1675_ = lean_float_of_nat(v___x_1671_);
v___x_1676_ = lean_float_div(v___x_1675_, v___x_1673_);
v___x_1677_ = lean_box_float(v___x_1674_);
v___x_1678_ = lean_box_float(v___x_1676_);
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v_a_1670_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1634_, v___x_1635_, v___x_1636_, v_opts_1639_, v___y_1668_, v___y_1667_, v___f_1637_, v___x_1680_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5___boxed(lean_object** _args){
lean_object* v___f_1755_ = _args[0];
lean_object* v_cls_1756_ = _args[1];
lean_object* v___x_1757_ = _args[2];
lean_object* v___x_1758_ = _args[3];
lean_object* v___f_1759_ = _args[4];
lean_object* v___f_1760_ = _args[5];
lean_object* v_opts_1761_ = _args[6];
lean_object* v___y_1762_ = _args[7];
lean_object* v___y_1763_ = _args[8];
lean_object* v___y_1764_ = _args[9];
lean_object* v___y_1765_ = _args[10];
lean_object* v___y_1766_ = _args[11];
lean_object* v___y_1767_ = _args[12];
lean_object* v___y_1768_ = _args[13];
lean_object* v___y_1769_ = _args[14];
lean_object* v___y_1770_ = _args[15];
lean_object* v___y_1771_ = _args[16];
lean_object* v___y_1772_ = _args[17];
lean_object* v___y_1773_ = _args[18];
lean_object* v___y_1774_ = _args[19];
_start:
{
uint8_t v___x_653001__boxed_1775_; lean_object* v_res_1776_; 
v___x_653001__boxed_1775_ = lean_unbox(v___x_1757_);
v_res_1776_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_1755_, v_cls_1756_, v___x_653001__boxed_1775_, v___x_1758_, v___f_1759_, v___f_1760_, v_opts_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v_opts_1761_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1777_){
_start:
{
lean_object* v_decls_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_decls_1778_ = lean_ctor_get(v_aig_1777_, 0);
v___x_1779_ = lean_array_get_size(v_decls_1778_);
v___x_1780_ = 0;
v___x_1781_ = lean_box(v___x_1780_);
v___x_1782_ = lean_mk_array(v___x_1779_, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___boxed(lean_object* v_aig_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1783_);
lean_dec_ref(v_aig_1783_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_aig_1787_){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0));
v___x_1789_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1787_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object* v_aig_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1791_);
lean_dec_ref(v_aig_1791_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_aig_1795_, lean_object* v___x_1796_, lean_object* v_entry_1797_, lean_object* v_ref_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v_state_1802_; lean_object* v_cnf_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1823_; 
v___x_1800_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1801_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1795_);
v_state_1802_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1796_, v___x_1800_, v_entry_1797_, v___x_1801_);
lean_dec_ref(v___x_1800_);
v_cnf_1803_ = lean_ctor_get(v_state_1802_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_state_1802_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_state_1802_, 1);
lean_dec(v_unused_1824_);
v___x_1805_ = v_state_1802_;
v_isShared_1806_ = v_isSharedCheck_1823_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_cnf_1803_);
lean_dec(v_state_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1823_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_gate_1807_; uint8_t v_invert_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___y_1812_; uint8_t v___y_1813_; 
v_gate_1807_ = lean_ctor_get(v_ref_1798_, 0);
lean_inc(v_gate_1807_);
v_invert_1808_ = lean_ctor_get_uint8(v_ref_1798_, sizeof(void*)*1);
lean_dec_ref(v_ref_1798_);
v___x_1809_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1810_ = l_ByteArray_empty;
if (v_invert_1808_ == 0)
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = lean_array_push(v___x_1809_, v_gate_1807_);
v___x_1820_ = 1;
v___y_1812_ = v___x_1819_;
v___y_1813_ = v___x_1820_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = lean_array_push(v___x_1809_, v_gate_1807_);
v___x_1822_ = 0;
v___y_1812_ = v___x_1821_;
v___y_1813_ = v___x_1822_;
goto v___jp_1811_;
}
v___jp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_byte_array_push(v___x_1810_, v___y_1813_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1814_);
lean_ctor_set(v___x_1805_, 0, v___y_1812_);
v___x_1816_ = v___x_1805_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___y_1812_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_array_push(v_cnf_1803_, v___x_1816_);
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object* v_aig_1825_, lean_object* v___x_1826_, lean_object* v_entry_1827_, lean_object* v_ref_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_aig_1825_, v___x_1826_, v_entry_1827_, v_ref_1828_, v_x_1829_);
lean_dec_ref(v___x_1826_);
lean_dec_ref(v_aig_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v___f_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_ref_1844_; lean_object* v___x_1845_; 
v_ref_1844_ = lean_ctor_get(v___y_1841_, 2);
v___x_1845_ = l_IO_lazyPure___redArg(v___f_1831_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1865_; 
v_a_1854_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1856_ = v___x_1845_;
v_isShared_1857_ = v_isSharedCheck_1865_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1845_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1865_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1858_ = lean_io_error_to_string(v_a_1854_);
v___x_1859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
v___x_1860_ = l_Lean_MessageData_ofFormat(v___x_1859_);
lean_inc(v_ref_1844_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v_ref_1844_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1861_);
v___x_1863_ = v___x_1856_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object* v___f_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v___f_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1879_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__1));
v___x_1884_ = l_Lean_MessageData_ofFormat(v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___boxed(lean_object* v_x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(v_x_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v_x_1901_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_aig_1916_, lean_object* v___x_1917_, lean_object* v_a_1918_, lean_object* v_ref_1919_, lean_object* v_x_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_state_1923_; lean_object* v_cnf_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1944_; 
v___x_1921_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1922_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1916_);
v_state_1923_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1917_, v___x_1921_, v_a_1918_, v___x_1922_);
lean_dec_ref(v___x_1921_);
v_cnf_1924_ = lean_ctor_get(v_state_1923_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_state_1923_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v_state_1923_, 1);
lean_dec(v_unused_1945_);
v___x_1926_ = v_state_1923_;
v_isShared_1927_ = v_isSharedCheck_1944_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_cnf_1924_);
lean_dec(v_state_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1944_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v_gate_1928_; uint8_t v_invert_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___y_1933_; uint8_t v___y_1934_; 
v_gate_1928_ = lean_ctor_get(v_ref_1919_, 0);
lean_inc(v_gate_1928_);
v_invert_1929_ = lean_ctor_get_uint8(v_ref_1919_, sizeof(void*)*1);
lean_dec_ref(v_ref_1919_);
v___x_1930_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1931_ = l_ByteArray_empty;
if (v_invert_1929_ == 0)
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = lean_array_push(v___x_1930_, v_gate_1928_);
v___x_1941_ = 1;
v___y_1933_ = v___x_1940_;
v___y_1934_ = v___x_1941_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = lean_array_push(v___x_1930_, v_gate_1928_);
v___x_1943_ = 0;
v___y_1933_ = v___x_1942_;
v___y_1934_ = v___x_1943_;
goto v___jp_1932_;
}
v___jp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_byte_array_push(v___x_1931_, v___y_1934_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 1, v___x_1935_);
lean_ctor_set(v___x_1926_, 0, v___y_1933_);
v___x_1937_ = v___x_1926_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___y_1933_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_array_push(v_cnf_1924_, v___x_1937_);
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_aig_1946_, lean_object* v___x_1947_, lean_object* v_a_1948_, lean_object* v_ref_1949_, lean_object* v_x_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_aig_1946_, v___x_1947_, v_a_1948_, v_ref_1949_, v_x_1950_);
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_aig_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(lean_object* v_as_1952_, size_t v_i_1953_, size_t v_stop_1954_, lean_object* v_b_1955_){
_start:
{
lean_object* v___y_1957_; uint8_t v___x_1961_; 
v___x_1961_ = lean_usize_dec_eq(v_i_1953_, v_stop_1954_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; lean_object* v_snd_1963_; lean_object* v_fst_1964_; uint8_t v___x_1965_; 
v___x_1962_ = lean_array_uget_borrowed(v_as_1952_, v_i_1953_);
v_snd_1963_ = lean_ctor_get(v___x_1962_, 1);
lean_inc(v_snd_1963_);
v_fst_1964_ = lean_ctor_get(v_snd_1963_, 0);
v___x_1965_ = lean_unbox(v_fst_1964_);
if (v___x_1965_ == 0)
{
lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1975_; 
v_fst_1966_ = lean_ctor_get(v___x_1962_, 0);
v_snd_1967_ = lean_ctor_get(v_snd_1963_, 1);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_snd_1963_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v_snd_1963_, 0);
lean_dec(v_unused_1976_);
v___x_1969_ = v_snd_1963_;
v_isShared_1970_ = v_isSharedCheck_1975_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_snd_1967_);
lean_dec(v_snd_1963_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1975_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
lean_inc(v_fst_1966_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v_fst_1966_);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_fst_1966_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_snd_1967_);
v___x_1972_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_array_push(v_b_1955_, v___x_1972_);
v___y_1957_ = v___x_1973_;
goto v___jp_1956_;
}
}
}
else
{
lean_dec(v_snd_1963_);
v___y_1957_ = v_b_1955_;
goto v___jp_1956_;
}
}
else
{
return v_b_1955_;
}
v___jp_1956_:
{
size_t v___x_1958_; size_t v___x_1959_; 
v___x_1958_ = ((size_t)1ULL);
v___x_1959_ = lean_usize_add(v_i_1953_, v___x_1958_);
v_i_1953_ = v___x_1959_;
v_b_1955_ = v___y_1957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2___boxed(lean_object* v_as_1977_, lean_object* v_i_1978_, lean_object* v_stop_1979_, lean_object* v_b_1980_){
_start:
{
size_t v_i_boxed_1981_; size_t v_stop_boxed_1982_; lean_object* v_res_1983_; 
v_i_boxed_1981_ = lean_unbox_usize(v_i_1978_);
lean_dec(v_i_1978_);
v_stop_boxed_1982_ = lean_unbox_usize(v_stop_1979_);
lean_dec(v_stop_1979_);
v_res_1983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1977_, v_i_boxed_1981_, v_stop_boxed_1982_, v_b_1980_);
lean_dec_ref(v_as_1977_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(lean_object* v_as_1986_, lean_object* v_start_1987_, lean_object* v_stop_1988_){
_start:
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___closed__0));
v___x_1990_ = lean_nat_dec_lt(v_start_1987_, v_stop_1988_);
if (v___x_1990_ == 0)
{
return v___x_1989_;
}
else
{
lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1991_ = lean_array_get_size(v_as_1986_);
v___x_1992_ = lean_nat_dec_le(v_stop_1988_, v___x_1991_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_nat_dec_lt(v_start_1987_, v___x_1991_);
if (v___x_1993_ == 0)
{
return v___x_1989_;
}
else
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_usize_of_nat(v_start_1987_);
v___x_1995_ = lean_usize_of_nat(v___x_1991_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1986_, v___x_1994_, v___x_1995_, v___x_1989_);
return v___x_1996_;
}
}
else
{
size_t v___x_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = lean_usize_of_nat(v_start_1987_);
v___x_1998_ = lean_usize_of_nat(v_stop_1988_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1_spec__2(v_as_1986_, v___x_1997_, v___x_1998_, v___x_1989_);
return v___x_1999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1___boxed(lean_object* v_as_2000_, lean_object* v_start_2001_, lean_object* v_stop_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v_as_2000_, v_start_2001_, v_stop_2002_);
lean_dec(v_stop_2002_);
lean_dec(v_start_2001_);
lean_dec_ref(v_as_2000_);
return v_res_2003_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(lean_object* v_e_2004_){
_start:
{
if (lean_obj_tag(v_e_2004_) == 0)
{
uint8_t v___x_2005_; 
v___x_2005_ = 2;
return v___x_2005_;
}
else
{
uint8_t v___x_2006_; 
v___x_2006_ = 0;
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12___boxed(lean_object* v_e_2007_){
_start:
{
uint8_t v_res_2008_; lean_object* v_r_2009_; 
v_res_2008_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_e_2007_);
lean_dec_ref(v_e_2007_);
v_r_2009_ = lean_box(v_res_2008_);
return v_r_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(lean_object* v_cls_2010_, uint8_t v_collapsed_2011_, lean_object* v_tag_2012_, lean_object* v_opts_2013_, uint8_t v_clsEnabled_2014_, lean_object* v_oldTraces_2015_, lean_object* v_msg_2016_, lean_object* v_resStartStop_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v_data_2036_; lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; lean_object* v___y_2052_; lean_object* v_a_2053_; uint8_t v___y_2068_; double v___y_2100_; 
v_fst_2031_ = lean_ctor_get(v_resStartStop_2017_, 0);
lean_inc(v_fst_2031_);
v_snd_2032_ = lean_ctor_get(v_resStartStop_2017_, 1);
lean_inc(v_snd_2032_);
lean_dec_ref(v_resStartStop_2017_);
v_fst_2047_ = lean_ctor_get(v_snd_2032_, 0);
lean_inc(v_fst_2047_);
v_snd_2048_ = lean_ctor_get(v_snd_2032_, 1);
lean_inc(v_snd_2048_);
lean_dec(v_snd_2032_);
v___x_2049_ = l_Lean_trace_profiler;
v___x_2050_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2013_, v___x_2049_);
if (v___x_2050_ == 0)
{
v___y_2068_ = v___x_2050_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2106_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2013_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; double v___x_2109_; double v___x_2110_; double v___x_2111_; 
v___x_2107_ = l_Lean_trace_profiler_threshold;
v___x_2108_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2013_, v___x_2107_);
v___x_2109_ = lean_float_of_nat(v___x_2108_);
v___x_2110_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2111_ = lean_float_div(v___x_2109_, v___x_2110_);
v___y_2100_ = v___x_2111_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; double v___x_2114_; 
v___x_2112_ = l_Lean_trace_profiler_threshold;
v___x_2113_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2013_, v___x_2112_);
v___x_2114_ = lean_float_of_nat(v___x_2113_);
v___y_2100_ = v___x_2114_;
goto v___jp_2099_;
}
}
v___jp_2033_:
{
lean_object* v___x_2037_; 
lean_inc(v___y_2035_);
v___x_2037_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2015_, v_data_2036_, v___y_2035_, v___y_2034_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v___x_2038_; 
lean_dec_ref_known(v___x_2037_, 1);
v___x_2038_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2031_);
return v___x_2038_;
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_fst_2031_);
v_a_2039_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2037_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2037_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
v___jp_2051_:
{
uint8_t v_result_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; double v___x_2057_; lean_object* v_data_2058_; 
v_result_2054_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6_spec__12(v_fst_2031_);
v___x_2055_ = lean_box(v_result_2054_);
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
v___x_2057_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2012_);
lean_inc_ref(v___x_2056_);
lean_inc(v_cls_2010_);
v_data_2058_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2058_, 0, v_cls_2010_);
lean_ctor_set(v_data_2058_, 1, v___x_2056_);
lean_ctor_set(v_data_2058_, 2, v_tag_2012_);
lean_ctor_set_float(v_data_2058_, sizeof(void*)*3, v___x_2057_);
lean_ctor_set_float(v_data_2058_, sizeof(void*)*3 + 8, v___x_2057_);
lean_ctor_set_uint8(v_data_2058_, sizeof(void*)*3 + 16, v_collapsed_2011_);
if (v___x_2050_ == 0)
{
lean_dec_ref_known(v___x_2056_, 1);
lean_dec(v_snd_2048_);
lean_dec(v_fst_2047_);
lean_dec_ref(v_tag_2012_);
lean_dec(v_cls_2010_);
v___y_2034_ = v_a_2053_;
v___y_2035_ = v___y_2052_;
v_data_2036_ = v_data_2058_;
goto v___jp_2033_;
}
else
{
lean_object* v_data_2059_; double v___x_2060_; double v___x_2061_; 
lean_dec_ref_known(v_data_2058_, 3);
v_data_2059_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2059_, 0, v_cls_2010_);
lean_ctor_set(v_data_2059_, 1, v___x_2056_);
lean_ctor_set(v_data_2059_, 2, v_tag_2012_);
v___x_2060_ = lean_unbox_float(v_fst_2047_);
lean_dec(v_fst_2047_);
lean_ctor_set_float(v_data_2059_, sizeof(void*)*3, v___x_2060_);
v___x_2061_ = lean_unbox_float(v_snd_2048_);
lean_dec(v_snd_2048_);
lean_ctor_set_float(v_data_2059_, sizeof(void*)*3 + 8, v___x_2061_);
lean_ctor_set_uint8(v_data_2059_, sizeof(void*)*3 + 16, v_collapsed_2011_);
v___y_2034_ = v_a_2053_;
v___y_2035_ = v___y_2052_;
v_data_2036_ = v_data_2059_;
goto v___jp_2033_;
}
}
v___jp_2062_:
{
lean_object* v_ref_2063_; lean_object* v___x_2064_; 
v_ref_2063_ = lean_ctor_get(v___y_2028_, 2);
lean_inc(v___y_2029_);
lean_inc_ref(v___y_2028_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
lean_inc(v___y_2021_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
lean_inc(v___y_2018_);
lean_inc(v_fst_2031_);
v___x_2064_ = lean_apply_14(v_msg_2016_, v_fst_2031_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, lean_box(0));
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___y_2052_ = v_ref_2063_;
v_a_2053_ = v_a_2065_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2066_; 
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2052_ = v_ref_2063_;
v_a_2053_ = v___x_2066_;
goto v___jp_2051_;
}
}
v___jp_2067_:
{
if (v_clsEnabled_2014_ == 0)
{
if (v___y_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v_traceState_2070_; lean_object* v_env_2071_; lean_object* v_nextMacroScope_2072_; lean_object* v_ngen_2073_; lean_object* v_auxDeclNGen_2074_; lean_object* v_cache_2075_; lean_object* v_recordedDeps_2076_; lean_object* v_messages_2077_; lean_object* v_infoState_2078_; lean_object* v_snapshotTasks_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_snd_2048_);
lean_dec(v_fst_2047_);
lean_dec_ref(v_msg_2016_);
lean_dec_ref(v_tag_2012_);
lean_dec(v_cls_2010_);
v___x_2069_ = lean_st_ref_take(v___y_2029_);
v_traceState_2070_ = lean_ctor_get(v___x_2069_, 4);
v_env_2071_ = lean_ctor_get(v___x_2069_, 0);
v_nextMacroScope_2072_ = lean_ctor_get(v___x_2069_, 1);
v_ngen_2073_ = lean_ctor_get(v___x_2069_, 2);
v_auxDeclNGen_2074_ = lean_ctor_get(v___x_2069_, 3);
v_cache_2075_ = lean_ctor_get(v___x_2069_, 5);
v_recordedDeps_2076_ = lean_ctor_get(v___x_2069_, 6);
v_messages_2077_ = lean_ctor_get(v___x_2069_, 7);
v_infoState_2078_ = lean_ctor_get(v___x_2069_, 8);
v_snapshotTasks_2079_ = lean_ctor_get(v___x_2069_, 9);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2081_ = v___x_2069_;
v_isShared_2082_ = v_isSharedCheck_2098_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snapshotTasks_2079_);
lean_inc(v_infoState_2078_);
lean_inc(v_messages_2077_);
lean_inc(v_recordedDeps_2076_);
lean_inc(v_cache_2075_);
lean_inc(v_traceState_2070_);
lean_inc(v_auxDeclNGen_2074_);
lean_inc(v_ngen_2073_);
lean_inc(v_nextMacroScope_2072_);
lean_inc(v_env_2071_);
lean_dec(v___x_2069_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2098_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
uint64_t v_tid_2083_; lean_object* v_traces_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2097_; 
v_tid_2083_ = lean_ctor_get_uint64(v_traceState_2070_, sizeof(void*)*1);
v_traces_2084_ = lean_ctor_get(v_traceState_2070_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_traceState_2070_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2086_ = v_traceState_2070_;
v_isShared_2087_ = v_isSharedCheck_2097_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_traces_2084_);
lean_dec(v_traceState_2070_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2097_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2015_, v_traces_2084_);
lean_dec_ref(v_traces_2084_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2088_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2088_);
lean_ctor_set_uint64(v_reuseFailAlloc_2096_, sizeof(void*)*1, v_tid_2083_);
v___x_2090_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2092_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 4, v___x_2090_);
v___x_2092_ = v___x_2081_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_env_2071_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_nextMacroScope_2072_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_ngen_2073_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_auxDeclNGen_2074_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2095_, 5, v_cache_2075_);
lean_ctor_set(v_reuseFailAlloc_2095_, 6, v_recordedDeps_2076_);
lean_ctor_set(v_reuseFailAlloc_2095_, 7, v_messages_2077_);
lean_ctor_set(v_reuseFailAlloc_2095_, 8, v_infoState_2078_);
lean_ctor_set(v_reuseFailAlloc_2095_, 9, v_snapshotTasks_2079_);
v___x_2092_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_st_ref_put(v___y_2029_, v___x_2092_);
v___x_2094_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2031_);
return v___x_2094_;
}
}
}
}
}
else
{
goto v___jp_2062_;
}
}
else
{
goto v___jp_2062_;
}
}
v___jp_2099_:
{
double v___x_2101_; double v___x_2102_; double v___x_2103_; uint8_t v___x_2104_; 
v___x_2101_ = lean_unbox_float(v_snd_2048_);
v___x_2102_ = lean_unbox_float(v_fst_2047_);
v___x_2103_ = lean_float_sub(v___x_2101_, v___x_2102_);
v___x_2104_ = lean_float_decLt(v___y_2100_, v___x_2103_);
v___y_2068_ = v___x_2104_;
goto v___jp_2067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6___boxed(lean_object** _args){
lean_object* v_cls_2115_ = _args[0];
lean_object* v_collapsed_2116_ = _args[1];
lean_object* v_tag_2117_ = _args[2];
lean_object* v_opts_2118_ = _args[3];
lean_object* v_clsEnabled_2119_ = _args[4];
lean_object* v_oldTraces_2120_ = _args[5];
lean_object* v_msg_2121_ = _args[6];
lean_object* v_resStartStop_2122_ = _args[7];
lean_object* v___y_2123_ = _args[8];
lean_object* v___y_2124_ = _args[9];
lean_object* v___y_2125_ = _args[10];
lean_object* v___y_2126_ = _args[11];
lean_object* v___y_2127_ = _args[12];
lean_object* v___y_2128_ = _args[13];
lean_object* v___y_2129_ = _args[14];
lean_object* v___y_2130_ = _args[15];
lean_object* v___y_2131_ = _args[16];
lean_object* v___y_2132_ = _args[17];
lean_object* v___y_2133_ = _args[18];
lean_object* v___y_2134_ = _args[19];
lean_object* v___y_2135_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_2136_; uint8_t v_clsEnabled_boxed_2137_; lean_object* v_res_2138_; 
v_collapsed_boxed_2136_ = lean_unbox(v_collapsed_2116_);
v_clsEnabled_boxed_2137_ = lean_unbox(v_clsEnabled_2119_);
v_res_2138_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v_cls_2115_, v_collapsed_boxed_2136_, v_tag_2117_, v_opts_2118_, v_clsEnabled_boxed_2137_, v_oldTraces_2120_, v_msg_2121_, v_resStartStop_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v_opts_2118_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
if (lean_obj_tag(v_x_2140_) == 0)
{
return v_x_2139_;
}
else
{
lean_object* v_key_2141_; lean_object* v_value_2142_; lean_object* v_tail_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2166_; 
v_key_2141_ = lean_ctor_get(v_x_2140_, 0);
v_value_2142_ = lean_ctor_get(v_x_2140_, 1);
v_tail_2143_ = lean_ctor_get(v_x_2140_, 2);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_x_2140_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2145_ = v_x_2140_;
v_isShared_2146_ = v_isSharedCheck_2166_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_tail_2143_);
lean_inc(v_value_2142_);
lean_inc(v_key_2141_);
lean_dec(v_x_2140_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2166_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; uint64_t v___x_2148_; uint64_t v___x_2149_; uint64_t v___x_2150_; uint64_t v_fold_2151_; uint64_t v___x_2152_; uint64_t v___x_2153_; uint64_t v___x_2154_; size_t v___x_2155_; size_t v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2147_ = lean_array_get_size(v_x_2139_);
v___x_2148_ = lean_uint64_of_nat(v_key_2141_);
v___x_2149_ = 32ULL;
v___x_2150_ = lean_uint64_shift_right(v___x_2148_, v___x_2149_);
v_fold_2151_ = lean_uint64_xor(v___x_2148_, v___x_2150_);
v___x_2152_ = 16ULL;
v___x_2153_ = lean_uint64_shift_right(v_fold_2151_, v___x_2152_);
v___x_2154_ = lean_uint64_xor(v_fold_2151_, v___x_2153_);
v___x_2155_ = lean_uint64_to_usize(v___x_2154_);
v___x_2156_ = lean_usize_of_nat(v___x_2147_);
v___x_2157_ = ((size_t)1ULL);
v___x_2158_ = lean_usize_sub(v___x_2156_, v___x_2157_);
v___x_2159_ = lean_usize_land(v___x_2155_, v___x_2158_);
v___x_2160_ = lean_array_uget_borrowed(v_x_2139_, v___x_2159_);
lean_inc(v___x_2160_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 2, v___x_2160_);
v___x_2162_ = v___x_2145_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_key_2141_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_value_2142_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_array_uset(v_x_2139_, v___x_2159_, v___x_2162_);
v_x_2139_ = v___x_2163_;
v_x_2140_ = v_tail_2143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(lean_object* v_i_2167_, lean_object* v_source_2168_, lean_object* v_target_2169_){
_start:
{
lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = lean_array_get_size(v_source_2168_);
v___x_2171_ = lean_nat_dec_lt(v_i_2167_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_dec_ref(v_source_2168_);
lean_dec(v_i_2167_);
return v_target_2169_;
}
else
{
lean_object* v_es_2172_; lean_object* v___x_2173_; lean_object* v_source_2174_; lean_object* v_target_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_es_2172_ = lean_array_fget(v_source_2168_, v_i_2167_);
v___x_2173_ = lean_box(0);
v_source_2174_ = lean_array_fset(v_source_2168_, v_i_2167_, v___x_2173_);
v_target_2175_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_target_2169_, v_es_2172_);
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_add(v_i_2167_, v___x_2176_);
lean_dec(v_i_2167_);
v_i_2167_ = v___x_2177_;
v_source_2168_ = v_source_2174_;
v_target_2169_ = v_target_2175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(lean_object* v___x_2179_, lean_object* v_data_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_nbuckets_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2181_ = lean_array_get_size(v_data_2180_);
v___x_2182_ = lean_unsigned_to_nat(2u);
v_nbuckets_2183_ = lean_nat_mul(v___x_2181_, v___x_2182_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_mk_array(v_nbuckets_2183_, v___x_2185_);
v___x_2187_ = lean_array_propagate_mark(v_data_2180_, v___x_2186_);
v___x_2188_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v___x_2184_, v_data_2180_, v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg___boxed(lean_object* v___x_2189_, lean_object* v_data_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_2189_, v_data_2190_);
lean_dec(v___x_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(lean_object* v_a_2192_, lean_object* v_x_2193_){
_start:
{
if (lean_obj_tag(v_x_2193_) == 0)
{
uint8_t v___x_2194_; 
v___x_2194_ = 0;
return v___x_2194_;
}
else
{
lean_object* v_key_2195_; lean_object* v_tail_2196_; uint8_t v___x_2197_; 
v_key_2195_ = lean_ctor_get(v_x_2193_, 0);
v_tail_2196_ = lean_ctor_get(v_x_2193_, 2);
v___x_2197_ = lean_nat_dec_eq(v_key_2195_, v_a_2192_);
if (v___x_2197_ == 0)
{
v_x_2193_ = v_tail_2196_;
goto _start;
}
else
{
return v___x_2197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg___boxed(lean_object* v_a_2199_, lean_object* v_x_2200_){
_start:
{
uint8_t v_res_2201_; lean_object* v_r_2202_; 
v_res_2201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2199_, v_x_2200_);
lean_dec(v_x_2200_);
lean_dec(v_a_2199_);
v_r_2202_ = lean_box(v_res_2201_);
return v_r_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(lean_object* v___x_2203_, lean_object* v_m_2204_, lean_object* v_a_2205_, lean_object* v_b_2206_){
_start:
{
lean_object* v_size_2207_; lean_object* v_buckets_2208_; lean_object* v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; uint64_t v_fold_2213_; uint64_t v___x_2214_; uint64_t v___x_2215_; uint64_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; size_t v___x_2221_; lean_object* v_bkt_2222_; uint8_t v___x_2223_; 
v_size_2207_ = lean_ctor_get(v_m_2204_, 0);
v_buckets_2208_ = lean_ctor_get(v_m_2204_, 1);
v___x_2209_ = lean_array_get_size(v_buckets_2208_);
v___x_2210_ = lean_uint64_of_nat(v_a_2205_);
v___x_2211_ = 32ULL;
v___x_2212_ = lean_uint64_shift_right(v___x_2210_, v___x_2211_);
v_fold_2213_ = lean_uint64_xor(v___x_2210_, v___x_2212_);
v___x_2214_ = 16ULL;
v___x_2215_ = lean_uint64_shift_right(v_fold_2213_, v___x_2214_);
v___x_2216_ = lean_uint64_xor(v_fold_2213_, v___x_2215_);
v___x_2217_ = lean_uint64_to_usize(v___x_2216_);
v___x_2218_ = lean_usize_of_nat(v___x_2209_);
v___x_2219_ = ((size_t)1ULL);
v___x_2220_ = lean_usize_sub(v___x_2218_, v___x_2219_);
v___x_2221_ = lean_usize_land(v___x_2217_, v___x_2220_);
v_bkt_2222_ = lean_array_uget_borrowed(v_buckets_2208_, v___x_2221_);
v___x_2223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2205_, v_bkt_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2244_; 
lean_inc_ref(v_buckets_2208_);
lean_inc(v_size_2207_);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_m_2204_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; lean_object* v_unused_2246_; 
v_unused_2245_ = lean_ctor_get(v_m_2204_, 1);
lean_dec(v_unused_2245_);
v_unused_2246_ = lean_ctor_get(v_m_2204_, 0);
lean_dec(v_unused_2246_);
v___x_2225_ = v_m_2204_;
v_isShared_2226_ = v_isSharedCheck_2244_;
goto v_resetjp_2224_;
}
else
{
lean_dec(v_m_2204_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2244_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v_size_x27_2228_; lean_object* v___x_2229_; lean_object* v_buckets_x27_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v___x_2227_ = lean_unsigned_to_nat(1u);
v_size_x27_2228_ = lean_nat_add(v_size_2207_, v___x_2227_);
lean_dec(v_size_2207_);
lean_inc(v_bkt_2222_);
v___x_2229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2229_, 0, v_a_2205_);
lean_ctor_set(v___x_2229_, 1, v_b_2206_);
lean_ctor_set(v___x_2229_, 2, v_bkt_2222_);
v_buckets_x27_2230_ = lean_array_uset(v_buckets_2208_, v___x_2221_, v___x_2229_);
v___x_2231_ = lean_unsigned_to_nat(4u);
v___x_2232_ = lean_nat_mul(v_size_x27_2228_, v___x_2231_);
v___x_2233_ = lean_unsigned_to_nat(3u);
v___x_2234_ = lean_nat_div(v___x_2232_, v___x_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_array_get_size(v_buckets_x27_2230_);
v___x_2236_ = lean_nat_dec_le(v___x_2234_, v___x_2235_);
lean_dec(v___x_2234_);
if (v___x_2236_ == 0)
{
lean_object* v_val_2237_; lean_object* v___x_2239_; 
v_val_2237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_2203_, v_buckets_x27_2230_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 1, v_val_2237_);
lean_ctor_set(v___x_2225_, 0, v_size_x27_2228_);
v___x_2239_ = v___x_2225_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_size_x27_2228_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_val_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
else
{
lean_object* v___x_2242_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 1, v_buckets_x27_2230_);
lean_ctor_set(v___x_2225_, 0, v_size_x27_2228_);
v___x_2242_ = v___x_2225_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_size_x27_2228_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_buckets_x27_2230_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_dec(v_b_2206_);
lean_dec(v_a_2205_);
return v_m_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg___boxed(lean_object* v___x_2247_, lean_object* v_m_2248_, lean_object* v_a_2249_, lean_object* v_b_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_2247_, v_m_2248_, v_a_2249_, v_b_2250_);
lean_dec(v___x_2247_);
return v_res_2251_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(lean_object* v___x_2252_, lean_object* v_m_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_buckets_2255_; lean_object* v___x_2256_; uint64_t v___x_2257_; uint64_t v___x_2258_; uint64_t v___x_2259_; uint64_t v_fold_2260_; uint64_t v___x_2261_; uint64_t v___x_2262_; uint64_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; size_t v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v_buckets_2255_ = lean_ctor_get(v_m_2253_, 1);
v___x_2256_ = lean_array_get_size(v_buckets_2255_);
v___x_2257_ = lean_uint64_of_nat(v_a_2254_);
v___x_2258_ = 32ULL;
v___x_2259_ = lean_uint64_shift_right(v___x_2257_, v___x_2258_);
v_fold_2260_ = lean_uint64_xor(v___x_2257_, v___x_2259_);
v___x_2261_ = 16ULL;
v___x_2262_ = lean_uint64_shift_right(v_fold_2260_, v___x_2261_);
v___x_2263_ = lean_uint64_xor(v_fold_2260_, v___x_2262_);
v___x_2264_ = lean_uint64_to_usize(v___x_2263_);
v___x_2265_ = lean_usize_of_nat(v___x_2256_);
v___x_2266_ = ((size_t)1ULL);
v___x_2267_ = lean_usize_sub(v___x_2265_, v___x_2266_);
v___x_2268_ = lean_usize_land(v___x_2264_, v___x_2267_);
v___x_2269_ = lean_array_uget_borrowed(v_buckets_2255_, v___x_2268_);
v___x_2270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_2254_, v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg___boxed(lean_object* v___x_2271_, lean_object* v_m_2272_, lean_object* v_a_2273_){
_start:
{
uint8_t v_res_2274_; lean_object* v_r_2275_; 
v_res_2274_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2271_, v_m_2272_, v_a_2273_);
lean_dec(v_a_2273_);
lean_dec_ref(v_m_2272_);
lean_dec(v___x_2271_);
v_r_2275_ = lean_box(v_res_2274_);
return v_r_2275_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(lean_object* v_acc_2279_, lean_object* v_decls_2280_, lean_object* v_idx_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = lean_array_get_size(v_decls_2280_);
v___x_2284_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_2283_, v_a_2282_, v_idx_2281_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_box(0);
lean_inc(v_idx_2281_);
v___x_2286_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_2283_, v_a_2282_, v_idx_2281_, v___x_2285_);
v___x_2287_ = lean_array_fget_borrowed(v_decls_2280_, v_idx_2281_);
if (lean_obj_tag(v___x_2287_) == 2)
{
lean_object* v_l_2288_; lean_object* v_r_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___y_2293_; lean_object* v___y_2294_; uint8_t v___y_2295_; uint8_t v___y_2319_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_l_2288_ = lean_ctor_get(v___x_2287_, 0);
v_r_2289_ = lean_ctor_get(v___x_2287_, 1);
v___x_2290_ = lean_unsigned_to_nat(1u);
v___x_2291_ = lean_nat_shiftr(v_l_2288_, v___x_2290_);
v___x_2325_ = lean_nat_land(v___x_2290_, v_l_2288_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = lean_nat_dec_eq(v___x_2325_, v___x_2326_);
lean_dec(v___x_2325_);
if (v___x_2327_ == 0)
{
uint8_t v___x_2328_; 
v___x_2328_ = 1;
v___y_2319_ = v___x_2328_;
goto v___jp_2318_;
}
else
{
v___y_2319_ = v___x_2284_;
goto v___jp_2318_;
}
v___jp_2292_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_fst_2315_; lean_object* v_snd_2316_; 
v___x_2296_ = l_Nat_reprFast(v_idx_2281_);
v___x_2297_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__0));
lean_inc_ref(v___x_2296_);
v___x_2298_ = lean_string_append(v___x_2296_, v___x_2297_);
lean_inc(v___x_2291_);
v___x_2299_ = l_Nat_reprFast(v___x_2291_);
v___x_2300_ = lean_string_append(v___x_2298_, v___x_2299_);
lean_dec_ref(v___x_2299_);
v___x_2301_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2293_);
v___x_2302_ = lean_string_append(v___x_2300_, v___x_2301_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__1));
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
v___x_2305_ = lean_string_append(v___x_2304_, v___x_2296_);
lean_dec_ref(v___x_2296_);
v___x_2306_ = lean_string_append(v___x_2305_, v___x_2297_);
lean_inc(v___y_2294_);
v___x_2307_ = l_Nat_reprFast(v___y_2294_);
v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2295_);
v___x_2310_ = lean_string_append(v___x_2308_, v___x_2309_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__2));
v___x_2312_ = lean_string_append(v___x_2310_, v___x_2311_);
v___x_2313_ = lean_string_append(v_acc_2279_, v___x_2312_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v___x_2313_, v_decls_2280_, v___x_2291_, v___x_2286_);
v_fst_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_fst_2315_);
v_snd_2316_ = lean_ctor_get(v___x_2314_, 1);
lean_inc(v_snd_2316_);
lean_dec_ref(v___x_2314_);
v_acc_2279_ = v_fst_2315_;
v_idx_2281_ = v___y_2294_;
v_a_2282_ = v_snd_2316_;
goto _start;
}
v___jp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2320_ = lean_nat_shiftr(v_r_2289_, v___x_2290_);
v___x_2321_ = lean_nat_land(v___x_2290_, v_r_2289_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = lean_nat_dec_eq(v___x_2321_, v___x_2322_);
lean_dec(v___x_2321_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; 
v___x_2324_ = 1;
v___y_2293_ = v___y_2319_;
v___y_2294_ = v___x_2320_;
v___y_2295_ = v___x_2324_;
goto v___jp_2292_;
}
else
{
v___y_2293_ = v___y_2319_;
v___y_2294_ = v___x_2320_;
v___y_2295_ = v___x_2284_;
goto v___jp_2292_;
}
}
}
else
{
lean_object* v___x_2329_; 
lean_dec(v_idx_2281_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v_acc_2279_);
lean_ctor_set(v___x_2329_, 1, v___x_2286_);
return v___x_2329_;
}
}
else
{
lean_object* v___x_2330_; 
lean_dec(v_idx_2281_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_acc_2279_);
lean_ctor_set(v___x_2330_, 1, v_a_2282_);
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___boxed(lean_object* v_acc_2331_, lean_object* v_decls_2332_, lean_object* v_idx_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_2331_, v_decls_2332_, v_idx_2333_, v_a_2334_);
lean_dec_ref(v_decls_2332_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(lean_object* v_decls_2344_, lean_object* v_idx_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = lean_array_fget_borrowed(v_decls_2344_, v_idx_2345_);
switch(lean_obj_tag(v___x_2346_))
{
case 0:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2347_ = l_Nat_reprFast(v_idx_2345_);
v___x_2348_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
v___x_2349_ = lean_string_append(v___x_2347_, v___x_2348_);
v___x_2350_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__1));
v___x_2351_ = lean_string_append(v___x_2349_, v___x_2350_);
v___x_2352_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__2));
v___x_2353_ = lean_string_append(v___x_2351_, v___x_2352_);
return v___x_2353_;
}
case 1:
{
lean_object* v_idx_2354_; lean_object* v_var_2355_; lean_object* v_idx_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_idx_2354_ = lean_ctor_get(v___x_2346_, 0);
v_var_2355_ = lean_ctor_get(v_idx_2354_, 0);
v_idx_2356_ = lean_ctor_get(v_idx_2354_, 2);
v___x_2357_ = l_Nat_reprFast(v_idx_2345_);
v___x_2358_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
v___x_2359_ = lean_string_append(v___x_2357_, v___x_2358_);
v___x_2360_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__3));
lean_inc(v_var_2355_);
v___x_2361_ = l_Nat_reprFast(v_var_2355_);
v___x_2362_ = lean_string_append(v___x_2360_, v___x_2361_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__4));
v___x_2364_ = lean_string_append(v___x_2362_, v___x_2363_);
lean_inc(v_idx_2356_);
v___x_2365_ = l_Nat_reprFast(v_idx_2356_);
v___x_2366_ = lean_string_append(v___x_2364_, v___x_2365_);
lean_dec_ref(v___x_2365_);
v___x_2367_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__5));
v___x_2368_ = lean_string_append(v___x_2366_, v___x_2367_);
v___x_2369_ = lean_string_append(v___x_2359_, v___x_2368_);
lean_dec_ref(v___x_2368_);
v___x_2370_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__6));
v___x_2371_ = lean_string_append(v___x_2369_, v___x_2370_);
return v___x_2371_;
}
default: 
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2372_ = l_Nat_reprFast(v_idx_2345_);
v___x_2373_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__0));
lean_inc_ref(v___x_2372_);
v___x_2374_ = lean_string_append(v___x_2372_, v___x_2373_);
v___x_2375_ = lean_string_append(v___x_2374_, v___x_2372_);
lean_dec_ref(v___x_2372_);
v___x_2376_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___closed__7));
v___x_2377_ = lean_string_append(v___x_2375_, v___x_2376_);
return v___x_2377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14___boxed(lean_object* v_decls_2378_, lean_object* v_idx_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(v_decls_2378_, v_idx_2379_);
lean_dec_ref(v_decls_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(lean_object* v_decls_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 0)
{
return v_x_2382_;
}
else
{
lean_object* v_key_2384_; lean_object* v_tail_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_key_2384_ = lean_ctor_get(v_x_2383_, 0);
lean_inc(v_key_2384_);
v_tail_2385_ = lean_ctor_get(v_x_2383_, 2);
lean_inc(v_tail_2385_);
lean_dec_ref_known(v_x_2383_, 3);
v___x_2386_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__14(v_decls_2381_, v_key_2384_);
v___x_2387_ = lean_string_append(v_x_2382_, v___x_2386_);
lean_dec_ref(v___x_2386_);
v_x_2382_ = v___x_2387_;
v_x_2383_ = v_tail_2385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16___boxed(lean_object* v_decls_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(v_decls_2389_, v_x_2390_, v_x_2391_);
lean_dec_ref(v_decls_2389_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(lean_object* v_decls_2393_, lean_object* v_as_2394_, size_t v_i_2395_, size_t v_stop_2396_, lean_object* v_b_2397_){
_start:
{
uint8_t v___x_2398_; 
v___x_2398_ = lean_usize_dec_eq(v_i_2395_, v_stop_2396_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; size_t v___x_2401_; size_t v___x_2402_; 
v___x_2399_ = lean_array_uget_borrowed(v_as_2394_, v_i_2395_);
lean_inc(v___x_2399_);
v___x_2400_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__16(v_decls_2393_, v_b_2397_, v___x_2399_);
v___x_2401_ = ((size_t)1ULL);
v___x_2402_ = lean_usize_add(v_i_2395_, v___x_2401_);
v_i_2395_ = v___x_2402_;
v_b_2397_ = v___x_2400_;
goto _start;
}
else
{
return v_b_2397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17___boxed(lean_object* v_decls_2404_, lean_object* v_as_2405_, lean_object* v_i_2406_, lean_object* v_stop_2407_, lean_object* v_b_2408_){
_start:
{
size_t v_i_boxed_2409_; size_t v_stop_boxed_2410_; lean_object* v_res_2411_; 
v_i_boxed_2409_ = lean_unbox_usize(v_i_2406_);
lean_dec(v_i_2406_);
v_stop_boxed_2410_ = lean_unbox_usize(v_stop_2407_);
lean_dec(v_stop_2407_);
v_res_2411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2404_, v_as_2405_, v_i_boxed_2409_, v_stop_boxed_2410_, v_b_2408_);
lean_dec_ref(v_as_2405_);
lean_dec_ref(v_decls_2404_);
return v_res_2411_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_unsigned_to_nat(16u);
v___x_2414_ = lean_mk_array(v___x_2413_, v___x_2412_);
return v___x_2414_;
}
}
static lean_object* _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__0);
v___x_2416_ = lean_unsigned_to_nat(0u);
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v___x_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(lean_object* v_entry_2420_){
_start:
{
lean_object* v_aig_2421_; lean_object* v_ref_2422_; lean_object* v_decls_2423_; lean_object* v_gate_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v_fst_2429_; lean_object* v_snd_2430_; lean_object* v___y_2432_; lean_object* v_buckets_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_aig_2421_ = lean_ctor_get(v_entry_2420_, 0);
lean_inc_ref(v_aig_2421_);
v_ref_2422_ = lean_ctor_get(v_entry_2420_, 1);
lean_inc_ref(v_ref_2422_);
lean_dec_ref(v_entry_2420_);
v_decls_2423_ = lean_ctor_get(v_aig_2421_, 0);
lean_inc_ref(v_decls_2423_);
lean_dec_ref(v_aig_2421_);
v_gate_2424_ = lean_ctor_get(v_ref_2422_, 0);
lean_inc(v_gate_2424_);
lean_dec_ref(v_ref_2422_);
v___x_2425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = lean_obj_once(&l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1, &l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1_once, _init_l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__1);
v___x_2428_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v___x_2425_, v_decls_2423_, v_gate_2424_, v___x_2427_);
v_fst_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_fst_2429_);
v_snd_2430_ = lean_ctor_get(v___x_2428_, 1);
lean_inc(v_snd_2430_);
lean_dec_ref(v___x_2428_);
v_buckets_2438_ = lean_ctor_get(v_snd_2430_, 1);
lean_inc_ref(v_buckets_2438_);
lean_dec(v_snd_2430_);
v___x_2439_ = lean_array_get_size(v_buckets_2438_);
v___x_2440_ = lean_nat_dec_lt(v___x_2426_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_dec_ref(v_buckets_2438_);
lean_dec_ref(v_decls_2423_);
v___y_2432_ = v___x_2425_;
goto v___jp_2431_;
}
else
{
size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = ((size_t)0ULL);
v___x_2442_ = lean_usize_of_nat(v___x_2439_);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__17(v_decls_2423_, v_buckets_2438_, v___x_2441_, v___x_2442_, v___x_2425_);
lean_dec_ref(v_buckets_2438_);
lean_dec_ref(v_decls_2423_);
v___y_2432_ = v___x_2443_;
goto v___jp_2431_;
}
v___jp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2433_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__2));
v___x_2434_ = lean_string_append(v___x_2433_, v___y_2432_);
lean_dec_ref(v___y_2432_);
v___x_2435_ = lean_string_append(v___x_2434_, v_fst_2429_);
lean_dec(v_fst_2429_);
v___x_2436_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7___closed__3));
v___x_2437_ = lean_string_append(v___x_2435_, v___x_2436_);
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(lean_object* v_cls_2446_, lean_object* v_msg_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_ref_2453_; lean_object* v___x_2454_; lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2500_; 
v_ref_2453_ = lean_ctor_get(v___y_2450_, 2);
v___x_2454_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2500_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2500_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v_traceState_2460_; lean_object* v_env_2461_; lean_object* v_nextMacroScope_2462_; lean_object* v_ngen_2463_; lean_object* v_auxDeclNGen_2464_; lean_object* v_cache_2465_; lean_object* v_recordedDeps_2466_; lean_object* v_messages_2467_; lean_object* v_infoState_2468_; lean_object* v_snapshotTasks_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2499_; 
v___x_2459_ = lean_st_ref_take(v___y_2451_);
v_traceState_2460_ = lean_ctor_get(v___x_2459_, 4);
v_env_2461_ = lean_ctor_get(v___x_2459_, 0);
v_nextMacroScope_2462_ = lean_ctor_get(v___x_2459_, 1);
v_ngen_2463_ = lean_ctor_get(v___x_2459_, 2);
v_auxDeclNGen_2464_ = lean_ctor_get(v___x_2459_, 3);
v_cache_2465_ = lean_ctor_get(v___x_2459_, 5);
v_recordedDeps_2466_ = lean_ctor_get(v___x_2459_, 6);
v_messages_2467_ = lean_ctor_get(v___x_2459_, 7);
v_infoState_2468_ = lean_ctor_get(v___x_2459_, 8);
v_snapshotTasks_2469_ = lean_ctor_get(v___x_2459_, 9);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2471_ = v___x_2459_;
v_isShared_2472_ = v_isSharedCheck_2499_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_snapshotTasks_2469_);
lean_inc(v_infoState_2468_);
lean_inc(v_messages_2467_);
lean_inc(v_recordedDeps_2466_);
lean_inc(v_cache_2465_);
lean_inc(v_traceState_2460_);
lean_inc(v_auxDeclNGen_2464_);
lean_inc(v_ngen_2463_);
lean_inc(v_nextMacroScope_2462_);
lean_inc(v_env_2461_);
lean_dec(v___x_2459_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2499_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
uint64_t v_tid_2473_; lean_object* v_traces_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2498_; 
v_tid_2473_ = lean_ctor_get_uint64(v_traceState_2460_, sizeof(void*)*1);
v_traces_2474_ = lean_ctor_get(v_traceState_2460_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_traceState_2460_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2476_ = v_traceState_2460_;
v_isShared_2477_ = v_isSharedCheck_2498_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_traces_2474_);
lean_dec(v_traceState_2460_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2498_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; double v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_box(0);
v___x_2480_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
v___x_2481_ = 0;
v___x_2482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_2483_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2483_, 0, v_cls_2446_);
lean_ctor_set(v___x_2483_, 1, v___x_2479_);
lean_ctor_set(v___x_2483_, 2, v___x_2482_);
lean_ctor_set_float(v___x_2483_, sizeof(void*)*3, v___x_2480_);
lean_ctor_set_float(v___x_2483_, sizeof(void*)*3 + 8, v___x_2480_);
lean_ctor_set_uint8(v___x_2483_, sizeof(void*)*3 + 16, v___x_2481_);
v___x_2484_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___closed__0));
v___x_2485_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v_a_2455_);
lean_ctor_set(v___x_2485_, 2, v___x_2484_);
lean_inc(v_ref_2453_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_ref_2453_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = l_Lean_PersistentArray_push___redArg(v_traces_2474_, v___x_2486_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v___x_2487_);
v___x_2489_ = v___x_2476_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2487_);
lean_ctor_set_uint64(v_reuseFailAlloc_2497_, sizeof(void*)*1, v_tid_2473_);
v___x_2489_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2491_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 4, v___x_2489_);
v___x_2491_ = v___x_2471_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_env_2461_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_nextMacroScope_2462_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_ngen_2463_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_auxDeclNGen_2464_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2496_, 5, v_cache_2465_);
lean_ctor_set(v_reuseFailAlloc_2496_, 6, v_recordedDeps_2466_);
lean_ctor_set(v_reuseFailAlloc_2496_, 7, v_messages_2467_);
lean_ctor_set(v_reuseFailAlloc_2496_, 8, v_infoState_2468_);
lean_ctor_set(v_reuseFailAlloc_2496_, 9, v_snapshotTasks_2469_);
v___x_2491_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2492_ = lean_st_ref_put(v___y_2451_, v___x_2491_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2478_);
v___x_2494_ = v___x_2457_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2478_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg___boxed(lean_object* v_cls_2501_, lean_object* v_msg_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_2501_, v_msg_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2508_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(lean_object* v_e_2509_){
_start:
{
if (lean_obj_tag(v_e_2509_) == 0)
{
uint8_t v___x_2510_; 
v___x_2510_ = 2;
return v___x_2510_;
}
else
{
uint8_t v___x_2511_; 
v___x_2511_ = 0;
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10___boxed(lean_object* v_e_2512_){
_start:
{
uint8_t v_res_2513_; lean_object* v_r_2514_; 
v_res_2513_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_e_2512_);
lean_dec_ref(v_e_2512_);
v_r_2514_ = lean_box(v_res_2513_);
return v_r_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(lean_object* v_cls_2515_, uint8_t v_collapsed_2516_, lean_object* v_tag_2517_, lean_object* v_opts_2518_, uint8_t v_clsEnabled_2519_, lean_object* v_oldTraces_2520_, lean_object* v_msg_2521_, lean_object* v_resStartStop_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_fst_2536_; lean_object* v_snd_2537_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v_data_2541_; lean_object* v_fst_2552_; lean_object* v_snd_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; lean_object* v___y_2557_; lean_object* v_a_2558_; uint8_t v___y_2573_; double v___y_2605_; 
v_fst_2536_ = lean_ctor_get(v_resStartStop_2522_, 0);
lean_inc(v_fst_2536_);
v_snd_2537_ = lean_ctor_get(v_resStartStop_2522_, 1);
lean_inc(v_snd_2537_);
lean_dec_ref(v_resStartStop_2522_);
v_fst_2552_ = lean_ctor_get(v_snd_2537_, 0);
lean_inc(v_fst_2552_);
v_snd_2553_ = lean_ctor_get(v_snd_2537_, 1);
lean_inc(v_snd_2553_);
lean_dec(v_snd_2537_);
v___x_2554_ = l_Lean_trace_profiler;
v___x_2555_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2518_, v___x_2554_);
if (v___x_2555_ == 0)
{
v___y_2573_ = v___x_2555_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2610_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2611_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_2518_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; double v___x_2614_; double v___x_2615_; double v___x_2616_; 
v___x_2612_ = l_Lean_trace_profiler_threshold;
v___x_2613_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2518_, v___x_2612_);
v___x_2614_ = lean_float_of_nat(v___x_2613_);
v___x_2615_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_2616_ = lean_float_div(v___x_2614_, v___x_2615_);
v___y_2605_ = v___x_2616_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; double v___x_2619_; 
v___x_2617_ = l_Lean_trace_profiler_threshold;
v___x_2618_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_2518_, v___x_2617_);
v___x_2619_ = lean_float_of_nat(v___x_2618_);
v___y_2605_ = v___x_2619_;
goto v___jp_2604_;
}
}
v___jp_2538_:
{
lean_object* v___x_2542_; 
lean_inc(v___y_2539_);
v___x_2542_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2520_, v_data_2541_, v___y_2539_, v___y_2540_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v___x_2543_; 
lean_dec_ref_known(v___x_2542_, 1);
v___x_2543_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2536_);
return v___x_2543_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_fst_2536_);
v_a_2544_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2542_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2542_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
v___jp_2556_:
{
uint8_t v_result_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; double v___x_2562_; lean_object* v_data_2563_; 
v_result_2559_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__10(v_fst_2536_);
v___x_2560_ = lean_box(v_result_2559_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
v___x_2562_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_2517_);
lean_inc_ref(v___x_2561_);
lean_inc(v_cls_2515_);
v_data_2563_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2563_, 0, v_cls_2515_);
lean_ctor_set(v_data_2563_, 1, v___x_2561_);
lean_ctor_set(v_data_2563_, 2, v_tag_2517_);
lean_ctor_set_float(v_data_2563_, sizeof(void*)*3, v___x_2562_);
lean_ctor_set_float(v_data_2563_, sizeof(void*)*3 + 8, v___x_2562_);
lean_ctor_set_uint8(v_data_2563_, sizeof(void*)*3 + 16, v_collapsed_2516_);
if (v___x_2555_ == 0)
{
lean_dec_ref_known(v___x_2561_, 1);
lean_dec(v_snd_2553_);
lean_dec(v_fst_2552_);
lean_dec_ref(v_tag_2517_);
lean_dec(v_cls_2515_);
v___y_2539_ = v___y_2557_;
v___y_2540_ = v_a_2558_;
v_data_2541_ = v_data_2563_;
goto v___jp_2538_;
}
else
{
lean_object* v_data_2564_; double v___x_2565_; double v___x_2566_; 
lean_dec_ref_known(v_data_2563_, 3);
v_data_2564_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2564_, 0, v_cls_2515_);
lean_ctor_set(v_data_2564_, 1, v___x_2561_);
lean_ctor_set(v_data_2564_, 2, v_tag_2517_);
v___x_2565_ = lean_unbox_float(v_fst_2552_);
lean_dec(v_fst_2552_);
lean_ctor_set_float(v_data_2564_, sizeof(void*)*3, v___x_2565_);
v___x_2566_ = lean_unbox_float(v_snd_2553_);
lean_dec(v_snd_2553_);
lean_ctor_set_float(v_data_2564_, sizeof(void*)*3 + 8, v___x_2566_);
lean_ctor_set_uint8(v_data_2564_, sizeof(void*)*3 + 16, v_collapsed_2516_);
v___y_2539_ = v___y_2557_;
v___y_2540_ = v_a_2558_;
v_data_2541_ = v_data_2564_;
goto v___jp_2538_;
}
}
v___jp_2567_:
{
lean_object* v_ref_2568_; lean_object* v___x_2569_; 
v_ref_2568_ = lean_ctor_get(v___y_2533_, 2);
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc(v___y_2525_);
lean_inc_ref(v___y_2524_);
lean_inc(v___y_2523_);
lean_inc(v_fst_2536_);
v___x_2569_ = lean_apply_14(v_msg_2521_, v_fst_2536_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, lean_box(0));
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___y_2557_ = v_ref_2568_;
v_a_2558_ = v_a_2570_;
goto v___jp_2556_;
}
else
{
lean_object* v___x_2571_; 
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_2557_ = v_ref_2568_;
v_a_2558_ = v___x_2571_;
goto v___jp_2556_;
}
}
v___jp_2572_:
{
if (v_clsEnabled_2519_ == 0)
{
if (v___y_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v_traceState_2575_; lean_object* v_env_2576_; lean_object* v_nextMacroScope_2577_; lean_object* v_ngen_2578_; lean_object* v_auxDeclNGen_2579_; lean_object* v_cache_2580_; lean_object* v_recordedDeps_2581_; lean_object* v_messages_2582_; lean_object* v_infoState_2583_; lean_object* v_snapshotTasks_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_snd_2553_);
lean_dec(v_fst_2552_);
lean_dec_ref(v_msg_2521_);
lean_dec_ref(v_tag_2517_);
lean_dec(v_cls_2515_);
v___x_2574_ = lean_st_ref_take(v___y_2534_);
v_traceState_2575_ = lean_ctor_get(v___x_2574_, 4);
v_env_2576_ = lean_ctor_get(v___x_2574_, 0);
v_nextMacroScope_2577_ = lean_ctor_get(v___x_2574_, 1);
v_ngen_2578_ = lean_ctor_get(v___x_2574_, 2);
v_auxDeclNGen_2579_ = lean_ctor_get(v___x_2574_, 3);
v_cache_2580_ = lean_ctor_get(v___x_2574_, 5);
v_recordedDeps_2581_ = lean_ctor_get(v___x_2574_, 6);
v_messages_2582_ = lean_ctor_get(v___x_2574_, 7);
v_infoState_2583_ = lean_ctor_get(v___x_2574_, 8);
v_snapshotTasks_2584_ = lean_ctor_get(v___x_2574_, 9);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2586_ = v___x_2574_;
v_isShared_2587_ = v_isSharedCheck_2603_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_snapshotTasks_2584_);
lean_inc(v_infoState_2583_);
lean_inc(v_messages_2582_);
lean_inc(v_recordedDeps_2581_);
lean_inc(v_cache_2580_);
lean_inc(v_traceState_2575_);
lean_inc(v_auxDeclNGen_2579_);
lean_inc(v_ngen_2578_);
lean_inc(v_nextMacroScope_2577_);
lean_inc(v_env_2576_);
lean_dec(v___x_2574_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2603_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
uint64_t v_tid_2588_; lean_object* v_traces_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2602_; 
v_tid_2588_ = lean_ctor_get_uint64(v_traceState_2575_, sizeof(void*)*1);
v_traces_2589_ = lean_ctor_get(v_traceState_2575_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_traceState_2575_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2591_ = v_traceState_2575_;
v_isShared_2592_ = v_isSharedCheck_2602_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_traces_2589_);
lean_dec(v_traceState_2575_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2602_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2520_, v_traces_2589_);
lean_dec_ref(v_traces_2589_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2593_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2593_);
lean_ctor_set_uint64(v_reuseFailAlloc_2601_, sizeof(void*)*1, v_tid_2588_);
v___x_2595_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 4, v___x_2595_);
v___x_2597_ = v___x_2586_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_env_2576_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_nextMacroScope_2577_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_ngen_2578_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_auxDeclNGen_2579_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v_cache_2580_);
lean_ctor_set(v_reuseFailAlloc_2600_, 6, v_recordedDeps_2581_);
lean_ctor_set(v_reuseFailAlloc_2600_, 7, v_messages_2582_);
lean_ctor_set(v_reuseFailAlloc_2600_, 8, v_infoState_2583_);
lean_ctor_set(v_reuseFailAlloc_2600_, 9, v_snapshotTasks_2584_);
v___x_2597_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_st_ref_put(v___y_2534_, v___x_2597_);
v___x_2599_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_2536_);
return v___x_2599_;
}
}
}
}
}
else
{
goto v___jp_2567_;
}
}
else
{
goto v___jp_2567_;
}
}
v___jp_2604_:
{
double v___x_2606_; double v___x_2607_; double v___x_2608_; uint8_t v___x_2609_; 
v___x_2606_ = lean_unbox_float(v_snd_2553_);
v___x_2607_ = lean_unbox_float(v_fst_2552_);
v___x_2608_ = lean_float_sub(v___x_2606_, v___x_2607_);
v___x_2609_ = lean_float_decLt(v___y_2605_, v___x_2608_);
v___y_2573_ = v___x_2609_;
goto v___jp_2572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5___boxed(lean_object** _args){
lean_object* v_cls_2620_ = _args[0];
lean_object* v_collapsed_2621_ = _args[1];
lean_object* v_tag_2622_ = _args[2];
lean_object* v_opts_2623_ = _args[3];
lean_object* v_clsEnabled_2624_ = _args[4];
lean_object* v_oldTraces_2625_ = _args[5];
lean_object* v_msg_2626_ = _args[6];
lean_object* v_resStartStop_2627_ = _args[7];
lean_object* v___y_2628_ = _args[8];
lean_object* v___y_2629_ = _args[9];
lean_object* v___y_2630_ = _args[10];
lean_object* v___y_2631_ = _args[11];
lean_object* v___y_2632_ = _args[12];
lean_object* v___y_2633_ = _args[13];
lean_object* v___y_2634_ = _args[14];
lean_object* v___y_2635_ = _args[15];
lean_object* v___y_2636_ = _args[16];
lean_object* v___y_2637_ = _args[17];
lean_object* v___y_2638_ = _args[18];
lean_object* v___y_2639_ = _args[19];
lean_object* v___y_2640_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_2641_; uint8_t v_clsEnabled_boxed_2642_; lean_object* v_res_2643_; 
v_collapsed_boxed_2641_ = lean_unbox(v_collapsed_2621_);
v_clsEnabled_boxed_2642_ = lean_unbox(v_clsEnabled_2624_);
v_res_2643_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v_cls_2620_, v_collapsed_boxed_2641_, v_tag_2622_, v_opts_2623_, v_clsEnabled_boxed_2642_, v_oldTraces_2625_, v_msg_2626_, v_resStartStop_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v_opts_2623_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v_ks_2648_; lean_object* v_vs_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2673_; 
v_ks_2648_ = lean_ctor_get(v_x_2644_, 0);
v_vs_2649_ = lean_ctor_get(v_x_2644_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2651_ = v_x_2644_;
v_isShared_2652_ = v_isSharedCheck_2673_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_vs_2649_);
lean_inc(v_ks_2648_);
lean_dec(v_x_2644_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2673_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2653_ = lean_array_get_size(v_ks_2648_);
v___x_2654_ = lean_nat_dec_lt(v_x_2645_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_dec(v_x_2645_);
v___x_2655_ = lean_array_push(v_ks_2648_, v_x_2646_);
v___x_2656_ = lean_array_push(v_vs_2649_, v_x_2647_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2656_);
lean_ctor_set(v___x_2651_, 0, v___x_2655_);
v___x_2658_ = v___x_2651_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
else
{
lean_object* v_k_x27_2660_; uint8_t v___x_2661_; 
v_k_x27_2660_ = lean_array_fget_borrowed(v_ks_2648_, v_x_2645_);
v___x_2661_ = l_Lean_instBEqMVarId_beq(v_x_2646_, v_k_x27_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2663_; 
if (v_isShared_2652_ == 0)
{
v___x_2663_ = v___x_2651_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_ks_2648_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_vs_2649_);
v___x_2663_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_unsigned_to_nat(1u);
v___x_2665_ = lean_nat_add(v_x_2645_, v___x_2664_);
lean_dec(v_x_2645_);
v_x_2644_ = v___x_2663_;
v_x_2645_ = v___x_2665_;
goto _start;
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2668_ = lean_array_fset(v_ks_2648_, v_x_2645_, v_x_2646_);
v___x_2669_ = lean_array_fset(v_vs_2649_, v_x_2645_, v_x_2647_);
lean_dec(v_x_2645_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2669_);
lean_ctor_set(v___x_2651_, 0, v___x_2668_);
v___x_2671_ = v___x_2651_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(lean_object* v_n_2674_, lean_object* v_k_2675_, lean_object* v_v_2676_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_n_2674_, v___x_2677_, v_k_2675_, v_v_2676_);
return v___x_2678_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(lean_object* v_x_2680_, size_t v_x_2681_, size_t v_x_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_){
_start:
{
if (lean_obj_tag(v_x_2680_) == 0)
{
lean_object* v_es_2685_; size_t v___x_2686_; size_t v___x_2687_; lean_object* v_j_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v_es_2685_ = lean_ctor_get(v_x_2680_, 0);
v___x_2686_ = ((size_t)31ULL);
v___x_2687_ = lean_usize_land(v_x_2681_, v___x_2686_);
v_j_2688_ = lean_usize_to_nat(v___x_2687_);
v___x_2689_ = lean_array_get_size(v_es_2685_);
v___x_2690_ = lean_nat_dec_lt(v_j_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_dec(v_j_2688_);
lean_dec(v_x_2684_);
lean_dec(v_x_2683_);
return v_x_2680_;
}
else
{
lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2729_; 
lean_inc_ref(v_es_2685_);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_x_2680_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v_x_2680_, 0);
lean_dec(v_unused_2730_);
v___x_2692_ = v_x_2680_;
v_isShared_2693_ = v_isSharedCheck_2729_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v_x_2680_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2729_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_v_2694_; lean_object* v___x_2695_; lean_object* v_xs_x27_2696_; lean_object* v___y_2698_; 
v_v_2694_ = lean_array_fget(v_es_2685_, v_j_2688_);
v___x_2695_ = lean_box(0);
v_xs_x27_2696_ = lean_array_fset(v_es_2685_, v_j_2688_, v___x_2695_);
switch(lean_obj_tag(v_v_2694_))
{
case 0:
{
lean_object* v_key_2703_; lean_object* v_val_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2714_; 
v_key_2703_ = lean_ctor_get(v_v_2694_, 0);
v_val_2704_ = lean_ctor_get(v_v_2694_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_v_2694_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2706_ = v_v_2694_;
v_isShared_2707_ = v_isSharedCheck_2714_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_val_2704_);
lean_inc(v_key_2703_);
lean_dec(v_v_2694_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2714_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
uint8_t v___x_2708_; 
v___x_2708_ = l_Lean_instBEqMVarId_beq(v_x_2683_, v_key_2703_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_del_object(v___x_2706_);
v___x_2709_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2703_, v_val_2704_, v_x_2683_, v_x_2684_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
v___y_2698_ = v___x_2710_;
goto v___jp_2697_;
}
else
{
lean_object* v___x_2712_; 
lean_dec(v_val_2704_);
lean_dec(v_key_2703_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 1, v_x_2684_);
lean_ctor_set(v___x_2706_, 0, v_x_2683_);
v___x_2712_ = v___x_2706_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_x_2683_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_x_2684_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
v___y_2698_ = v___x_2712_;
goto v___jp_2697_;
}
}
}
}
case 1:
{
lean_object* v_node_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2727_; 
v_node_2715_ = lean_ctor_get(v_v_2694_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_v_2694_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2717_ = v_v_2694_;
v_isShared_2718_ = v_isSharedCheck_2727_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_node_2715_);
lean_dec(v_v_2694_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2727_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
size_t v___x_2719_; size_t v___x_2720_; size_t v___x_2721_; size_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2719_ = ((size_t)5ULL);
v___x_2720_ = lean_usize_shift_right(v_x_2681_, v___x_2719_);
v___x_2721_ = ((size_t)1ULL);
v___x_2722_ = lean_usize_add(v_x_2682_, v___x_2721_);
v___x_2723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_node_2715_, v___x_2720_, v___x_2722_, v_x_2683_, v_x_2684_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2723_);
v___x_2725_ = v___x_2717_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
v___y_2698_ = v___x_2725_;
goto v___jp_2697_;
}
}
}
default: 
{
lean_object* v___x_2728_; 
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v_x_2683_);
lean_ctor_set(v___x_2728_, 1, v_x_2684_);
v___y_2698_ = v___x_2728_;
goto v___jp_2697_;
}
}
v___jp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2699_ = lean_array_fset(v_xs_x27_2696_, v_j_2688_, v___y_2698_);
lean_dec(v_j_2688_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2699_);
v___x_2701_ = v___x_2692_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
else
{
lean_object* v_ks_2731_; lean_object* v_vs_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2750_; 
v_ks_2731_ = lean_ctor_get(v_x_2680_, 0);
v_vs_2732_ = lean_ctor_get(v_x_2680_, 1);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_x_2680_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2734_ = v_x_2680_;
v_isShared_2735_ = v_isSharedCheck_2750_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_vs_2732_);
lean_inc(v_ks_2731_);
lean_dec(v_x_2680_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2750_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_ks_2731_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_vs_2732_);
v___x_2737_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v_newNode_2738_; size_t v___x_2739_; uint8_t v___x_2740_; 
v_newNode_2738_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v___x_2737_, v_x_2683_, v_x_2684_);
v___x_2739_ = ((size_t)7ULL);
v___x_2740_ = lean_usize_dec_le(v___x_2739_, v_x_2682_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2741_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2738_);
v___x_2742_ = lean_unsigned_to_nat(4u);
v___x_2743_ = lean_nat_dec_lt(v___x_2741_, v___x_2742_);
lean_dec(v___x_2741_);
if (v___x_2743_ == 0)
{
lean_object* v_ks_2744_; lean_object* v_vs_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_ks_2744_ = lean_ctor_get(v_newNode_2738_, 0);
lean_inc_ref(v_ks_2744_);
v_vs_2745_ = lean_ctor_get(v_newNode_2738_, 1);
lean_inc_ref(v_vs_2745_);
lean_dec_ref(v_newNode_2738_);
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_2748_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_x_2682_, v_ks_2744_, v_vs_2745_, v___x_2746_, v___x_2747_);
lean_dec_ref(v_vs_2745_);
lean_dec_ref(v_ks_2744_);
return v___x_2748_;
}
else
{
return v_newNode_2738_;
}
}
else
{
return v_newNode_2738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(size_t v_depth_2751_, lean_object* v_keys_2752_, lean_object* v_vals_2753_, lean_object* v_i_2754_, lean_object* v_entries_2755_){
_start:
{
lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2756_ = lean_array_get_size(v_keys_2752_);
v___x_2757_ = lean_nat_dec_lt(v_i_2754_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_dec(v_i_2754_);
return v_entries_2755_;
}
else
{
lean_object* v_k_2758_; lean_object* v_v_2759_; uint64_t v___x_2760_; size_t v_h_2761_; size_t v___x_2762_; lean_object* v___x_2763_; size_t v___x_2764_; size_t v___x_2765_; size_t v___x_2766_; size_t v_h_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_k_2758_ = lean_array_fget_borrowed(v_keys_2752_, v_i_2754_);
v_v_2759_ = lean_array_fget_borrowed(v_vals_2753_, v_i_2754_);
v___x_2760_ = l_Lean_instHashableMVarId_hash(v_k_2758_);
v_h_2761_ = lean_uint64_to_usize(v___x_2760_);
v___x_2762_ = ((size_t)5ULL);
v___x_2763_ = lean_unsigned_to_nat(1u);
v___x_2764_ = ((size_t)1ULL);
v___x_2765_ = lean_usize_sub(v_depth_2751_, v___x_2764_);
v___x_2766_ = lean_usize_mul(v___x_2762_, v___x_2765_);
v_h_2767_ = lean_usize_shift_right(v_h_2761_, v___x_2766_);
v___x_2768_ = lean_nat_add(v_i_2754_, v___x_2763_);
lean_dec(v_i_2754_);
lean_inc(v_v_2759_);
lean_inc(v_k_2758_);
v___x_2769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_entries_2755_, v_h_2767_, v_depth_2751_, v_k_2758_, v_v_2759_);
v_i_2754_ = v___x_2768_;
v_entries_2755_ = v___x_2769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg___boxed(lean_object* v_depth_2771_, lean_object* v_keys_2772_, lean_object* v_vals_2773_, lean_object* v_i_2774_, lean_object* v_entries_2775_){
_start:
{
size_t v_depth_boxed_2776_; lean_object* v_res_2777_; 
v_depth_boxed_2776_ = lean_unbox_usize(v_depth_2771_);
lean_dec(v_depth_2771_);
v_res_2777_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_boxed_2776_, v_keys_2772_, v_vals_2773_, v_i_2774_, v_entries_2775_);
lean_dec_ref(v_vals_2773_);
lean_dec_ref(v_keys_2772_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_){
_start:
{
size_t v_x_654652__boxed_2783_; size_t v_x_654653__boxed_2784_; lean_object* v_res_2785_; 
v_x_654652__boxed_2783_ = lean_unbox_usize(v_x_2779_);
lean_dec(v_x_2779_);
v_x_654653__boxed_2784_ = lean_unbox_usize(v_x_2780_);
lean_dec(v_x_2780_);
v_res_2785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2778_, v_x_654652__boxed_2783_, v_x_654653__boxed_2784_, v_x_2781_, v_x_2782_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
uint64_t v___x_2789_; size_t v___x_2790_; size_t v___x_2791_; lean_object* v___x_2792_; 
v___x_2789_ = l_Lean_instHashableMVarId_hash(v_x_2787_);
v___x_2790_ = lean_uint64_to_usize(v___x_2789_);
v___x_2791_ = ((size_t)1ULL);
v___x_2792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2786_, v___x_2790_, v___x_2791_, v_x_2787_, v_x_2788_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(lean_object* v_mvarId_2793_, lean_object* v_val_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; lean_object* v_mctx_2798_; lean_object* v_cache_2799_; lean_object* v_zetaDeltaFVarIds_2800_; lean_object* v_postponed_2801_; lean_object* v_diag_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2832_; 
v___x_2797_ = lean_st_ref_take(v___y_2795_);
v_mctx_2798_ = lean_ctor_get(v___x_2797_, 0);
v_cache_2799_ = lean_ctor_get(v___x_2797_, 1);
v_zetaDeltaFVarIds_2800_ = lean_ctor_get(v___x_2797_, 2);
v_postponed_2801_ = lean_ctor_get(v___x_2797_, 3);
v_diag_2802_ = lean_ctor_get(v___x_2797_, 4);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2804_ = v___x_2797_;
v_isShared_2805_ = v_isSharedCheck_2832_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_diag_2802_);
lean_inc(v_postponed_2801_);
lean_inc(v_zetaDeltaFVarIds_2800_);
lean_inc(v_cache_2799_);
lean_inc(v_mctx_2798_);
lean_dec(v___x_2797_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2832_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v_depth_2806_; lean_object* v_levelAssignDepth_2807_; lean_object* v_lmvarCounter_2808_; lean_object* v_mvarCounter_2809_; lean_object* v_lDecls_2810_; lean_object* v_decls_2811_; lean_object* v_userNames_2812_; lean_object* v_lAssignment_2813_; lean_object* v_eAssignment_2814_; lean_object* v_dAssignment_2815_; lean_object* v_instanceTypedMVars_2816_; lean_object* v_synthNormMemo_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2831_; 
v_depth_2806_ = lean_ctor_get(v_mctx_2798_, 0);
v_levelAssignDepth_2807_ = lean_ctor_get(v_mctx_2798_, 1);
v_lmvarCounter_2808_ = lean_ctor_get(v_mctx_2798_, 2);
v_mvarCounter_2809_ = lean_ctor_get(v_mctx_2798_, 3);
v_lDecls_2810_ = lean_ctor_get(v_mctx_2798_, 4);
v_decls_2811_ = lean_ctor_get(v_mctx_2798_, 5);
v_userNames_2812_ = lean_ctor_get(v_mctx_2798_, 6);
v_lAssignment_2813_ = lean_ctor_get(v_mctx_2798_, 7);
v_eAssignment_2814_ = lean_ctor_get(v_mctx_2798_, 8);
v_dAssignment_2815_ = lean_ctor_get(v_mctx_2798_, 9);
v_instanceTypedMVars_2816_ = lean_ctor_get(v_mctx_2798_, 10);
v_synthNormMemo_2817_ = lean_ctor_get(v_mctx_2798_, 11);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_mctx_2798_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2819_ = v_mctx_2798_;
v_isShared_2820_ = v_isSharedCheck_2831_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_synthNormMemo_2817_);
lean_inc(v_instanceTypedMVars_2816_);
lean_inc(v_dAssignment_2815_);
lean_inc(v_eAssignment_2814_);
lean_inc(v_lAssignment_2813_);
lean_inc(v_userNames_2812_);
lean_inc(v_decls_2811_);
lean_inc(v_lDecls_2810_);
lean_inc(v_mvarCounter_2809_);
lean_inc(v_lmvarCounter_2808_);
lean_inc(v_levelAssignDepth_2807_);
lean_inc(v_depth_2806_);
lean_dec(v_mctx_2798_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2831_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2821_ = lean_box(0);
v___x_2822_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_2814_, v_mvarId_2793_, v_val_2794_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 8, v___x_2822_);
v___x_2824_ = v___x_2819_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_depth_2806_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_levelAssignDepth_2807_);
lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_lmvarCounter_2808_);
lean_ctor_set(v_reuseFailAlloc_2830_, 3, v_mvarCounter_2809_);
lean_ctor_set(v_reuseFailAlloc_2830_, 4, v_lDecls_2810_);
lean_ctor_set(v_reuseFailAlloc_2830_, 5, v_decls_2811_);
lean_ctor_set(v_reuseFailAlloc_2830_, 6, v_userNames_2812_);
lean_ctor_set(v_reuseFailAlloc_2830_, 7, v_lAssignment_2813_);
lean_ctor_set(v_reuseFailAlloc_2830_, 8, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2830_, 9, v_dAssignment_2815_);
lean_ctor_set(v_reuseFailAlloc_2830_, 10, v_instanceTypedMVars_2816_);
lean_ctor_set(v_reuseFailAlloc_2830_, 11, v_synthNormMemo_2817_);
v___x_2824_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2826_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2824_);
v___x_2826_ = v___x_2804_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_cache_2799_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_zetaDeltaFVarIds_2800_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_postponed_2801_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_diag_2802_);
v___x_2826_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_st_ref_put(v___y_2795_, v___x_2826_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2821_);
return v___x_2828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg___boxed(lean_object* v_mvarId_2833_, lean_object* v_val_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_2833_, v_val_2834_, v___y_2835_);
lean_dec(v___y_2835_);
return v_res_2837_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__1));
v___x_2842_ = l_Lean_stringToMessageData(v___x_2841_);
return v___x_2842_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4(void){
_start:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2844_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__3));
v___x_2845_ = l_Lean_stringToMessageData(v___x_2844_);
return v___x_2845_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__6));
v___x_2849_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__5));
v___x_2850_ = l_System_FilePath_join(v___x_2849_, v___x_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(lean_object* v_ctx_2851_, lean_object* v_aig_2852_, lean_object* v_goal_2853_, lean_object* v_unusedHypotheses_2854_, lean_object* v_reflectionResult_2855_, lean_object* v_satExpr_2856_, uint8_t v___x_2857_, lean_object* v___x_2858_, lean_object* v___f_2859_, lean_object* v___x_2860_, lean_object* v___f_2861_, lean_object* v___f_2862_, lean_object* v___x_2863_, lean_object* v___x_2864_, lean_object* v___f_2865_, lean_object* v_a_2866_, lean_object* v_____r_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; uint8_t v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v_a_3030_; uint8_t v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v_a_3057_; uint8_t v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; uint8_t v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; uint8_t v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; uint8_t v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v_config_3131_; lean_object* v_solver_3132_; lean_object* v_lratPath_3133_; lean_object* v_timeout_3134_; uint8_t v_trimProofs_3135_; uint8_t v_binaryProofs_3136_; uint8_t v_graphviz_3137_; uint8_t v_solverMode_3138_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v_a_3193_; uint8_t v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v_a_3223_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v_toCold_3316_; lean_object* v_ref_3317_; lean_object* v___y_3318_; 
v_config_3131_ = lean_ctor_get(v_ctx_2851_, 5);
v_solver_3132_ = lean_ctor_get(v_ctx_2851_, 3);
v_lratPath_3133_ = lean_ctor_get(v_ctx_2851_, 4);
v_timeout_3134_ = lean_ctor_get(v_config_3131_, 0);
v_trimProofs_3135_ = lean_ctor_get_uint8(v_config_3131_, sizeof(void*)*3);
v_binaryProofs_3136_ = lean_ctor_get_uint8(v_config_3131_, sizeof(void*)*3 + 1);
v_graphviz_3137_ = lean_ctor_get_uint8(v_config_3131_, sizeof(void*)*3 + 8);
v_solverMode_3138_ = lean_ctor_get_uint8(v_config_3131_, sizeof(void*)*3 + 10);
if (v_graphviz_3137_ == 0)
{
lean_object* v_toCold_3331_; lean_object* v_ref_3332_; 
lean_dec_ref(v_a_2866_);
v_toCold_3331_ = lean_ctor_get(v___y_2878_, 0);
v_ref_3332_ = lean_ctor_get(v___y_2878_, 2);
v___y_3305_ = v___y_2868_;
v___y_3306_ = v___y_2869_;
v___y_3307_ = v___y_2870_;
v___y_3308_ = v___y_2871_;
v___y_3309_ = v___y_2872_;
v___y_3310_ = v___y_2873_;
v___y_3311_ = v___y_2874_;
v___y_3312_ = v___y_2875_;
v___y_3313_ = v___y_2876_;
v___y_3314_ = v___y_2877_;
v___y_3315_ = v___y_2878_;
v_toCold_3316_ = v_toCold_3331_;
v_ref_3317_ = v_ref_3332_;
v___y_3318_ = v___y_2879_;
goto v___jp_3304_;
}
else
{
lean_object* v_toCold_3333_; lean_object* v_ref_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_toCold_3333_ = lean_ctor_get(v___y_2878_, 0);
v_ref_3334_ = lean_ctor_get(v___y_2878_, 2);
v___x_3335_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3336_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_2866_);
v___x_3337_ = l_IO_FS_writeFile(v___x_3335_, v___x_3336_);
lean_dec_ref(v___x_3336_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_dec_ref_known(v___x_3337_, 1);
v___y_3305_ = v___y_2868_;
v___y_3306_ = v___y_2869_;
v___y_3307_ = v___y_2870_;
v___y_3308_ = v___y_2871_;
v___y_3309_ = v___y_2872_;
v___y_3310_ = v___y_2873_;
v___y_3311_ = v___y_2874_;
v___y_3312_ = v___y_2875_;
v___y_3313_ = v___y_2876_;
v___y_3314_ = v___y_2877_;
v___y_3315_ = v___y_2878_;
v_toCold_3316_ = v_toCold_3333_;
v_ref_3317_ = v_ref_3334_;
v___y_3318_ = v___y_2879_;
goto v___jp_3304_;
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3349_; 
lean_dec_ref(v___f_2865_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___f_2862_);
lean_dec_ref(v___f_2861_);
lean_dec_ref(v___f_2859_);
lean_dec_ref(v___x_2858_);
lean_dec_ref(v_satExpr_2856_);
lean_dec_ref(v_reflectionResult_2855_);
lean_dec_ref(v_unusedHypotheses_2854_);
lean_dec(v_goal_2853_);
lean_dec_ref(v_aig_2852_);
lean_dec_ref(v_ctx_2851_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3349_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3349_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3342_ = lean_io_error_to_string(v_a_3338_);
v___x_3343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
v___x_3344_ = l_Lean_MessageData_ofFormat(v___x_3343_);
lean_inc(v_ref_3334_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_ref_3334_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3345_);
v___x_3347_ = v___x_3340_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
v___jp_2881_:
{
lean_object* v___x_2894_; 
lean_inc_ref(v___y_2882_);
v___x_2894_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_2882_, v_ctx_2851_, v_reflectionResult_2855_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_2856_, v_a_2895_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2906_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_2853_, v_a_2897_, v___y_2891_);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v___x_2898_, 0);
lean_dec(v_unused_2907_);
v___x_2900_ = v___x_2898_;
v_isShared_2901_ = v_isSharedCheck_2906_;
goto v_resetjp_2899_;
}
else
{
lean_dec(v___x_2898_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2906_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___y_2882_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2902_);
v___x_2904_ = v___x_2900_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v___y_2882_);
lean_dec(v_goal_2853_);
v_a_2908_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2896_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2896_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v___y_2882_);
lean_dec_ref(v_satExpr_2856_);
lean_dec(v_goal_2853_);
v_a_2916_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2894_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2894_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
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
v___jp_2924_:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_2926_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2942_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2942_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2942_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2932_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_2852_, v___y_2925_, v_a_2928_);
lean_dec(v_a_2928_);
lean_dec_ref(v___y_2925_);
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = lean_array_get_size(v___x_2932_);
v___x_2935_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_2932_, v___x_2933_, v___x_2934_);
lean_dec_ref(v___x_2932_);
v___x_2936_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_2937_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2937_, 0, v_goal_2853_);
lean_ctor_set(v___x_2937_, 1, v_unusedHypotheses_2854_);
lean_ctor_set(v___x_2937_, 2, v___x_2935_);
lean_ctor_set(v___x_2937_, 3, v___x_2936_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2938_);
v___x_2940_ = v___x_2930_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v___y_2925_);
lean_dec_ref(v_unusedHypotheses_2854_);
lean_dec(v_goal_2853_);
lean_dec_ref(v_aig_2852_);
v_a_2943_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2927_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2927_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
v___jp_2951_:
{
if (lean_obj_tag(v___y_2964_) == 0)
{
lean_object* v_a_2965_; 
v_a_2965_ = lean_ctor_get(v___y_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___y_2964_, 1);
if (lean_obj_tag(v_a_2965_) == 0)
{
lean_object* v_toCold_2966_; lean_object* v_options_2967_; uint8_t v_hasTrace_2968_; 
lean_dec_ref(v_satExpr_2856_);
lean_dec_ref(v_reflectionResult_2855_);
lean_dec_ref(v_ctx_2851_);
v_toCold_2966_ = lean_ctor_get(v___y_2954_, 0);
v_options_2967_ = lean_ctor_get(v_toCold_2966_, 2);
v_hasTrace_2968_ = lean_ctor_get_uint8(v_options_2967_, sizeof(void*)*1);
if (v_hasTrace_2968_ == 0)
{
lean_object* v_a_2969_; 
lean_dec(v___y_2956_);
v_a_2969_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v_a_2965_, 1);
v___y_2925_ = v_a_2969_;
v___y_2926_ = v___y_2955_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_2970_; lean_object* v_inheritedTraceOptions_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v_a_2970_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v_a_2965_, 1);
v_inheritedTraceOptions_2971_ = lean_ctor_get(v_toCold_2966_, 11);
v___x_2972_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2956_);
v___x_2973_ = l_Lean_Name_append(v___x_2972_, v___y_2956_);
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2971_, v_options_2967_, v___x_2973_);
lean_dec(v___x_2973_);
if (v___x_2974_ == 0)
{
lean_dec(v___y_2956_);
v___y_2925_ = v_a_2970_;
v___y_2926_ = v___y_2955_;
goto v___jp_2924_;
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_2976_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2956_, v___x_2975_, v___y_2960_, v___y_2959_, v___y_2954_, v___y_2962_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_dec_ref_known(v___x_2976_, 1);
v___y_2925_ = v_a_2970_;
v___y_2926_ = v___y_2955_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v_a_2970_);
lean_dec_ref(v_unusedHypotheses_2854_);
lean_dec(v_goal_2853_);
lean_dec_ref(v_aig_2852_);
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2976_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2976_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2985_; lean_object* v_options_2986_; uint8_t v_hasTrace_2987_; 
lean_dec_ref(v_unusedHypotheses_2854_);
lean_dec_ref(v_aig_2852_);
v_toCold_2985_ = lean_ctor_get(v___y_2954_, 0);
v_options_2986_ = lean_ctor_get(v_toCold_2985_, 2);
v_hasTrace_2987_ = lean_ctor_get_uint8(v_options_2986_, sizeof(void*)*1);
if (v_hasTrace_2987_ == 0)
{
lean_object* v_a_2988_; 
lean_dec(v___y_2956_);
v_a_2988_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v_a_2965_, 1);
v___y_2882_ = v_a_2988_;
v___y_2883_ = v___y_2957_;
v___y_2884_ = v___y_2955_;
v___y_2885_ = v___y_2958_;
v___y_2886_ = v___y_2961_;
v___y_2887_ = v___y_2952_;
v___y_2888_ = v___y_2963_;
v___y_2889_ = v___y_2953_;
v___y_2890_ = v___y_2960_;
v___y_2891_ = v___y_2959_;
v___y_2892_ = v___y_2954_;
v___y_2893_ = v___y_2962_;
goto v___jp_2881_;
}
else
{
lean_object* v_a_2989_; lean_object* v_inheritedTraceOptions_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v_a_2989_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v_a_2965_, 1);
v_inheritedTraceOptions_2990_ = lean_ctor_get(v_toCold_2985_, 11);
v___x_2991_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_2956_);
v___x_2992_ = l_Lean_Name_append(v___x_2991_, v___y_2956_);
v___x_2993_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2990_, v_options_2986_, v___x_2992_);
lean_dec(v___x_2992_);
if (v___x_2993_ == 0)
{
lean_dec(v___y_2956_);
v___y_2882_ = v_a_2989_;
v___y_2883_ = v___y_2957_;
v___y_2884_ = v___y_2955_;
v___y_2885_ = v___y_2958_;
v___y_2886_ = v___y_2961_;
v___y_2887_ = v___y_2952_;
v___y_2888_ = v___y_2963_;
v___y_2889_ = v___y_2953_;
v___y_2890_ = v___y_2960_;
v___y_2891_ = v___y_2959_;
v___y_2892_ = v___y_2954_;
v___y_2893_ = v___y_2962_;
goto v___jp_2881_;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_2995_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2956_, v___x_2994_, v___y_2960_, v___y_2959_, v___y_2954_, v___y_2962_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec_ref_known(v___x_2995_, 1);
v___y_2882_ = v_a_2989_;
v___y_2883_ = v___y_2957_;
v___y_2884_ = v___y_2955_;
v___y_2885_ = v___y_2958_;
v___y_2886_ = v___y_2961_;
v___y_2887_ = v___y_2952_;
v___y_2888_ = v___y_2963_;
v___y_2889_ = v___y_2953_;
v___y_2890_ = v___y_2960_;
v___y_2891_ = v___y_2959_;
v___y_2892_ = v___y_2954_;
v___y_2893_ = v___y_2962_;
goto v___jp_2881_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_a_2989_);
lean_dec_ref(v_satExpr_2856_);
lean_dec_ref(v_reflectionResult_2855_);
lean_dec(v_goal_2853_);
lean_dec_ref(v_ctx_2851_);
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec(v___y_2956_);
lean_dec_ref(v_satExpr_2856_);
lean_dec_ref(v_reflectionResult_2855_);
lean_dec_ref(v_unusedHypotheses_2854_);
lean_dec(v_goal_2853_);
lean_dec_ref(v_aig_2852_);
lean_dec_ref(v_ctx_2851_);
v_a_3004_ = lean_ctor_get(v___y_2964_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___y_2964_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___y_2964_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___y_2964_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
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
return v___x_3009_;
}
}
}
}
v___jp_3012_:
{
lean_object* v___x_3031_; double v___x_3032_; double v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3031_ = lean_io_get_num_heartbeats();
v___x_3032_ = lean_float_of_nat(v___y_3025_);
v___x_3033_ = lean_float_of_nat(v___x_3031_);
v___x_3034_ = lean_box_float(v___x_3032_);
v___x_3035_ = lean_box_float(v___x_3033_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_a_3030_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
lean_inc(v___y_3017_);
v___x_3038_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3017_, v___x_2857_, v___x_2858_, v___y_3022_, v___y_3013_, v___y_3024_, v___f_2859_, v___x_3037_, v___y_3028_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3026_, v___y_3014_, v___y_3029_, v___y_3015_, v___y_3023_, v___y_3021_, v___y_3016_, v___y_3027_);
v___y_2952_ = v___y_3014_;
v___y_2953_ = v___y_3015_;
v___y_2954_ = v___y_3016_;
v___y_2955_ = v___y_3019_;
v___y_2956_ = v___y_3017_;
v___y_2957_ = v___y_3018_;
v___y_2958_ = v___y_3020_;
v___y_2959_ = v___y_3021_;
v___y_2960_ = v___y_3023_;
v___y_2961_ = v___y_3026_;
v___y_2962_ = v___y_3027_;
v___y_2963_ = v___y_3029_;
v___y_2964_ = v___x_3038_;
goto v___jp_2951_;
}
v___jp_3039_:
{
lean_object* v___x_3058_; double v___x_3059_; double v___x_3060_; double v___x_3061_; double v___x_3062_; double v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3058_ = lean_io_mono_nanos_now();
v___x_3059_ = lean_float_of_nat(v___y_3051_);
v___x_3060_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3061_ = lean_float_div(v___x_3059_, v___x_3060_);
v___x_3062_ = lean_float_of_nat(v___x_3058_);
v___x_3063_ = lean_float_div(v___x_3062_, v___x_3060_);
v___x_3064_ = lean_box_float(v___x_3061_);
v___x_3065_ = lean_box_float(v___x_3063_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_a_3057_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
lean_inc(v___y_3044_);
v___x_3068_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3044_, v___x_2857_, v___x_2858_, v___y_3049_, v___y_3040_, v___y_3052_, v___f_2859_, v___x_3067_, v___y_3055_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3053_, v___y_3041_, v___y_3056_, v___y_3042_, v___y_3050_, v___y_3048_, v___y_3043_, v___y_3054_);
v___y_2952_ = v___y_3041_;
v___y_2953_ = v___y_3042_;
v___y_2954_ = v___y_3043_;
v___y_2955_ = v___y_3046_;
v___y_2956_ = v___y_3044_;
v___y_2957_ = v___y_3045_;
v___y_2958_ = v___y_3047_;
v___y_2959_ = v___y_3048_;
v___y_2960_ = v___y_3050_;
v___y_2961_ = v___y_3053_;
v___y_2962_ = v___y_3054_;
v___y_2963_ = v___y_3056_;
v___y_2964_ = v___x_3068_;
goto v___jp_2951_;
}
v___jp_3069_:
{
lean_object* v___x_3092_; lean_object* v_a_3093_; uint8_t v___x_3094_; 
v___x_3092_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3089_);
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref(v___x_3092_);
v___x_3094_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3082_, v___x_2860_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = lean_io_mono_nanos_now();
v___x_3096_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3085_, v___y_3077_, v___y_3083_, v___y_3078_, v___y_3080_, v___y_3084_, v___y_3087_, v___y_3076_, v___y_3089_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 1);
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
v___y_3040_ = v___y_3070_;
v___y_3041_ = v___y_3071_;
v___y_3042_ = v___y_3072_;
v___y_3043_ = v___y_3076_;
v___y_3044_ = v___y_3073_;
v___y_3045_ = v___y_3074_;
v___y_3046_ = v___y_3075_;
v___y_3047_ = v___y_3079_;
v___y_3048_ = v___y_3081_;
v___y_3049_ = v___y_3082_;
v___y_3050_ = v___y_3086_;
v___y_3051_ = v___x_3095_;
v___y_3052_ = v_a_3093_;
v___y_3053_ = v___y_3088_;
v___y_3054_ = v___y_3089_;
v___y_3055_ = v___y_3090_;
v___y_3056_ = v___y_3091_;
v_a_3057_ = v___x_3102_;
goto v___jp_3039_;
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_a_3105_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3096_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3096_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set_tag(v___x_3107_, 0);
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
v___y_3040_ = v___y_3070_;
v___y_3041_ = v___y_3071_;
v___y_3042_ = v___y_3072_;
v___y_3043_ = v___y_3076_;
v___y_3044_ = v___y_3073_;
v___y_3045_ = v___y_3074_;
v___y_3046_ = v___y_3075_;
v___y_3047_ = v___y_3079_;
v___y_3048_ = v___y_3081_;
v___y_3049_ = v___y_3082_;
v___y_3050_ = v___y_3086_;
v___y_3051_ = v___x_3095_;
v___y_3052_ = v_a_3093_;
v___y_3053_ = v___y_3088_;
v___y_3054_ = v___y_3089_;
v___y_3055_ = v___y_3090_;
v___y_3056_ = v___y_3091_;
v_a_3057_ = v___x_3110_;
goto v___jp_3039_;
}
}
}
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_io_get_num_heartbeats();
v___x_3114_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3085_, v___y_3077_, v___y_3083_, v___y_3078_, v___y_3080_, v___y_3084_, v___y_3087_, v___y_3076_, v___y_3089_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set_tag(v___x_3117_, 1);
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
v___y_3013_ = v___y_3070_;
v___y_3014_ = v___y_3071_;
v___y_3015_ = v___y_3072_;
v___y_3016_ = v___y_3076_;
v___y_3017_ = v___y_3073_;
v___y_3018_ = v___y_3074_;
v___y_3019_ = v___y_3075_;
v___y_3020_ = v___y_3079_;
v___y_3021_ = v___y_3081_;
v___y_3022_ = v___y_3082_;
v___y_3023_ = v___y_3086_;
v___y_3024_ = v_a_3093_;
v___y_3025_ = v___x_3113_;
v___y_3026_ = v___y_3088_;
v___y_3027_ = v___y_3089_;
v___y_3028_ = v___y_3090_;
v___y_3029_ = v___y_3091_;
v_a_3030_ = v___x_3120_;
goto v___jp_3012_;
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
v_a_3123_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3114_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3114_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 0);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
v___y_3013_ = v___y_3070_;
v___y_3014_ = v___y_3071_;
v___y_3015_ = v___y_3072_;
v___y_3016_ = v___y_3076_;
v___y_3017_ = v___y_3073_;
v___y_3018_ = v___y_3074_;
v___y_3019_ = v___y_3075_;
v___y_3020_ = v___y_3079_;
v___y_3021_ = v___y_3081_;
v___y_3022_ = v___y_3082_;
v___y_3023_ = v___y_3086_;
v___y_3024_ = v_a_3093_;
v___y_3025_ = v___x_3113_;
v___y_3026_ = v___y_3088_;
v___y_3027_ = v___y_3089_;
v___y_3028_ = v___y_3090_;
v___y_3029_ = v___y_3091_;
v_a_3030_ = v___x_3128_;
goto v___jp_3012_;
}
}
}
}
}
v___jp_3139_:
{
if (lean_obj_tag(v___y_3153_) == 0)
{
lean_object* v_toCold_3154_; lean_object* v_options_3155_; uint8_t v_hasTrace_3156_; 
v_toCold_3154_ = lean_ctor_get(v___y_3142_, 0);
v_options_3155_ = lean_ctor_get(v_toCold_3154_, 2);
v_hasTrace_3156_ = lean_ctor_get_uint8(v_options_3155_, sizeof(void*)*1);
if (v_hasTrace_3156_ == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3158_; 
lean_dec_ref(v___f_2859_);
lean_dec_ref(v___x_2858_);
v_a_3157_ = lean_ctor_get(v___y_3153_, 0);
lean_inc(v_a_3157_);
lean_dec_ref_known(v___y_3153_, 1);
lean_inc(v_timeout_3134_);
lean_inc_ref(v_lratPath_3133_);
lean_inc_ref(v_solver_3132_);
v___x_3158_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3157_, v_solver_3132_, v_lratPath_3133_, v_trimProofs_3135_, v_timeout_3134_, v_binaryProofs_3136_, v_solverMode_3138_, v___y_3142_, v___y_3150_);
v___y_2952_ = v___y_3140_;
v___y_2953_ = v___y_3141_;
v___y_2954_ = v___y_3142_;
v___y_2955_ = v___y_3143_;
v___y_2956_ = v___y_3144_;
v___y_2957_ = v___y_3145_;
v___y_2958_ = v___y_3146_;
v___y_2959_ = v___y_3147_;
v___y_2960_ = v___y_3148_;
v___y_2961_ = v___y_3149_;
v___y_2962_ = v___y_3150_;
v___y_2963_ = v___y_3152_;
v___y_2964_ = v___x_3158_;
goto v___jp_2951_;
}
else
{
lean_object* v_a_3159_; lean_object* v_inheritedTraceOptions_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v_a_3159_ = lean_ctor_get(v___y_3153_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___y_3153_, 1);
v_inheritedTraceOptions_3160_ = lean_ctor_get(v_toCold_3154_, 11);
v___x_3161_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3144_);
v___x_3162_ = l_Lean_Name_append(v___x_3161_, v___y_3144_);
v___x_3163_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3160_, v_options_3155_, v___x_3162_);
lean_dec(v___x_3162_);
if (v___x_3163_ == 0)
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = l_Lean_trace_profiler;
v___x_3165_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3155_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; 
lean_dec_ref(v___f_2859_);
lean_dec_ref(v___x_2858_);
lean_inc(v_timeout_3134_);
lean_inc_ref(v_lratPath_3133_);
lean_inc_ref(v_solver_3132_);
v___x_3166_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3159_, v_solver_3132_, v_lratPath_3133_, v_trimProofs_3135_, v_timeout_3134_, v_binaryProofs_3136_, v_solverMode_3138_, v___y_3142_, v___y_3150_);
v___y_2952_ = v___y_3140_;
v___y_2953_ = v___y_3141_;
v___y_2954_ = v___y_3142_;
v___y_2955_ = v___y_3143_;
v___y_2956_ = v___y_3144_;
v___y_2957_ = v___y_3145_;
v___y_2958_ = v___y_3146_;
v___y_2959_ = v___y_3147_;
v___y_2960_ = v___y_3148_;
v___y_2961_ = v___y_3149_;
v___y_2962_ = v___y_3150_;
v___y_2963_ = v___y_3152_;
v___y_2964_ = v___x_3166_;
goto v___jp_2951_;
}
else
{
lean_inc_ref(v_lratPath_3133_);
lean_inc(v_timeout_3134_);
lean_inc_ref(v_solver_3132_);
v___y_3070_ = v___x_3163_;
v___y_3071_ = v___y_3140_;
v___y_3072_ = v___y_3141_;
v___y_3073_ = v___y_3144_;
v___y_3074_ = v___y_3145_;
v___y_3075_ = v___y_3143_;
v___y_3076_ = v___y_3142_;
v___y_3077_ = v_solver_3132_;
v___y_3078_ = v_trimProofs_3135_;
v___y_3079_ = v___y_3146_;
v___y_3080_ = v_timeout_3134_;
v___y_3081_ = v___y_3147_;
v___y_3082_ = v_options_3155_;
v___y_3083_ = v_lratPath_3133_;
v___y_3084_ = v_binaryProofs_3136_;
v___y_3085_ = v_a_3159_;
v___y_3086_ = v___y_3148_;
v___y_3087_ = v_solverMode_3138_;
v___y_3088_ = v___y_3149_;
v___y_3089_ = v___y_3150_;
v___y_3090_ = v___y_3151_;
v___y_3091_ = v___y_3152_;
goto v___jp_3069_;
}
}
else
{
lean_inc_ref(v_lratPath_3133_);
lean_inc(v_timeout_3134_);
lean_inc_ref(v_solver_3132_);
v___y_3070_ = v___x_3163_;
v___y_3071_ = v___y_3140_;
v___y_3072_ = v___y_3141_;
v___y_3073_ = v___y_3144_;
v___y_3074_ = v___y_3145_;
v___y_3075_ = v___y_3143_;
v___y_3076_ = v___y_3142_;
v___y_3077_ = v_solver_3132_;
v___y_3078_ = v_trimProofs_3135_;
v___y_3079_ = v___y_3146_;
v___y_3080_ = v_timeout_3134_;
v___y_3081_ = v___y_3147_;
v___y_3082_ = v_options_3155_;
v___y_3083_ = v_lratPath_3133_;
v___y_3084_ = v_binaryProofs_3136_;
v___y_3085_ = v_a_3159_;
v___y_3086_ = v___y_3148_;
v___y_3087_ = v_solverMode_3138_;
v___y_3088_ = v___y_3149_;
v___y_3089_ = v___y_3150_;
v___y_3090_ = v___y_3151_;
v___y_3091_ = v___y_3152_;
goto v___jp_3069_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v___y_3144_);
lean_dec_ref(v___f_2859_);
lean_dec_ref(v___x_2858_);
lean_dec_ref(v_satExpr_2856_);
lean_dec_ref(v_reflectionResult_2855_);
lean_dec_ref(v_unusedHypotheses_2854_);
lean_dec(v_goal_2853_);
lean_dec_ref(v_aig_2852_);
lean_dec_ref(v_ctx_2851_);
v_a_3167_ = lean_ctor_get(v___y_3153_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___y_3153_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___y_3153_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___y_3153_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
v___jp_3175_:
{
lean_object* v___x_3194_; double v___x_3195_; double v___x_3196_; double v___x_3197_; double v___x_3198_; double v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3194_ = lean_io_mono_nanos_now();
v___x_3195_ = lean_float_of_nat(v___y_3187_);
v___x_3196_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3197_ = lean_float_div(v___x_3195_, v___x_3196_);
v___x_3198_ = lean_float_of_nat(v___x_3194_);
v___x_3199_ = lean_float_div(v___x_3198_, v___x_3196_);
v___x_3200_ = lean_box_float(v___x_3197_);
v___x_3201_ = lean_box_float(v___x_3199_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3200_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v_a_3193_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
lean_inc_ref(v___x_2858_);
lean_inc(v___y_3180_);
v___x_3204_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3180_, v___x_2857_, v___x_2858_, v___y_3188_, v___y_3176_, v___y_3185_, v___f_2861_, v___x_3203_, v___y_3191_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3189_, v___y_3177_, v___y_3192_, v___y_3178_, v___y_3186_, v___y_3184_, v___y_3179_, v___y_3190_);
v___y_3140_ = v___y_3177_;
v___y_3141_ = v___y_3178_;
v___y_3142_ = v___y_3179_;
v___y_3143_ = v___y_3182_;
v___y_3144_ = v___y_3180_;
v___y_3145_ = v___y_3181_;
v___y_3146_ = v___y_3183_;
v___y_3147_ = v___y_3184_;
v___y_3148_ = v___y_3186_;
v___y_3149_ = v___y_3189_;
v___y_3150_ = v___y_3190_;
v___y_3151_ = v___y_3191_;
v___y_3152_ = v___y_3192_;
v___y_3153_ = v___x_3204_;
goto v___jp_3139_;
}
v___jp_3205_:
{
lean_object* v___x_3224_; double v___x_3225_; double v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3224_ = lean_io_get_num_heartbeats();
v___x_3225_ = lean_float_of_nat(v___y_3216_);
v___x_3226_ = lean_float_of_nat(v___x_3224_);
v___x_3227_ = lean_box_float(v___x_3225_);
v___x_3228_ = lean_box_float(v___x_3226_);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3227_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_a_3223_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
lean_inc_ref(v___x_2858_);
lean_inc(v___y_3210_);
v___x_3231_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3210_, v___x_2857_, v___x_2858_, v___y_3218_, v___y_3206_, v___y_3215_, v___f_2861_, v___x_3230_, v___y_3221_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3219_, v___y_3207_, v___y_3222_, v___y_3208_, v___y_3217_, v___y_3214_, v___y_3209_, v___y_3220_);
v___y_3140_ = v___y_3207_;
v___y_3141_ = v___y_3208_;
v___y_3142_ = v___y_3209_;
v___y_3143_ = v___y_3212_;
v___y_3144_ = v___y_3210_;
v___y_3145_ = v___y_3211_;
v___y_3146_ = v___y_3213_;
v___y_3147_ = v___y_3214_;
v___y_3148_ = v___y_3217_;
v___y_3149_ = v___y_3219_;
v___y_3150_ = v___y_3220_;
v___y_3151_ = v___y_3221_;
v___y_3152_ = v___y_3222_;
v___y_3153_ = v___x_3231_;
goto v___jp_3139_;
}
v___jp_3232_:
{
lean_object* v___x_3249_; lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3303_; 
v___x_3249_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3246_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3303_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3303_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
uint8_t v___x_3254_; 
v___x_3254_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3244_, v___x_2860_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = lean_io_mono_nanos_now();
v___x_3256_ = l_IO_lazyPure___redArg(v___f_2862_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_del_object(v___x_3252_);
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
lean_ctor_set_tag(v___x_3259_, 1);
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
v___y_3176_ = v___y_3233_;
v___y_3177_ = v___y_3234_;
v___y_3178_ = v___y_3235_;
v___y_3179_ = v___y_3239_;
v___y_3180_ = v___y_3236_;
v___y_3181_ = v___y_3237_;
v___y_3182_ = v___y_3238_;
v___y_3183_ = v___y_3240_;
v___y_3184_ = v___y_3241_;
v___y_3185_ = v_a_3250_;
v___y_3186_ = v___y_3243_;
v___y_3187_ = v___x_3255_;
v___y_3188_ = v___y_3244_;
v___y_3189_ = v___y_3245_;
v___y_3190_ = v___y_3246_;
v___y_3191_ = v___y_3247_;
v___y_3192_ = v___y_3248_;
v_a_3193_ = v___x_3262_;
goto v___jp_3175_;
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3278_; 
v_a_3265_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3267_ = v___x_3256_;
v_isShared_3268_ = v_isSharedCheck_3278_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3256_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3278_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v___x_3271_; 
v___x_3269_ = lean_io_error_to_string(v_a_3265_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 3);
lean_ctor_set(v___x_3267_, 0, v___x_3269_);
v___x_3271_ = v___x_3267_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3272_ = l_Lean_MessageData_ofFormat(v___x_3271_);
lean_inc(v___y_3242_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___y_3242_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3273_);
v___x_3275_ = v___x_3252_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
v___y_3176_ = v___y_3233_;
v___y_3177_ = v___y_3234_;
v___y_3178_ = v___y_3235_;
v___y_3179_ = v___y_3239_;
v___y_3180_ = v___y_3236_;
v___y_3181_ = v___y_3237_;
v___y_3182_ = v___y_3238_;
v___y_3183_ = v___y_3240_;
v___y_3184_ = v___y_3241_;
v___y_3185_ = v_a_3250_;
v___y_3186_ = v___y_3243_;
v___y_3187_ = v___x_3255_;
v___y_3188_ = v___y_3244_;
v___y_3189_ = v___y_3245_;
v___y_3190_ = v___y_3246_;
v___y_3191_ = v___y_3247_;
v___y_3192_ = v___y_3248_;
v_a_3193_ = v___x_3275_;
goto v___jp_3175_;
}
}
}
}
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_io_get_num_heartbeats();
v___x_3280_ = l_IO_lazyPure___redArg(v___f_2862_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_del_object(v___x_3252_);
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 1);
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3239_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v___y_3237_;
v___y_3212_ = v___y_3238_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v_a_3250_;
v___y_3216_ = v___x_3279_;
v___y_3217_ = v___y_3243_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3245_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3247_;
v___y_3222_ = v___y_3248_;
v_a_3223_ = v___x_3286_;
goto v___jp_3205_;
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3302_; 
v_a_3289_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3291_ = v___x_3280_;
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3280_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3302_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = lean_io_error_to_string(v_a_3289_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 3);
lean_ctor_set(v___x_3291_, 0, v___x_3293_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3296_ = l_Lean_MessageData_ofFormat(v___x_3295_);
lean_inc(v___y_3242_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___y_3242_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3297_);
v___x_3299_ = v___x_3252_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3239_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v___y_3237_;
v___y_3212_ = v___y_3238_;
v___y_3213_ = v___y_3240_;
v___y_3214_ = v___y_3241_;
v___y_3215_ = v_a_3250_;
v___y_3216_ = v___x_3279_;
v___y_3217_ = v___y_3243_;
v___y_3218_ = v___y_3244_;
v___y_3219_ = v___y_3245_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3247_;
v___y_3222_ = v___y_3248_;
v_a_3223_ = v___x_3299_;
goto v___jp_3205_;
}
}
}
}
}
}
}
v___jp_3304_:
{
lean_object* v_options_3319_; lean_object* v_inheritedTraceOptions_3320_; uint8_t v_hasTrace_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_options_3319_ = lean_ctor_get(v_toCold_3316_, 2);
v_inheritedTraceOptions_3320_ = lean_ctor_get(v_toCold_3316_, 11);
v_hasTrace_3321_ = lean_ctor_get_uint8(v_options_3319_, sizeof(void*)*1);
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3323_ = l_Lean_Name_mkStr3(v___x_2863_, v___x_2864_, v___x_3322_);
if (v_hasTrace_3321_ == 0)
{
lean_object* v___x_3324_; 
lean_dec_ref(v___f_2862_);
lean_dec_ref(v___f_2861_);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3315_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3306_);
v___x_3324_ = lean_apply_12(v___f_2865_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3318_, lean_box(0));
v___y_3140_ = v___y_3310_;
v___y_3141_ = v___y_3312_;
v___y_3142_ = v___y_3315_;
v___y_3143_ = v___y_3307_;
v___y_3144_ = v___x_3323_;
v___y_3145_ = v___y_3306_;
v___y_3146_ = v___y_3308_;
v___y_3147_ = v___y_3314_;
v___y_3148_ = v___y_3313_;
v___y_3149_ = v___y_3309_;
v___y_3150_ = v___y_3318_;
v___y_3151_ = v___y_3305_;
v___y_3152_ = v___y_3311_;
v___y_3153_ = v___x_3324_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3325_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3323_);
v___x_3326_ = l_Lean_Name_append(v___x_3325_, v___x_3323_);
v___x_3327_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3320_, v_options_3319_, v___x_3326_);
lean_dec(v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3328_ = l_Lean_trace_profiler;
v___x_3329_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3319_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_dec_ref(v___f_2862_);
lean_dec_ref(v___f_2861_);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3315_);
lean_inc(v___y_3314_);
lean_inc_ref(v___y_3313_);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3306_);
v___x_3330_ = lean_apply_12(v___f_2865_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3318_, lean_box(0));
v___y_3140_ = v___y_3310_;
v___y_3141_ = v___y_3312_;
v___y_3142_ = v___y_3315_;
v___y_3143_ = v___y_3307_;
v___y_3144_ = v___x_3323_;
v___y_3145_ = v___y_3306_;
v___y_3146_ = v___y_3308_;
v___y_3147_ = v___y_3314_;
v___y_3148_ = v___y_3313_;
v___y_3149_ = v___y_3309_;
v___y_3150_ = v___y_3318_;
v___y_3151_ = v___y_3305_;
v___y_3152_ = v___y_3311_;
v___y_3153_ = v___x_3330_;
goto v___jp_3139_;
}
else
{
lean_dec_ref(v___f_2865_);
v___y_3233_ = v___x_3327_;
v___y_3234_ = v___y_3310_;
v___y_3235_ = v___y_3312_;
v___y_3236_ = v___x_3323_;
v___y_3237_ = v___y_3306_;
v___y_3238_ = v___y_3307_;
v___y_3239_ = v___y_3315_;
v___y_3240_ = v___y_3308_;
v___y_3241_ = v___y_3314_;
v___y_3242_ = v_ref_3317_;
v___y_3243_ = v___y_3313_;
v___y_3244_ = v_options_3319_;
v___y_3245_ = v___y_3309_;
v___y_3246_ = v___y_3318_;
v___y_3247_ = v___y_3305_;
v___y_3248_ = v___y_3311_;
goto v___jp_3232_;
}
}
else
{
lean_dec_ref(v___f_2865_);
v___y_3233_ = v___x_3327_;
v___y_3234_ = v___y_3310_;
v___y_3235_ = v___y_3312_;
v___y_3236_ = v___x_3323_;
v___y_3237_ = v___y_3306_;
v___y_3238_ = v___y_3307_;
v___y_3239_ = v___y_3315_;
v___y_3240_ = v___y_3308_;
v___y_3241_ = v___y_3314_;
v___y_3242_ = v_ref_3317_;
v___y_3243_ = v___y_3313_;
v___y_3244_ = v_options_3319_;
v___y_3245_ = v___y_3309_;
v___y_3246_ = v___y_3318_;
v___y_3247_ = v___y_3305_;
v___y_3248_ = v___y_3311_;
goto v___jp_3232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___boxed(lean_object** _args){
lean_object* v_ctx_3350_ = _args[0];
lean_object* v_aig_3351_ = _args[1];
lean_object* v_goal_3352_ = _args[2];
lean_object* v_unusedHypotheses_3353_ = _args[3];
lean_object* v_reflectionResult_3354_ = _args[4];
lean_object* v_satExpr_3355_ = _args[5];
lean_object* v___x_3356_ = _args[6];
lean_object* v___x_3357_ = _args[7];
lean_object* v___f_3358_ = _args[8];
lean_object* v___x_3359_ = _args[9];
lean_object* v___f_3360_ = _args[10];
lean_object* v___f_3361_ = _args[11];
lean_object* v___x_3362_ = _args[12];
lean_object* v___x_3363_ = _args[13];
lean_object* v___f_3364_ = _args[14];
lean_object* v_a_3365_ = _args[15];
lean_object* v_____r_3366_ = _args[16];
lean_object* v___y_3367_ = _args[17];
lean_object* v___y_3368_ = _args[18];
lean_object* v___y_3369_ = _args[19];
lean_object* v___y_3370_ = _args[20];
lean_object* v___y_3371_ = _args[21];
lean_object* v___y_3372_ = _args[22];
lean_object* v___y_3373_ = _args[23];
lean_object* v___y_3374_ = _args[24];
lean_object* v___y_3375_ = _args[25];
lean_object* v___y_3376_ = _args[26];
lean_object* v___y_3377_ = _args[27];
lean_object* v___y_3378_ = _args[28];
lean_object* v___y_3379_ = _args[29];
_start:
{
uint8_t v___x_654904__boxed_3380_; lean_object* v_res_3381_; 
v___x_654904__boxed_3380_ = lean_unbox(v___x_3356_);
v_res_3381_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_3350_, v_aig_3351_, v_goal_3352_, v_unusedHypotheses_3353_, v_reflectionResult_3354_, v_satExpr_3355_, v___x_654904__boxed_3380_, v___x_3357_, v___f_3358_, v___x_3359_, v___f_3360_, v___f_3361_, v___x_3362_, v___x_3363_, v___f_3364_, v_a_3365_, v_____r_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___x_3359_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(lean_object* v_ctx_3382_, lean_object* v_aig_3383_, lean_object* v_goal_3384_, lean_object* v_unusedHypotheses_3385_, lean_object* v_reflectionResult_3386_, lean_object* v_satExpr_3387_, uint8_t v___x_3388_, lean_object* v___x_3389_, lean_object* v___f_3390_, lean_object* v___x_3391_, lean_object* v___f_3392_, lean_object* v___f_3393_, lean_object* v___x_3394_, lean_object* v___x_3395_, lean_object* v___f_3396_, lean_object* v_a_3397_, lean_object* v_____r_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; uint8_t v___y_3560_; lean_object* v_a_3561_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; uint8_t v___y_3587_; lean_object* v_a_3588_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; lean_object* v___y_3608_; uint8_t v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; uint8_t v___y_3622_; lean_object* v_config_3662_; lean_object* v_solver_3663_; lean_object* v_lratPath_3664_; lean_object* v_timeout_3665_; uint8_t v_trimProofs_3666_; uint8_t v_binaryProofs_3667_; uint8_t v_graphviz_3668_; uint8_t v_solverMode_3669_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; uint8_t v___y_3722_; lean_object* v___y_3723_; lean_object* v_a_3724_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; uint8_t v___y_3752_; lean_object* v___y_3753_; lean_object* v_a_3754_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; uint8_t v___y_3779_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v_toCold_3847_; lean_object* v_ref_3848_; lean_object* v___y_3849_; 
v_config_3662_ = lean_ctor_get(v_ctx_3382_, 5);
v_solver_3663_ = lean_ctor_get(v_ctx_3382_, 3);
v_lratPath_3664_ = lean_ctor_get(v_ctx_3382_, 4);
v_timeout_3665_ = lean_ctor_get(v_config_3662_, 0);
v_trimProofs_3666_ = lean_ctor_get_uint8(v_config_3662_, sizeof(void*)*3);
v_binaryProofs_3667_ = lean_ctor_get_uint8(v_config_3662_, sizeof(void*)*3 + 1);
v_graphviz_3668_ = lean_ctor_get_uint8(v_config_3662_, sizeof(void*)*3 + 8);
v_solverMode_3669_ = lean_ctor_get_uint8(v_config_3662_, sizeof(void*)*3 + 10);
if (v_graphviz_3668_ == 0)
{
lean_object* v_toCold_3862_; lean_object* v_ref_3863_; 
lean_dec_ref(v_a_3397_);
v_toCold_3862_ = lean_ctor_get(v___y_3409_, 0);
v_ref_3863_ = lean_ctor_get(v___y_3409_, 2);
v___y_3836_ = v___y_3399_;
v___y_3837_ = v___y_3400_;
v___y_3838_ = v___y_3401_;
v___y_3839_ = v___y_3402_;
v___y_3840_ = v___y_3403_;
v___y_3841_ = v___y_3404_;
v___y_3842_ = v___y_3405_;
v___y_3843_ = v___y_3406_;
v___y_3844_ = v___y_3407_;
v___y_3845_ = v___y_3408_;
v___y_3846_ = v___y_3409_;
v_toCold_3847_ = v_toCold_3862_;
v_ref_3848_ = v_ref_3863_;
v___y_3849_ = v___y_3410_;
goto v___jp_3835_;
}
else
{
lean_object* v_toCold_3864_; lean_object* v_ref_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v_toCold_3864_ = lean_ctor_get(v___y_3409_, 0);
v_ref_3865_ = lean_ctor_get(v___y_3409_, 2);
v___x_3866_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3867_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_3397_);
v___x_3868_ = l_IO_FS_writeFile(v___x_3866_, v___x_3867_);
lean_dec_ref(v___x_3867_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_dec_ref_known(v___x_3868_, 1);
v___y_3836_ = v___y_3399_;
v___y_3837_ = v___y_3400_;
v___y_3838_ = v___y_3401_;
v___y_3839_ = v___y_3402_;
v___y_3840_ = v___y_3403_;
v___y_3841_ = v___y_3404_;
v___y_3842_ = v___y_3405_;
v___y_3843_ = v___y_3406_;
v___y_3844_ = v___y_3407_;
v___y_3845_ = v___y_3408_;
v___y_3846_ = v___y_3409_;
v_toCold_3847_ = v_toCold_3864_;
v_ref_3848_ = v_ref_3865_;
v___y_3849_ = v___y_3410_;
goto v___jp_3835_;
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v___f_3396_);
lean_dec_ref(v___x_3395_);
lean_dec_ref(v___x_3394_);
lean_dec_ref(v___f_3393_);
lean_dec_ref(v___f_3392_);
lean_dec_ref(v___f_3390_);
lean_dec_ref(v___x_3389_);
lean_dec_ref(v_satExpr_3387_);
lean_dec_ref(v_reflectionResult_3386_);
lean_dec_ref(v_unusedHypotheses_3385_);
lean_dec(v_goal_3384_);
lean_dec_ref(v_aig_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3871_ = v___x_3868_;
v_isShared_3872_ = v_isSharedCheck_3880_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3868_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3880_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3873_ = lean_io_error_to_string(v_a_3869_);
v___x_3874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
v___x_3875_ = l_Lean_MessageData_ofFormat(v___x_3874_);
lean_inc(v_ref_3865_);
v___x_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3876_, 0, v_ref_3865_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 0, v___x_3876_);
v___x_3878_ = v___x_3871_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
v___jp_3412_:
{
lean_object* v___x_3425_; 
lean_inc_ref(v___y_3413_);
v___x_3425_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3413_, v_ctx_3382_, v_reflectionResult_3386_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_3387_, v_a_3426_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3437_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_3384_, v_a_3428_, v___y_3422_);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3437_ == 0)
{
lean_object* v_unused_3438_; 
v_unused_3438_ = lean_ctor_get(v___x_3429_, 0);
lean_dec(v_unused_3438_);
v___x_3431_ = v___x_3429_;
v_isShared_3432_ = v_isSharedCheck_3437_;
goto v_resetjp_3430_;
}
else
{
lean_dec(v___x_3429_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3437_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___y_3413_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3433_);
v___x_3435_ = v___x_3431_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec_ref(v___y_3413_);
lean_dec(v_goal_3384_);
v_a_3439_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3427_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3427_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref(v___y_3413_);
lean_dec_ref(v_satExpr_3387_);
lean_dec(v_goal_3384_);
v_a_3447_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3425_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3425_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
v___jp_3455_:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_3457_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3473_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3473_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3473_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3463_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_3383_, v___y_3456_, v_a_3459_);
lean_dec(v_a_3459_);
lean_dec_ref(v___y_3456_);
v___x_3464_ = lean_unsigned_to_nat(0u);
v___x_3465_ = lean_array_get_size(v___x_3463_);
v___x_3466_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_3463_, v___x_3464_, v___x_3465_);
lean_dec_ref(v___x_3463_);
v___x_3467_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_3468_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3468_, 0, v_goal_3384_);
lean_ctor_set(v___x_3468_, 1, v_unusedHypotheses_3385_);
lean_ctor_set(v___x_3468_, 2, v___x_3466_);
lean_ctor_set(v___x_3468_, 3, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3469_);
v___x_3471_ = v___x_3461_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec_ref(v___y_3456_);
lean_dec_ref(v_unusedHypotheses_3385_);
lean_dec(v_goal_3384_);
lean_dec_ref(v_aig_3383_);
v_a_3474_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3458_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3458_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
v___jp_3482_:
{
if (lean_obj_tag(v___y_3495_) == 0)
{
lean_object* v_a_3496_; 
v_a_3496_ = lean_ctor_get(v___y_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___y_3495_, 1);
if (lean_obj_tag(v_a_3496_) == 0)
{
lean_object* v_toCold_3497_; lean_object* v_options_3498_; uint8_t v_hasTrace_3499_; 
lean_dec_ref(v_satExpr_3387_);
lean_dec_ref(v_reflectionResult_3386_);
lean_dec_ref(v_ctx_3382_);
v_toCold_3497_ = lean_ctor_get(v___y_3487_, 0);
v_options_3498_ = lean_ctor_get(v_toCold_3497_, 2);
v_hasTrace_3499_ = lean_ctor_get_uint8(v_options_3498_, sizeof(void*)*1);
if (v_hasTrace_3499_ == 0)
{
lean_object* v_a_3500_; 
lean_dec(v___y_3494_);
v_a_3500_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v_a_3496_, 1);
v___y_3456_ = v_a_3500_;
v___y_3457_ = v___y_3485_;
goto v___jp_3455_;
}
else
{
lean_object* v_a_3501_; lean_object* v_inheritedTraceOptions_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v_a_3501_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v_a_3496_, 1);
v_inheritedTraceOptions_3502_ = lean_ctor_get(v_toCold_3497_, 11);
v___x_3503_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3494_);
v___x_3504_ = l_Lean_Name_append(v___x_3503_, v___y_3494_);
v___x_3505_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3502_, v_options_3498_, v___x_3504_);
lean_dec(v___x_3504_);
if (v___x_3505_ == 0)
{
lean_dec(v___y_3494_);
v___y_3456_ = v_a_3501_;
v___y_3457_ = v___y_3485_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_3507_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3494_, v___x_3506_, v___y_3492_, v___y_3493_, v___y_3487_, v___y_3486_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_dec_ref_known(v___x_3507_, 1);
v___y_3456_ = v_a_3501_;
v___y_3457_ = v___y_3485_;
goto v___jp_3455_;
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v_a_3501_);
lean_dec_ref(v_unusedHypotheses_3385_);
lean_dec(v_goal_3384_);
lean_dec_ref(v_aig_3383_);
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3516_; lean_object* v_options_3517_; uint8_t v_hasTrace_3518_; 
lean_dec_ref(v_unusedHypotheses_3385_);
lean_dec_ref(v_aig_3383_);
v_toCold_3516_ = lean_ctor_get(v___y_3487_, 0);
v_options_3517_ = lean_ctor_get(v_toCold_3516_, 2);
v_hasTrace_3518_ = lean_ctor_get_uint8(v_options_3517_, sizeof(void*)*1);
if (v_hasTrace_3518_ == 0)
{
lean_object* v_a_3519_; 
lean_dec(v___y_3494_);
v_a_3519_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v_a_3496_, 1);
v___y_3413_ = v_a_3519_;
v___y_3414_ = v___y_3490_;
v___y_3415_ = v___y_3485_;
v___y_3416_ = v___y_3483_;
v___y_3417_ = v___y_3488_;
v___y_3418_ = v___y_3489_;
v___y_3419_ = v___y_3491_;
v___y_3420_ = v___y_3484_;
v___y_3421_ = v___y_3492_;
v___y_3422_ = v___y_3493_;
v___y_3423_ = v___y_3487_;
v___y_3424_ = v___y_3486_;
goto v___jp_3412_;
}
else
{
lean_object* v_a_3520_; lean_object* v_inheritedTraceOptions_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v_a_3520_ = lean_ctor_get(v_a_3496_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v_a_3496_, 1);
v_inheritedTraceOptions_3521_ = lean_ctor_get(v_toCold_3516_, 11);
v___x_3522_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3494_);
v___x_3523_ = l_Lean_Name_append(v___x_3522_, v___y_3494_);
v___x_3524_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3521_, v_options_3517_, v___x_3523_);
lean_dec(v___x_3523_);
if (v___x_3524_ == 0)
{
lean_dec(v___y_3494_);
v___y_3413_ = v_a_3520_;
v___y_3414_ = v___y_3490_;
v___y_3415_ = v___y_3485_;
v___y_3416_ = v___y_3483_;
v___y_3417_ = v___y_3488_;
v___y_3418_ = v___y_3489_;
v___y_3419_ = v___y_3491_;
v___y_3420_ = v___y_3484_;
v___y_3421_ = v___y_3492_;
v___y_3422_ = v___y_3493_;
v___y_3423_ = v___y_3487_;
v___y_3424_ = v___y_3486_;
goto v___jp_3412_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_3526_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3494_, v___x_3525_, v___y_3492_, v___y_3493_, v___y_3487_, v___y_3486_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_dec_ref_known(v___x_3526_, 1);
v___y_3413_ = v_a_3520_;
v___y_3414_ = v___y_3490_;
v___y_3415_ = v___y_3485_;
v___y_3416_ = v___y_3483_;
v___y_3417_ = v___y_3488_;
v___y_3418_ = v___y_3489_;
v___y_3419_ = v___y_3491_;
v___y_3420_ = v___y_3484_;
v___y_3421_ = v___y_3492_;
v___y_3422_ = v___y_3493_;
v___y_3423_ = v___y_3487_;
v___y_3424_ = v___y_3486_;
goto v___jp_3412_;
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_a_3520_);
lean_dec_ref(v_satExpr_3387_);
lean_dec_ref(v_reflectionResult_3386_);
lean_dec(v_goal_3384_);
lean_dec_ref(v_ctx_3382_);
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec(v___y_3494_);
lean_dec_ref(v_satExpr_3387_);
lean_dec_ref(v_reflectionResult_3386_);
lean_dec_ref(v_unusedHypotheses_3385_);
lean_dec(v_goal_3384_);
lean_dec_ref(v_aig_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3535_ = lean_ctor_get(v___y_3495_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___y_3495_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___y_3495_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___y_3495_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
v___jp_3543_:
{
lean_object* v___x_3562_; double v___x_3563_; double v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3562_ = lean_io_get_num_heartbeats();
v___x_3563_ = lean_float_of_nat(v___y_3551_);
v___x_3564_ = lean_float_of_nat(v___x_3562_);
v___x_3565_ = lean_box_float(v___x_3563_);
v___x_3566_ = lean_box_float(v___x_3564_);
v___x_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3565_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v_a_3561_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
lean_inc(v___y_3558_);
v___x_3569_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3558_, v___x_3388_, v___x_3389_, v___y_3559_, v___y_3560_, v___y_3549_, v___f_3390_, v___x_3568_, v___y_3552_, v___y_3554_, v___y_3547_, v___y_3544_, v___y_3550_, v___y_3553_, v___y_3555_, v___y_3545_, v___y_3557_, v___y_3556_, v___y_3548_, v___y_3546_);
v___y_3483_ = v___y_3544_;
v___y_3484_ = v___y_3545_;
v___y_3485_ = v___y_3547_;
v___y_3486_ = v___y_3546_;
v___y_3487_ = v___y_3548_;
v___y_3488_ = v___y_3550_;
v___y_3489_ = v___y_3553_;
v___y_3490_ = v___y_3554_;
v___y_3491_ = v___y_3555_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3556_;
v___y_3494_ = v___y_3558_;
v___y_3495_ = v___x_3569_;
goto v___jp_3482_;
}
v___jp_3570_:
{
lean_object* v___x_3589_; double v___x_3590_; double v___x_3591_; double v___x_3592_; double v___x_3593_; double v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3589_ = lean_io_mono_nanos_now();
v___x_3590_ = lean_float_of_nat(v___y_3584_);
v___x_3591_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3592_ = lean_float_div(v___x_3590_, v___x_3591_);
v___x_3593_ = lean_float_of_nat(v___x_3589_);
v___x_3594_ = lean_float_div(v___x_3593_, v___x_3591_);
v___x_3595_ = lean_box_float(v___x_3592_);
v___x_3596_ = lean_box_float(v___x_3594_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v_a_3588_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
lean_inc(v___y_3585_);
v___x_3599_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3585_, v___x_3388_, v___x_3389_, v___y_3586_, v___y_3587_, v___y_3576_, v___f_3390_, v___x_3598_, v___y_3578_, v___y_3580_, v___y_3574_, v___y_3571_, v___y_3577_, v___y_3579_, v___y_3581_, v___y_3572_, v___y_3583_, v___y_3582_, v___y_3575_, v___y_3573_);
v___y_3483_ = v___y_3571_;
v___y_3484_ = v___y_3572_;
v___y_3485_ = v___y_3574_;
v___y_3486_ = v___y_3573_;
v___y_3487_ = v___y_3575_;
v___y_3488_ = v___y_3577_;
v___y_3489_ = v___y_3579_;
v___y_3490_ = v___y_3580_;
v___y_3491_ = v___y_3581_;
v___y_3492_ = v___y_3583_;
v___y_3493_ = v___y_3582_;
v___y_3494_ = v___y_3585_;
v___y_3495_ = v___x_3599_;
goto v___jp_3482_;
}
v___jp_3600_:
{
lean_object* v___x_3623_; lean_object* v_a_3624_; uint8_t v___x_3625_; 
v___x_3623_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3606_);
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref(v___x_3623_);
v___x_3625_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3621_, v___x_3391_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_io_mono_nanos_now();
v___x_3627_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3620_, v___y_3601_, v___y_3618_, v___y_3607_, v___y_3612_, v___y_3609_, v___y_3603_, v___y_3608_, v___y_3606_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
v___y_3571_ = v___y_3602_;
v___y_3572_ = v___y_3604_;
v___y_3573_ = v___y_3606_;
v___y_3574_ = v___y_3605_;
v___y_3575_ = v___y_3608_;
v___y_3576_ = v_a_3624_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3611_;
v___y_3579_ = v___y_3613_;
v___y_3580_ = v___y_3614_;
v___y_3581_ = v___y_3615_;
v___y_3582_ = v___y_3617_;
v___y_3583_ = v___y_3616_;
v___y_3584_ = v___x_3626_;
v___y_3585_ = v___y_3619_;
v___y_3586_ = v___y_3621_;
v___y_3587_ = v___y_3622_;
v_a_3588_ = v___x_3633_;
goto v___jp_3570_;
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
v_a_3636_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3627_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3627_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 0);
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
v___y_3571_ = v___y_3602_;
v___y_3572_ = v___y_3604_;
v___y_3573_ = v___y_3606_;
v___y_3574_ = v___y_3605_;
v___y_3575_ = v___y_3608_;
v___y_3576_ = v_a_3624_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3611_;
v___y_3579_ = v___y_3613_;
v___y_3580_ = v___y_3614_;
v___y_3581_ = v___y_3615_;
v___y_3582_ = v___y_3617_;
v___y_3583_ = v___y_3616_;
v___y_3584_ = v___x_3626_;
v___y_3585_ = v___y_3619_;
v___y_3586_ = v___y_3621_;
v___y_3587_ = v___y_3622_;
v_a_3588_ = v___x_3641_;
goto v___jp_3570_;
}
}
}
}
else
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = lean_io_get_num_heartbeats();
v___x_3645_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3620_, v___y_3601_, v___y_3618_, v___y_3607_, v___y_3612_, v___y_3609_, v___y_3603_, v___y_3608_, v___y_3606_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set_tag(v___x_3648_, 1);
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
v___y_3544_ = v___y_3602_;
v___y_3545_ = v___y_3604_;
v___y_3546_ = v___y_3606_;
v___y_3547_ = v___y_3605_;
v___y_3548_ = v___y_3608_;
v___y_3549_ = v_a_3624_;
v___y_3550_ = v___y_3610_;
v___y_3551_ = v___x_3644_;
v___y_3552_ = v___y_3611_;
v___y_3553_ = v___y_3613_;
v___y_3554_ = v___y_3614_;
v___y_3555_ = v___y_3615_;
v___y_3556_ = v___y_3617_;
v___y_3557_ = v___y_3616_;
v___y_3558_ = v___y_3619_;
v___y_3559_ = v___y_3621_;
v___y_3560_ = v___y_3622_;
v_a_3561_ = v___x_3651_;
goto v___jp_3543_;
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
v_a_3654_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3645_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3645_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set_tag(v___x_3656_, 0);
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
v___y_3544_ = v___y_3602_;
v___y_3545_ = v___y_3604_;
v___y_3546_ = v___y_3606_;
v___y_3547_ = v___y_3605_;
v___y_3548_ = v___y_3608_;
v___y_3549_ = v_a_3624_;
v___y_3550_ = v___y_3610_;
v___y_3551_ = v___x_3644_;
v___y_3552_ = v___y_3611_;
v___y_3553_ = v___y_3613_;
v___y_3554_ = v___y_3614_;
v___y_3555_ = v___y_3615_;
v___y_3556_ = v___y_3617_;
v___y_3557_ = v___y_3616_;
v___y_3558_ = v___y_3619_;
v___y_3559_ = v___y_3621_;
v___y_3560_ = v___y_3622_;
v_a_3561_ = v___x_3659_;
goto v___jp_3543_;
}
}
}
}
}
v___jp_3670_:
{
if (lean_obj_tag(v___y_3684_) == 0)
{
lean_object* v_toCold_3685_; lean_object* v_options_3686_; uint8_t v_hasTrace_3687_; 
v_toCold_3685_ = lean_ctor_get(v___y_3675_, 0);
v_options_3686_ = lean_ctor_get(v_toCold_3685_, 2);
v_hasTrace_3687_ = lean_ctor_get_uint8(v_options_3686_, sizeof(void*)*1);
if (v_hasTrace_3687_ == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
lean_dec_ref(v___f_3390_);
lean_dec_ref(v___x_3389_);
v_a_3688_ = lean_ctor_get(v___y_3684_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___y_3684_, 1);
lean_inc(v_timeout_3665_);
lean_inc_ref(v_lratPath_3664_);
lean_inc_ref(v_solver_3663_);
v___x_3689_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3688_, v_solver_3663_, v_lratPath_3664_, v_trimProofs_3666_, v_timeout_3665_, v_binaryProofs_3667_, v_solverMode_3669_, v___y_3675_, v___y_3673_);
v___y_3483_ = v___y_3671_;
v___y_3484_ = v___y_3672_;
v___y_3485_ = v___y_3674_;
v___y_3486_ = v___y_3673_;
v___y_3487_ = v___y_3675_;
v___y_3488_ = v___y_3676_;
v___y_3489_ = v___y_3678_;
v___y_3490_ = v___y_3679_;
v___y_3491_ = v___y_3680_;
v___y_3492_ = v___y_3681_;
v___y_3493_ = v___y_3682_;
v___y_3494_ = v___y_3683_;
v___y_3495_ = v___x_3689_;
goto v___jp_3482_;
}
else
{
lean_object* v_a_3690_; lean_object* v_inheritedTraceOptions_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v_a_3690_ = lean_ctor_get(v___y_3684_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___y_3684_, 1);
v_inheritedTraceOptions_3691_ = lean_ctor_get(v_toCold_3685_, 11);
v___x_3692_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3683_);
v___x_3693_ = l_Lean_Name_append(v___x_3692_, v___y_3683_);
v___x_3694_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3691_, v_options_3686_, v___x_3693_);
lean_dec(v___x_3693_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; uint8_t v___x_3696_; 
v___x_3695_ = l_Lean_trace_profiler;
v___x_3696_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3686_, v___x_3695_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; 
lean_dec_ref(v___f_3390_);
lean_dec_ref(v___x_3389_);
lean_inc(v_timeout_3665_);
lean_inc_ref(v_lratPath_3664_);
lean_inc_ref(v_solver_3663_);
v___x_3697_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3690_, v_solver_3663_, v_lratPath_3664_, v_trimProofs_3666_, v_timeout_3665_, v_binaryProofs_3667_, v_solverMode_3669_, v___y_3675_, v___y_3673_);
v___y_3483_ = v___y_3671_;
v___y_3484_ = v___y_3672_;
v___y_3485_ = v___y_3674_;
v___y_3486_ = v___y_3673_;
v___y_3487_ = v___y_3675_;
v___y_3488_ = v___y_3676_;
v___y_3489_ = v___y_3678_;
v___y_3490_ = v___y_3679_;
v___y_3491_ = v___y_3680_;
v___y_3492_ = v___y_3681_;
v___y_3493_ = v___y_3682_;
v___y_3494_ = v___y_3683_;
v___y_3495_ = v___x_3697_;
goto v___jp_3482_;
}
else
{
lean_inc_ref(v_lratPath_3664_);
lean_inc(v_timeout_3665_);
lean_inc_ref(v_solver_3663_);
v___y_3601_ = v_solver_3663_;
v___y_3602_ = v___y_3671_;
v___y_3603_ = v_solverMode_3669_;
v___y_3604_ = v___y_3672_;
v___y_3605_ = v___y_3674_;
v___y_3606_ = v___y_3673_;
v___y_3607_ = v_trimProofs_3666_;
v___y_3608_ = v___y_3675_;
v___y_3609_ = v_binaryProofs_3667_;
v___y_3610_ = v___y_3676_;
v___y_3611_ = v___y_3677_;
v___y_3612_ = v_timeout_3665_;
v___y_3613_ = v___y_3678_;
v___y_3614_ = v___y_3679_;
v___y_3615_ = v___y_3680_;
v___y_3616_ = v___y_3681_;
v___y_3617_ = v___y_3682_;
v___y_3618_ = v_lratPath_3664_;
v___y_3619_ = v___y_3683_;
v___y_3620_ = v_a_3690_;
v___y_3621_ = v_options_3686_;
v___y_3622_ = v___x_3694_;
goto v___jp_3600_;
}
}
else
{
lean_inc_ref(v_lratPath_3664_);
lean_inc(v_timeout_3665_);
lean_inc_ref(v_solver_3663_);
v___y_3601_ = v_solver_3663_;
v___y_3602_ = v___y_3671_;
v___y_3603_ = v_solverMode_3669_;
v___y_3604_ = v___y_3672_;
v___y_3605_ = v___y_3674_;
v___y_3606_ = v___y_3673_;
v___y_3607_ = v_trimProofs_3666_;
v___y_3608_ = v___y_3675_;
v___y_3609_ = v_binaryProofs_3667_;
v___y_3610_ = v___y_3676_;
v___y_3611_ = v___y_3677_;
v___y_3612_ = v_timeout_3665_;
v___y_3613_ = v___y_3678_;
v___y_3614_ = v___y_3679_;
v___y_3615_ = v___y_3680_;
v___y_3616_ = v___y_3681_;
v___y_3617_ = v___y_3682_;
v___y_3618_ = v_lratPath_3664_;
v___y_3619_ = v___y_3683_;
v___y_3620_ = v_a_3690_;
v___y_3621_ = v_options_3686_;
v___y_3622_ = v___x_3694_;
goto v___jp_3600_;
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec(v___y_3683_);
lean_dec_ref(v___f_3390_);
lean_dec_ref(v___x_3389_);
lean_dec_ref(v_satExpr_3387_);
lean_dec_ref(v_reflectionResult_3386_);
lean_dec_ref(v_unusedHypotheses_3385_);
lean_dec(v_goal_3384_);
lean_dec_ref(v_aig_3383_);
lean_dec_ref(v_ctx_3382_);
v_a_3698_ = lean_ctor_get(v___y_3684_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___y_3684_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___y_3684_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___y_3684_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
v___jp_3706_:
{
lean_object* v___x_3725_; double v___x_3726_; double v___x_3727_; double v___x_3728_; double v___x_3729_; double v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3725_ = lean_io_mono_nanos_now();
v___x_3726_ = lean_float_of_nat(v___y_3723_);
v___x_3727_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3728_ = lean_float_div(v___x_3726_, v___x_3727_);
v___x_3729_ = lean_float_of_nat(v___x_3725_);
v___x_3730_ = lean_float_div(v___x_3729_, v___x_3727_);
v___x_3731_ = lean_box_float(v___x_3728_);
v___x_3732_ = lean_box_float(v___x_3730_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v_a_3724_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
lean_inc_ref(v___x_3389_);
lean_inc(v___y_3721_);
v___x_3735_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3721_, v___x_3388_, v___x_3389_, v___y_3714_, v___y_3722_, v___y_3718_, v___f_3392_, v___x_3734_, v___y_3713_, v___y_3716_, v___y_3710_, v___y_3707_, v___y_3712_, v___y_3715_, v___y_3717_, v___y_3708_, v___y_3720_, v___y_3719_, v___y_3711_, v___y_3709_);
v___y_3671_ = v___y_3707_;
v___y_3672_ = v___y_3708_;
v___y_3673_ = v___y_3709_;
v___y_3674_ = v___y_3710_;
v___y_3675_ = v___y_3711_;
v___y_3676_ = v___y_3712_;
v___y_3677_ = v___y_3713_;
v___y_3678_ = v___y_3715_;
v___y_3679_ = v___y_3716_;
v___y_3680_ = v___y_3717_;
v___y_3681_ = v___y_3720_;
v___y_3682_ = v___y_3719_;
v___y_3683_ = v___y_3721_;
v___y_3684_ = v___x_3735_;
goto v___jp_3670_;
}
v___jp_3736_:
{
lean_object* v___x_3755_; double v___x_3756_; double v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3755_ = lean_io_get_num_heartbeats();
v___x_3756_ = lean_float_of_nat(v___y_3753_);
v___x_3757_ = lean_float_of_nat(v___x_3755_);
v___x_3758_ = lean_box_float(v___x_3756_);
v___x_3759_ = lean_box_float(v___x_3757_);
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v_a_3754_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
lean_inc_ref(v___x_3389_);
lean_inc(v___y_3751_);
v___x_3762_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3751_, v___x_3388_, v___x_3389_, v___y_3744_, v___y_3752_, v___y_3748_, v___f_3392_, v___x_3761_, v___y_3743_, v___y_3746_, v___y_3740_, v___y_3737_, v___y_3742_, v___y_3745_, v___y_3747_, v___y_3738_, v___y_3750_, v___y_3749_, v___y_3741_, v___y_3739_);
v___y_3671_ = v___y_3737_;
v___y_3672_ = v___y_3738_;
v___y_3673_ = v___y_3739_;
v___y_3674_ = v___y_3740_;
v___y_3675_ = v___y_3741_;
v___y_3676_ = v___y_3742_;
v___y_3677_ = v___y_3743_;
v___y_3678_ = v___y_3745_;
v___y_3679_ = v___y_3746_;
v___y_3680_ = v___y_3747_;
v___y_3681_ = v___y_3750_;
v___y_3682_ = v___y_3749_;
v___y_3683_ = v___y_3751_;
v___y_3684_ = v___x_3762_;
goto v___jp_3670_;
}
v___jp_3763_:
{
lean_object* v___x_3780_; lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3834_; 
v___x_3780_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3767_);
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3783_ = v___x_3780_;
v_isShared_3784_ = v_isSharedCheck_3834_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3834_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
uint8_t v___x_3785_; 
v___x_3785_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3771_, v___x_3391_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3786_ = lean_io_mono_nanos_now();
v___x_3787_ = l_IO_lazyPure___redArg(v___f_3393_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_del_object(v___x_3783_);
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set_tag(v___x_3790_, 1);
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
v___y_3707_ = v___y_3764_;
v___y_3708_ = v___y_3765_;
v___y_3709_ = v___y_3767_;
v___y_3710_ = v___y_3766_;
v___y_3711_ = v___y_3768_;
v___y_3712_ = v___y_3769_;
v___y_3713_ = v___y_3770_;
v___y_3714_ = v___y_3771_;
v___y_3715_ = v___y_3772_;
v___y_3716_ = v___y_3774_;
v___y_3717_ = v___y_3775_;
v___y_3718_ = v_a_3781_;
v___y_3719_ = v___y_3777_;
v___y_3720_ = v___y_3776_;
v___y_3721_ = v___y_3778_;
v___y_3722_ = v___y_3779_;
v___y_3723_ = v___x_3786_;
v_a_3724_ = v___x_3793_;
goto v___jp_3706_;
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3809_; 
v_a_3796_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3798_ = v___x_3787_;
v_isShared_3799_ = v_isSharedCheck_3809_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3787_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3809_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3800_; lean_object* v___x_3802_; 
v___x_3800_ = lean_io_error_to_string(v_a_3796_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set_tag(v___x_3798_, 3);
lean_ctor_set(v___x_3798_, 0, v___x_3800_);
v___x_3802_ = v___x_3798_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3803_ = l_Lean_MessageData_ofFormat(v___x_3802_);
lean_inc(v___y_3773_);
v___x_3804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___y_3773_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v___x_3804_);
v___x_3806_ = v___x_3783_;
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
v___y_3707_ = v___y_3764_;
v___y_3708_ = v___y_3765_;
v___y_3709_ = v___y_3767_;
v___y_3710_ = v___y_3766_;
v___y_3711_ = v___y_3768_;
v___y_3712_ = v___y_3769_;
v___y_3713_ = v___y_3770_;
v___y_3714_ = v___y_3771_;
v___y_3715_ = v___y_3772_;
v___y_3716_ = v___y_3774_;
v___y_3717_ = v___y_3775_;
v___y_3718_ = v_a_3781_;
v___y_3719_ = v___y_3777_;
v___y_3720_ = v___y_3776_;
v___y_3721_ = v___y_3778_;
v___y_3722_ = v___y_3779_;
v___y_3723_ = v___x_3786_;
v_a_3724_ = v___x_3806_;
goto v___jp_3706_;
}
}
}
}
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = lean_io_get_num_heartbeats();
v___x_3811_ = l_IO_lazyPure___redArg(v___f_3393_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_del_object(v___x_3783_);
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3811_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3811_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set_tag(v___x_3814_, 1);
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
v___y_3737_ = v___y_3764_;
v___y_3738_ = v___y_3765_;
v___y_3739_ = v___y_3767_;
v___y_3740_ = v___y_3766_;
v___y_3741_ = v___y_3768_;
v___y_3742_ = v___y_3769_;
v___y_3743_ = v___y_3770_;
v___y_3744_ = v___y_3771_;
v___y_3745_ = v___y_3772_;
v___y_3746_ = v___y_3774_;
v___y_3747_ = v___y_3775_;
v___y_3748_ = v_a_3781_;
v___y_3749_ = v___y_3777_;
v___y_3750_ = v___y_3776_;
v___y_3751_ = v___y_3778_;
v___y_3752_ = v___y_3779_;
v___y_3753_ = v___x_3810_;
v_a_3754_ = v___x_3817_;
goto v___jp_3736_;
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3833_; 
v_a_3820_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3822_ = v___x_3811_;
v_isShared_3823_ = v_isSharedCheck_3833_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3811_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3833_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3824_ = lean_io_error_to_string(v_a_3820_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set_tag(v___x_3822_, 3);
lean_ctor_set(v___x_3822_, 0, v___x_3824_);
v___x_3826_ = v___x_3822_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3830_; 
v___x_3827_ = l_Lean_MessageData_ofFormat(v___x_3826_);
lean_inc(v___y_3773_);
v___x_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___y_3773_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v___x_3828_);
v___x_3830_ = v___x_3783_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
v___y_3737_ = v___y_3764_;
v___y_3738_ = v___y_3765_;
v___y_3739_ = v___y_3767_;
v___y_3740_ = v___y_3766_;
v___y_3741_ = v___y_3768_;
v___y_3742_ = v___y_3769_;
v___y_3743_ = v___y_3770_;
v___y_3744_ = v___y_3771_;
v___y_3745_ = v___y_3772_;
v___y_3746_ = v___y_3774_;
v___y_3747_ = v___y_3775_;
v___y_3748_ = v_a_3781_;
v___y_3749_ = v___y_3777_;
v___y_3750_ = v___y_3776_;
v___y_3751_ = v___y_3778_;
v___y_3752_ = v___y_3779_;
v___y_3753_ = v___x_3810_;
v_a_3754_ = v___x_3830_;
goto v___jp_3736_;
}
}
}
}
}
}
}
v___jp_3835_:
{
lean_object* v_options_3850_; lean_object* v_inheritedTraceOptions_3851_; uint8_t v_hasTrace_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_options_3850_ = lean_ctor_get(v_toCold_3847_, 2);
v_inheritedTraceOptions_3851_ = lean_ctor_get(v_toCold_3847_, 11);
v_hasTrace_3852_ = lean_ctor_get_uint8(v_options_3850_, sizeof(void*)*1);
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3854_ = l_Lean_Name_mkStr3(v___x_3394_, v___x_3395_, v___x_3853_);
if (v_hasTrace_3852_ == 0)
{
lean_object* v___x_3855_; 
lean_dec_ref(v___f_3393_);
lean_dec_ref(v___f_3392_);
lean_inc(v___y_3849_);
lean_inc_ref(v___y_3846_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3844_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
lean_inc(v___y_3839_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
v___x_3855_ = lean_apply_12(v___f_3396_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3849_, lean_box(0));
v___y_3671_ = v___y_3839_;
v___y_3672_ = v___y_3843_;
v___y_3673_ = v___y_3849_;
v___y_3674_ = v___y_3838_;
v___y_3675_ = v___y_3846_;
v___y_3676_ = v___y_3840_;
v___y_3677_ = v___y_3836_;
v___y_3678_ = v___y_3841_;
v___y_3679_ = v___y_3837_;
v___y_3680_ = v___y_3842_;
v___y_3681_ = v___y_3844_;
v___y_3682_ = v___y_3845_;
v___y_3683_ = v___x_3854_;
v___y_3684_ = v___x_3855_;
goto v___jp_3670_;
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3856_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3854_);
v___x_3857_ = l_Lean_Name_append(v___x_3856_, v___x_3854_);
v___x_3858_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3851_, v_options_3850_, v___x_3857_);
lean_dec(v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3859_ = l_Lean_trace_profiler;
v___x_3860_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3850_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec_ref(v___f_3393_);
lean_dec_ref(v___f_3392_);
lean_inc(v___y_3849_);
lean_inc_ref(v___y_3846_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3844_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
lean_inc(v___y_3839_);
lean_inc(v___y_3838_);
lean_inc_ref(v___y_3837_);
v___x_3861_ = lean_apply_12(v___f_3396_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3849_, lean_box(0));
v___y_3671_ = v___y_3839_;
v___y_3672_ = v___y_3843_;
v___y_3673_ = v___y_3849_;
v___y_3674_ = v___y_3838_;
v___y_3675_ = v___y_3846_;
v___y_3676_ = v___y_3840_;
v___y_3677_ = v___y_3836_;
v___y_3678_ = v___y_3841_;
v___y_3679_ = v___y_3837_;
v___y_3680_ = v___y_3842_;
v___y_3681_ = v___y_3844_;
v___y_3682_ = v___y_3845_;
v___y_3683_ = v___x_3854_;
v___y_3684_ = v___x_3861_;
goto v___jp_3670_;
}
else
{
lean_dec_ref(v___f_3396_);
v___y_3764_ = v___y_3839_;
v___y_3765_ = v___y_3843_;
v___y_3766_ = v___y_3838_;
v___y_3767_ = v___y_3849_;
v___y_3768_ = v___y_3846_;
v___y_3769_ = v___y_3840_;
v___y_3770_ = v___y_3836_;
v___y_3771_ = v_options_3850_;
v___y_3772_ = v___y_3841_;
v___y_3773_ = v_ref_3848_;
v___y_3774_ = v___y_3837_;
v___y_3775_ = v___y_3842_;
v___y_3776_ = v___y_3844_;
v___y_3777_ = v___y_3845_;
v___y_3778_ = v___x_3854_;
v___y_3779_ = v___x_3858_;
goto v___jp_3763_;
}
}
else
{
lean_dec_ref(v___f_3396_);
v___y_3764_ = v___y_3839_;
v___y_3765_ = v___y_3843_;
v___y_3766_ = v___y_3838_;
v___y_3767_ = v___y_3849_;
v___y_3768_ = v___y_3846_;
v___y_3769_ = v___y_3840_;
v___y_3770_ = v___y_3836_;
v___y_3771_ = v_options_3850_;
v___y_3772_ = v___y_3841_;
v___y_3773_ = v_ref_3848_;
v___y_3774_ = v___y_3837_;
v___y_3775_ = v___y_3842_;
v___y_3776_ = v___y_3844_;
v___y_3777_ = v___y_3845_;
v___y_3778_ = v___x_3854_;
v___y_3779_ = v___x_3858_;
goto v___jp_3763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13___boxed(lean_object** _args){
lean_object* v_ctx_3881_ = _args[0];
lean_object* v_aig_3882_ = _args[1];
lean_object* v_goal_3883_ = _args[2];
lean_object* v_unusedHypotheses_3884_ = _args[3];
lean_object* v_reflectionResult_3885_ = _args[4];
lean_object* v_satExpr_3886_ = _args[5];
lean_object* v___x_3887_ = _args[6];
lean_object* v___x_3888_ = _args[7];
lean_object* v___f_3889_ = _args[8];
lean_object* v___x_3890_ = _args[9];
lean_object* v___f_3891_ = _args[10];
lean_object* v___f_3892_ = _args[11];
lean_object* v___x_3893_ = _args[12];
lean_object* v___x_3894_ = _args[13];
lean_object* v___f_3895_ = _args[14];
lean_object* v_a_3896_ = _args[15];
lean_object* v_____r_3897_ = _args[16];
lean_object* v___y_3898_ = _args[17];
lean_object* v___y_3899_ = _args[18];
lean_object* v___y_3900_ = _args[19];
lean_object* v___y_3901_ = _args[20];
lean_object* v___y_3902_ = _args[21];
lean_object* v___y_3903_ = _args[22];
lean_object* v___y_3904_ = _args[23];
lean_object* v___y_3905_ = _args[24];
lean_object* v___y_3906_ = _args[25];
lean_object* v___y_3907_ = _args[26];
lean_object* v___y_3908_ = _args[27];
lean_object* v___y_3909_ = _args[28];
lean_object* v___y_3910_ = _args[29];
_start:
{
uint8_t v___x_655906__boxed_3911_; lean_object* v_res_3912_; 
v___x_655906__boxed_3911_ = lean_unbox(v___x_3887_);
v_res_3912_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_3881_, v_aig_3882_, v_goal_3883_, v_unusedHypotheses_3884_, v_reflectionResult_3885_, v_satExpr_3886_, v___x_655906__boxed_3911_, v___x_3888_, v___f_3889_, v___x_3890_, v___f_3891_, v___f_3892_, v___x_3893_, v___x_3894_, v___f_3895_, v_a_3896_, v_____r_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___x_3890_);
return v_res_3912_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(lean_object* v_e_3913_){
_start:
{
if (lean_obj_tag(v_e_3913_) == 0)
{
uint8_t v___x_3914_; 
v___x_3914_ = 2;
return v___x_3914_;
}
else
{
uint8_t v___x_3915_; 
v___x_3915_ = 0;
return v___x_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21___boxed(lean_object* v_e_3916_){
_start:
{
uint8_t v_res_3917_; lean_object* v_r_3918_; 
v_res_3917_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_e_3916_);
lean_dec_ref(v_e_3916_);
v_r_3918_ = lean_box(v_res_3917_);
return v_r_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(lean_object* v_cls_3919_, uint8_t v_collapsed_3920_, lean_object* v_tag_3921_, lean_object* v_opts_3922_, uint8_t v_clsEnabled_3923_, lean_object* v_oldTraces_3924_, lean_object* v_msg_3925_, lean_object* v_resStartStop_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_fst_3940_; lean_object* v_snd_3941_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v_data_3945_; lean_object* v_fst_3956_; lean_object* v_snd_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; lean_object* v___y_3961_; lean_object* v_a_3962_; uint8_t v___y_3977_; double v___y_4009_; 
v_fst_3940_ = lean_ctor_get(v_resStartStop_3926_, 0);
lean_inc(v_fst_3940_);
v_snd_3941_ = lean_ctor_get(v_resStartStop_3926_, 1);
lean_inc(v_snd_3941_);
lean_dec_ref(v_resStartStop_3926_);
v_fst_3956_ = lean_ctor_get(v_snd_3941_, 0);
lean_inc(v_fst_3956_);
v_snd_3957_ = lean_ctor_get(v_snd_3941_, 1);
lean_inc(v_snd_3957_);
lean_dec(v_snd_3941_);
v___x_3958_ = l_Lean_trace_profiler;
v___x_3959_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_3922_, v___x_3958_);
if (v___x_3959_ == 0)
{
v___y_3977_ = v___x_3959_;
goto v___jp_3976_;
}
else
{
lean_object* v___x_4014_; uint8_t v___x_4015_; 
v___x_4014_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4015_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_3922_, v___x_4014_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; lean_object* v___x_4017_; double v___x_4018_; double v___x_4019_; double v___x_4020_; 
v___x_4016_ = l_Lean_trace_profiler_threshold;
v___x_4017_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_3922_, v___x_4016_);
v___x_4018_ = lean_float_of_nat(v___x_4017_);
v___x_4019_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_4020_ = lean_float_div(v___x_4018_, v___x_4019_);
v___y_4009_ = v___x_4020_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4021_; lean_object* v___x_4022_; double v___x_4023_; 
v___x_4021_ = l_Lean_trace_profiler_threshold;
v___x_4022_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_3922_, v___x_4021_);
v___x_4023_ = lean_float_of_nat(v___x_4022_);
v___y_4009_ = v___x_4023_;
goto v___jp_4008_;
}
}
v___jp_3942_:
{
lean_object* v___x_3946_; 
lean_inc(v___y_3943_);
v___x_3946_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_3924_, v_data_3945_, v___y_3943_, v___y_3944_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v___x_3947_; 
lean_dec_ref_known(v___x_3946_, 1);
v___x_3947_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_3940_);
return v___x_3947_;
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec(v_fst_3940_);
v_a_3948_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3946_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3946_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
v___jp_3960_:
{
uint8_t v_result_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; double v___x_3966_; lean_object* v_data_3967_; 
v_result_3963_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_fst_3940_);
v___x_3964_ = lean_box(v_result_3963_);
v___x_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
v___x_3966_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_3921_);
lean_inc_ref(v___x_3965_);
lean_inc(v_cls_3919_);
v_data_3967_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3967_, 0, v_cls_3919_);
lean_ctor_set(v_data_3967_, 1, v___x_3965_);
lean_ctor_set(v_data_3967_, 2, v_tag_3921_);
lean_ctor_set_float(v_data_3967_, sizeof(void*)*3, v___x_3966_);
lean_ctor_set_float(v_data_3967_, sizeof(void*)*3 + 8, v___x_3966_);
lean_ctor_set_uint8(v_data_3967_, sizeof(void*)*3 + 16, v_collapsed_3920_);
if (v___x_3959_ == 0)
{
lean_dec_ref_known(v___x_3965_, 1);
lean_dec(v_snd_3957_);
lean_dec(v_fst_3956_);
lean_dec_ref(v_tag_3921_);
lean_dec(v_cls_3919_);
v___y_3943_ = v___y_3961_;
v___y_3944_ = v_a_3962_;
v_data_3945_ = v_data_3967_;
goto v___jp_3942_;
}
else
{
lean_object* v_data_3968_; double v___x_3969_; double v___x_3970_; 
lean_dec_ref_known(v_data_3967_, 3);
v_data_3968_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3968_, 0, v_cls_3919_);
lean_ctor_set(v_data_3968_, 1, v___x_3965_);
lean_ctor_set(v_data_3968_, 2, v_tag_3921_);
v___x_3969_ = lean_unbox_float(v_fst_3956_);
lean_dec(v_fst_3956_);
lean_ctor_set_float(v_data_3968_, sizeof(void*)*3, v___x_3969_);
v___x_3970_ = lean_unbox_float(v_snd_3957_);
lean_dec(v_snd_3957_);
lean_ctor_set_float(v_data_3968_, sizeof(void*)*3 + 8, v___x_3970_);
lean_ctor_set_uint8(v_data_3968_, sizeof(void*)*3 + 16, v_collapsed_3920_);
v___y_3943_ = v___y_3961_;
v___y_3944_ = v_a_3962_;
v_data_3945_ = v_data_3968_;
goto v___jp_3942_;
}
}
v___jp_3971_:
{
lean_object* v_ref_3972_; lean_object* v___x_3973_; 
v_ref_3972_ = lean_ctor_get(v___y_3937_, 2);
lean_inc(v___y_3938_);
lean_inc_ref(v___y_3937_);
lean_inc(v___y_3936_);
lean_inc_ref(v___y_3935_);
lean_inc(v___y_3934_);
lean_inc_ref(v___y_3933_);
lean_inc(v___y_3932_);
lean_inc_ref(v___y_3931_);
lean_inc(v___y_3930_);
lean_inc(v___y_3929_);
lean_inc_ref(v___y_3928_);
lean_inc(v___y_3927_);
lean_inc(v_fst_3940_);
v___x_3973_ = lean_apply_14(v_msg_3925_, v_fst_3940_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, lean_box(0));
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v___x_3973_, 1);
v___y_3961_ = v_ref_3972_;
v_a_3962_ = v_a_3974_;
goto v___jp_3960_;
}
else
{
lean_object* v___x_3975_; 
lean_dec_ref_known(v___x_3973_, 1);
v___x_3975_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_3961_ = v_ref_3972_;
v_a_3962_ = v___x_3975_;
goto v___jp_3960_;
}
}
v___jp_3976_:
{
if (v_clsEnabled_3923_ == 0)
{
if (v___y_3977_ == 0)
{
lean_object* v___x_3978_; lean_object* v_traceState_3979_; lean_object* v_env_3980_; lean_object* v_nextMacroScope_3981_; lean_object* v_ngen_3982_; lean_object* v_auxDeclNGen_3983_; lean_object* v_cache_3984_; lean_object* v_recordedDeps_3985_; lean_object* v_messages_3986_; lean_object* v_infoState_3987_; lean_object* v_snapshotTasks_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v_snd_3957_);
lean_dec(v_fst_3956_);
lean_dec_ref(v_msg_3925_);
lean_dec_ref(v_tag_3921_);
lean_dec(v_cls_3919_);
v___x_3978_ = lean_st_ref_take(v___y_3938_);
v_traceState_3979_ = lean_ctor_get(v___x_3978_, 4);
v_env_3980_ = lean_ctor_get(v___x_3978_, 0);
v_nextMacroScope_3981_ = lean_ctor_get(v___x_3978_, 1);
v_ngen_3982_ = lean_ctor_get(v___x_3978_, 2);
v_auxDeclNGen_3983_ = lean_ctor_get(v___x_3978_, 3);
v_cache_3984_ = lean_ctor_get(v___x_3978_, 5);
v_recordedDeps_3985_ = lean_ctor_get(v___x_3978_, 6);
v_messages_3986_ = lean_ctor_get(v___x_3978_, 7);
v_infoState_3987_ = lean_ctor_get(v___x_3978_, 8);
v_snapshotTasks_3988_ = lean_ctor_get(v___x_3978_, 9);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3990_ = v___x_3978_;
v_isShared_3991_ = v_isSharedCheck_4007_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_snapshotTasks_3988_);
lean_inc(v_infoState_3987_);
lean_inc(v_messages_3986_);
lean_inc(v_recordedDeps_3985_);
lean_inc(v_cache_3984_);
lean_inc(v_traceState_3979_);
lean_inc(v_auxDeclNGen_3983_);
lean_inc(v_ngen_3982_);
lean_inc(v_nextMacroScope_3981_);
lean_inc(v_env_3980_);
lean_dec(v___x_3978_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4007_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
uint64_t v_tid_3992_; lean_object* v_traces_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4006_; 
v_tid_3992_ = lean_ctor_get_uint64(v_traceState_3979_, sizeof(void*)*1);
v_traces_3993_ = lean_ctor_get(v_traceState_3979_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_traceState_3979_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3995_ = v_traceState_3979_;
v_isShared_3996_ = v_isSharedCheck_4006_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_traces_3993_);
lean_dec(v_traceState_3979_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4006_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3997_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3924_, v_traces_3993_);
lean_dec_ref(v_traces_3993_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v___x_3997_);
v___x_3999_ = v___x_3995_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3997_);
lean_ctor_set_uint64(v_reuseFailAlloc_4005_, sizeof(void*)*1, v_tid_3992_);
v___x_3999_ = v_reuseFailAlloc_4005_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4001_; 
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 4, v___x_3999_);
v___x_4001_ = v___x_3990_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_env_3980_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_nextMacroScope_3981_);
lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_ngen_3982_);
lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_auxDeclNGen_3983_);
lean_ctor_set(v_reuseFailAlloc_4004_, 4, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4004_, 5, v_cache_3984_);
lean_ctor_set(v_reuseFailAlloc_4004_, 6, v_recordedDeps_3985_);
lean_ctor_set(v_reuseFailAlloc_4004_, 7, v_messages_3986_);
lean_ctor_set(v_reuseFailAlloc_4004_, 8, v_infoState_3987_);
lean_ctor_set(v_reuseFailAlloc_4004_, 9, v_snapshotTasks_3988_);
v___x_4001_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = lean_st_ref_put(v___y_3938_, v___x_4001_);
v___x_4003_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_3940_);
return v___x_4003_;
}
}
}
}
}
else
{
goto v___jp_3971_;
}
}
else
{
goto v___jp_3971_;
}
}
v___jp_4008_:
{
double v___x_4010_; double v___x_4011_; double v___x_4012_; uint8_t v___x_4013_; 
v___x_4010_ = lean_unbox_float(v_snd_3957_);
v___x_4011_ = lean_unbox_float(v_fst_3956_);
v___x_4012_ = lean_float_sub(v___x_4010_, v___x_4011_);
v___x_4013_ = lean_float_decLt(v___y_4009_, v___x_4012_);
v___y_3977_ = v___x_4013_;
goto v___jp_3976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9___boxed(lean_object** _args){
lean_object* v_cls_4024_ = _args[0];
lean_object* v_collapsed_4025_ = _args[1];
lean_object* v_tag_4026_ = _args[2];
lean_object* v_opts_4027_ = _args[3];
lean_object* v_clsEnabled_4028_ = _args[4];
lean_object* v_oldTraces_4029_ = _args[5];
lean_object* v_msg_4030_ = _args[6];
lean_object* v_resStartStop_4031_ = _args[7];
lean_object* v___y_4032_ = _args[8];
lean_object* v___y_4033_ = _args[9];
lean_object* v___y_4034_ = _args[10];
lean_object* v___y_4035_ = _args[11];
lean_object* v___y_4036_ = _args[12];
lean_object* v___y_4037_ = _args[13];
lean_object* v___y_4038_ = _args[14];
lean_object* v___y_4039_ = _args[15];
lean_object* v___y_4040_ = _args[16];
lean_object* v___y_4041_ = _args[17];
lean_object* v___y_4042_ = _args[18];
lean_object* v___y_4043_ = _args[19];
lean_object* v___y_4044_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_4045_; uint8_t v_clsEnabled_boxed_4046_; lean_object* v_res_4047_; 
v_collapsed_boxed_4045_ = lean_unbox(v_collapsed_4025_);
v_clsEnabled_boxed_4046_ = lean_unbox(v_clsEnabled_4028_);
v_res_4047_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4024_, v_collapsed_boxed_4045_, v_tag_4026_, v_opts_4027_, v_clsEnabled_boxed_4046_, v_oldTraces_4029_, v_msg_4030_, v_resStartStop_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v_opts_4027_);
return v_res_4047_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v_cls_4057_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_4058_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_4059_ = l_Lean_Name_append(v___x_4058_, v_cls_4057_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_4063_, lean_object* v_goal_4064_, lean_object* v_reflectionResult_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_satExpr_4079_; lean_object* v_unusedHypotheses_4080_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v_toCold_4214_; lean_object* v_options_4215_; lean_object* v_bvExpr_4216_; lean_object* v_ref_4217_; lean_object* v_inheritedTraceOptions_4218_; uint8_t v_hasTrace_4219_; lean_object* v___f_4220_; lean_object* v___f_4221_; lean_object* v___f_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v_cls_4226_; lean_object* v___f_4227_; lean_object* v___f_4228_; uint8_t v___x_4229_; lean_object* v___x_4230_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; uint8_t v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v_a_4250_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; uint8_t v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v_a_4278_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; uint8_t v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; uint8_t v___y_4302_; uint8_t v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; uint8_t v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; uint8_t v___y_4422_; lean_object* v___y_4423_; lean_object* v_a_4424_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; uint8_t v___y_4450_; lean_object* v___y_4451_; lean_object* v_a_4452_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; uint8_t v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v_toCold_4554_; lean_object* v_ref_4555_; lean_object* v___y_4556_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v_entry_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; 
v_satExpr_4079_ = lean_ctor_get(v_reflectionResult_4065_, 0);
v_unusedHypotheses_4080_ = lean_ctor_get(v_reflectionResult_4065_, 1);
v_toCold_4214_ = lean_ctor_get(v_a_4076_, 0);
v_options_4215_ = lean_ctor_get(v_toCold_4214_, 2);
v_bvExpr_4216_ = lean_ctor_get(v_satExpr_4079_, 0);
v_ref_4217_ = lean_ctor_get(v_a_4076_, 2);
v_inheritedTraceOptions_4218_ = lean_ctor_get(v_toCold_4214_, 11);
v_hasTrace_4219_ = lean_ctor_get_uint8(v_options_4215_, sizeof(void*)*1);
v___f_4220_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_4221_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_4222_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_4223_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_4224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_4225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v_cls_4226_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
lean_inc_ref(v_bvExpr_4216_);
v___f_4227_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4227_, 0, v_bvExpr_4216_);
lean_inc_ref(v___f_4227_);
v___f_4228_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed), 13, 1);
lean_closure_set(v___f_4228_, 0, v___f_4227_);
v___x_4229_ = 1;
v___x_4230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_4219_ == 0)
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4228_, v_cls_4226_, v___x_4229_, v___x_4230_, v___f_4222_, v___f_4227_, v_options_4215_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v___x_4655_, 1);
v_entry_4614_ = v_a_4656_;
v___y_4615_ = v_a_4066_;
v___y_4616_ = v_a_4067_;
v___y_4617_ = v_a_4068_;
v___y_4618_ = v_a_4069_;
v___y_4619_ = v_a_4070_;
v___y_4620_ = v_a_4071_;
v___y_4621_ = v_a_4072_;
v___y_4622_ = v_a_4073_;
v___y_4623_ = v_a_4074_;
v___y_4624_ = v_a_4075_;
v___y_4625_ = v_a_4076_;
v___y_4626_ = v_a_4077_;
goto v___jp_4613_;
}
else
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4664_; 
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4657_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4659_ = v___x_4655_;
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4655_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4662_; 
if (v_isShared_4660_ == 0)
{
v___x_4662_ = v___x_4659_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
}
else
{
lean_object* v___f_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v_a_4671_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v_a_4683_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4699_; lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4731_; lean_object* v___y_4732_; lean_object* v___y_4733_; lean_object* v___y_4734_; uint8_t v___y_4735_; lean_object* v___y_4736_; lean_object* v_a_4737_; lean_object* v___y_4747_; uint8_t v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v_a_4784_; lean_object* v___y_4797_; lean_object* v___y_4798_; lean_object* v_a_4799_; lean_object* v___y_4802_; lean_object* v___y_4803_; lean_object* v___y_4804_; lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v___y_4847_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___y_4850_; uint8_t v___y_4851_; lean_object* v___y_4852_; lean_object* v_a_4853_; lean_object* v___y_4866_; lean_object* v___y_4867_; lean_object* v___y_4868_; uint8_t v___y_4869_; 
v___f_4665_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_4666_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4218_, v_options_4215_, v___x_4666_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4913_; uint8_t v___x_4914_; 
v___x_4913_ = l_Lean_trace_profiler;
v___x_4914_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4215_, v___x_4913_);
if (v___x_4914_ == 0)
{
lean_object* v___x_4915_; 
v___x_4915_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4228_, v_cls_4226_, v___x_4229_, v___x_4230_, v___f_4222_, v___f_4227_, v_options_4215_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v___x_4915_, 1);
v_entry_4614_ = v_a_4916_;
v___y_4615_ = v_a_4066_;
v___y_4616_ = v_a_4067_;
v___y_4617_ = v_a_4068_;
v___y_4618_ = v_a_4069_;
v___y_4619_ = v_a_4070_;
v___y_4620_ = v_a_4071_;
v___y_4621_ = v_a_4072_;
v___y_4622_ = v_a_4073_;
v___y_4623_ = v_a_4074_;
v___y_4624_ = v_a_4075_;
v___y_4625_ = v_a_4076_;
v___y_4626_ = v_a_4077_;
goto v___jp_4613_;
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4917_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4915_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4915_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4080_);
lean_inc_ref(v_satExpr_4079_);
lean_dec_ref(v___f_4228_);
goto v___jp_4900_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4080_);
lean_inc_ref(v_satExpr_4079_);
lean_dec_ref(v___f_4228_);
goto v___jp_4900_;
}
v___jp_4668_:
{
lean_object* v___x_4672_; double v___x_4673_; double v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4672_ = lean_io_get_num_heartbeats();
v___x_4673_ = lean_float_of_nat(v___y_4670_);
v___x_4674_ = lean_float_of_nat(v___x_4672_);
v___x_4675_ = lean_box_float(v___x_4673_);
v___x_4676_ = lean_box_float(v___x_4674_);
v___x_4677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4675_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
v___x_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4678_, 0, v_a_4671_);
lean_ctor_set(v___x_4678_, 1, v___x_4677_);
v___x_4679_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4226_, v___x_4229_, v___x_4230_, v_options_4215_, v___x_4667_, v___y_4669_, v___f_4665_, v___x_4678_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
return v___x_4679_;
}
v___jp_4680_:
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4684_, 0, v_a_4683_);
v___y_4669_ = v___y_4681_;
v___y_4670_ = v___y_4682_;
v_a_4671_ = v___x_4684_;
goto v___jp_4668_;
}
v___jp_4685_:
{
if (lean_obj_tag(v___y_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
v_a_4689_ = lean_ctor_get(v___y_4688_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___y_4688_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___y_4688_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___y_4688_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set_tag(v___x_4691_, 1);
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
v___y_4669_ = v___y_4686_;
v___y_4670_ = v___y_4687_;
v_a_4671_ = v___x_4694_;
goto v___jp_4668_;
}
}
}
else
{
lean_object* v_a_4697_; 
v_a_4697_ = lean_ctor_get(v___y_4688_, 0);
lean_inc(v_a_4697_);
lean_dec_ref_known(v___y_4688_, 1);
v___y_4681_ = v___y_4686_;
v___y_4682_ = v___y_4687_;
v_a_4683_ = v_a_4697_;
goto v___jp_4680_;
}
}
v___jp_4698_:
{
if (lean_obj_tag(v___y_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4728_; 
v_a_4703_ = lean_ctor_get(v___y_4702_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___y_4702_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4705_ = v___y_4702_;
v_isShared_4706_ = v_isSharedCheck_4728_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___y_4702_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4728_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v_aig_4707_; lean_object* v_ref_4708_; lean_object* v_decls_4709_; lean_object* v___f_4710_; lean_object* v___f_4711_; 
v_aig_4707_ = lean_ctor_get(v_a_4703_, 0);
lean_inc_ref_n(v_aig_4707_, 2);
v_ref_4708_ = lean_ctor_get(v_a_4703_, 1);
v_decls_4709_ = lean_ctor_get(v_aig_4707_, 0);
lean_inc_ref(v_ref_4708_);
lean_inc(v_a_4703_);
v___f_4710_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed), 5, 4);
lean_closure_set(v___f_4710_, 0, v_aig_4707_);
lean_closure_set(v___f_4710_, 1, v___x_4223_);
lean_closure_set(v___f_4710_, 2, v_a_4703_);
lean_closure_set(v___f_4710_, 3, v_ref_4708_);
lean_inc_ref(v___f_4710_);
v___f_4711_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4711_, 0, v___f_4710_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4712_; lean_object* v___x_4713_; 
lean_del_object(v___x_4705_);
v___x_4712_ = lean_box(0);
v___x_4713_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4063_, v_aig_4707_, v_goal_4064_, v_unusedHypotheses_4080_, v_reflectionResult_4065_, v_satExpr_4079_, v___x_4229_, v___x_4230_, v___f_4220_, v___y_4699_, v___f_4221_, v___f_4710_, v___x_4224_, v___x_4225_, v___f_4711_, v_a_4703_, v___x_4712_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
v___y_4686_ = v___y_4700_;
v___y_4687_ = v___y_4701_;
v___y_4688_ = v___x_4713_;
goto v___jp_4685_;
}
else
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4721_; 
v___x_4714_ = lean_array_get_size(v_decls_4709_);
v___x_4715_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4716_ = l_Nat_reprFast(v___x_4714_);
v___x_4717_ = lean_string_append(v___x_4715_, v___x_4716_);
lean_dec_ref(v___x_4716_);
v___x_4718_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4719_ = lean_string_append(v___x_4717_, v___x_4718_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set_tag(v___x_4705_, 3);
lean_ctor_set(v___x_4705_, 0, v___x_4719_);
v___x_4721_ = v___x_4705_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = l_Lean_MessageData_ofFormat(v___x_4721_);
v___x_4723_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4226_, v___x_4722_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; lean_object* v___x_4725_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v___x_4725_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4063_, v_aig_4707_, v_goal_4064_, v_unusedHypotheses_4080_, v_reflectionResult_4065_, v_satExpr_4079_, v___x_4229_, v___x_4230_, v___f_4220_, v___y_4699_, v___f_4221_, v___f_4710_, v___x_4224_, v___x_4225_, v___f_4711_, v_a_4703_, v_a_4724_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
v___y_4686_ = v___y_4700_;
v___y_4687_ = v___y_4701_;
v___y_4688_ = v___x_4725_;
goto v___jp_4685_;
}
else
{
lean_object* v_a_4726_; 
lean_dec_ref(v___f_4711_);
lean_dec_ref(v___f_4710_);
lean_dec_ref(v_aig_4707_);
lean_dec(v_a_4703_);
lean_dec_ref(v_unusedHypotheses_4080_);
lean_dec_ref(v_satExpr_4079_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4726_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4726_);
lean_dec_ref_known(v___x_4723_, 1);
v___y_4681_ = v___y_4700_;
v___y_4682_ = v___y_4701_;
v_a_4683_ = v_a_4726_;
goto v___jp_4680_;
}
}
}
}
}
else
{
lean_object* v_a_4729_; 
lean_dec_ref(v_unusedHypotheses_4080_);
lean_dec_ref(v_satExpr_4079_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4729_ = lean_ctor_get(v___y_4702_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v___y_4702_, 1);
v___y_4681_ = v___y_4700_;
v___y_4682_ = v___y_4701_;
v_a_4683_ = v_a_4729_;
goto v___jp_4680_;
}
}
v___jp_4730_:
{
lean_object* v___x_4738_; double v___x_4739_; double v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4738_ = lean_io_get_num_heartbeats();
v___x_4739_ = lean_float_of_nat(v___y_4732_);
v___x_4740_ = lean_float_of_nat(v___x_4738_);
v___x_4741_ = lean_box_float(v___x_4739_);
v___x_4742_ = lean_box_float(v___x_4740_);
v___x_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4741_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4744_, 0, v_a_4737_);
lean_ctor_set(v___x_4744_, 1, v___x_4743_);
v___x_4745_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4226_, v___x_4229_, v___x_4230_, v_options_4215_, v___y_4735_, v___y_4733_, v___f_4222_, v___x_4744_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
v___y_4699_ = v___y_4731_;
v___y_4700_ = v___y_4734_;
v___y_4701_ = v___y_4736_;
v___y_4702_ = v___x_4745_;
goto v___jp_4698_;
}
v___jp_4746_:
{
lean_object* v___x_4751_; lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4780_; 
v___x_4751_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4077_);
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4754_ = v___x_4751_;
v_isShared_4755_ = v_isSharedCheck_4780_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4751_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4780_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4756_ = lean_io_get_num_heartbeats();
v___x_4757_ = l_IO_lazyPure___redArg(v___f_4227_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_del_object(v___x_4754_);
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4757_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4757_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
lean_ctor_set_tag(v___x_4760_, 1);
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
v___y_4731_ = v___y_4747_;
v___y_4732_ = v___x_4756_;
v___y_4733_ = v_a_4752_;
v___y_4734_ = v___y_4749_;
v___y_4735_ = v___y_4748_;
v___y_4736_ = v___y_4750_;
v_a_4737_ = v___x_4763_;
goto v___jp_4730_;
}
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4779_; 
v_a_4766_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4768_ = v___x_4757_;
v_isShared_4769_ = v_isSharedCheck_4779_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4757_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4779_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4770_; lean_object* v___x_4772_; 
v___x_4770_ = lean_io_error_to_string(v_a_4766_);
if (v_isShared_4769_ == 0)
{
lean_ctor_set_tag(v___x_4768_, 3);
lean_ctor_set(v___x_4768_, 0, v___x_4770_);
v___x_4772_ = v___x_4768_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4770_);
v___x_4772_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4776_; 
v___x_4773_ = l_Lean_MessageData_ofFormat(v___x_4772_);
lean_inc(v_ref_4217_);
v___x_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4774_, 0, v_ref_4217_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 0, v___x_4774_);
v___x_4776_ = v___x_4754_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4774_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
v___y_4731_ = v___y_4747_;
v___y_4732_ = v___x_4756_;
v___y_4733_ = v_a_4752_;
v___y_4734_ = v___y_4749_;
v___y_4735_ = v___y_4748_;
v___y_4736_ = v___y_4750_;
v_a_4737_ = v___x_4776_;
goto v___jp_4730_;
}
}
}
}
}
}
v___jp_4781_:
{
lean_object* v___x_4785_; double v___x_4786_; double v___x_4787_; double v___x_4788_; double v___x_4789_; double v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4785_ = lean_io_mono_nanos_now();
v___x_4786_ = lean_float_of_nat(v___y_4782_);
v___x_4787_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4788_ = lean_float_div(v___x_4786_, v___x_4787_);
v___x_4789_ = lean_float_of_nat(v___x_4785_);
v___x_4790_ = lean_float_div(v___x_4789_, v___x_4787_);
v___x_4791_ = lean_box_float(v___x_4788_);
v___x_4792_ = lean_box_float(v___x_4790_);
v___x_4793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4791_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
v___x_4794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4794_, 0, v_a_4784_);
lean_ctor_set(v___x_4794_, 1, v___x_4793_);
v___x_4795_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4226_, v___x_4229_, v___x_4230_, v_options_4215_, v___x_4667_, v___y_4783_, v___f_4665_, v___x_4794_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
return v___x_4795_;
}
v___jp_4796_:
{
lean_object* v___x_4800_; 
v___x_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4800_, 0, v_a_4799_);
v___y_4782_ = v___y_4797_;
v___y_4783_ = v___y_4798_;
v_a_4784_ = v___x_4800_;
goto v___jp_4781_;
}
v___jp_4801_:
{
if (lean_obj_tag(v___y_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
v_a_4805_ = lean_ctor_get(v___y_4804_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___y_4804_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___y_4804_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___y_4804_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
lean_ctor_set_tag(v___x_4807_, 1);
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
v___y_4782_ = v___y_4802_;
v___y_4783_ = v___y_4803_;
v_a_4784_ = v___x_4810_;
goto v___jp_4781_;
}
}
}
else
{
lean_object* v_a_4813_; 
v_a_4813_ = lean_ctor_get(v___y_4804_, 0);
lean_inc(v_a_4813_);
lean_dec_ref_known(v___y_4804_, 1);
v___y_4797_ = v___y_4802_;
v___y_4798_ = v___y_4803_;
v_a_4799_ = v_a_4813_;
goto v___jp_4796_;
}
}
v___jp_4814_:
{
if (lean_obj_tag(v___y_4818_) == 0)
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4844_; 
v_a_4819_ = lean_ctor_get(v___y_4818_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___y_4818_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4821_ = v___y_4818_;
v_isShared_4822_ = v_isSharedCheck_4844_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___y_4818_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4844_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v_aig_4823_; lean_object* v_ref_4824_; lean_object* v_decls_4825_; lean_object* v___f_4826_; lean_object* v___f_4827_; 
v_aig_4823_ = lean_ctor_get(v_a_4819_, 0);
lean_inc_ref_n(v_aig_4823_, 2);
v_ref_4824_ = lean_ctor_get(v_a_4819_, 1);
v_decls_4825_ = lean_ctor_get(v_aig_4823_, 0);
lean_inc_ref(v_ref_4824_);
lean_inc(v_a_4819_);
v___f_4826_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed), 5, 4);
lean_closure_set(v___f_4826_, 0, v_aig_4823_);
lean_closure_set(v___f_4826_, 1, v___x_4223_);
lean_closure_set(v___f_4826_, 2, v_a_4819_);
lean_closure_set(v___f_4826_, 3, v_ref_4824_);
lean_inc_ref(v___f_4826_);
v___f_4827_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4827_, 0, v___f_4826_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
lean_del_object(v___x_4821_);
v___x_4828_ = lean_box(0);
v___x_4829_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4063_, v_aig_4823_, v_goal_4064_, v_unusedHypotheses_4080_, v_reflectionResult_4065_, v_satExpr_4079_, v___x_4229_, v___x_4230_, v___f_4220_, v___y_4815_, v___f_4221_, v___f_4826_, v___x_4224_, v___x_4225_, v___f_4827_, v_a_4819_, v___x_4828_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
v___y_4802_ = v___y_4816_;
v___y_4803_ = v___y_4817_;
v___y_4804_ = v___x_4829_;
goto v___jp_4801_;
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4837_; 
v___x_4830_ = lean_array_get_size(v_decls_4825_);
v___x_4831_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4832_ = l_Nat_reprFast(v___x_4830_);
v___x_4833_ = lean_string_append(v___x_4831_, v___x_4832_);
lean_dec_ref(v___x_4832_);
v___x_4834_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4835_ = lean_string_append(v___x_4833_, v___x_4834_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set_tag(v___x_4821_, 3);
lean_ctor_set(v___x_4821_, 0, v___x_4835_);
v___x_4837_ = v___x_4821_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4835_);
v___x_4837_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4838_ = l_Lean_MessageData_ofFormat(v___x_4837_);
v___x_4839_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4226_, v___x_4838_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4841_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4840_);
lean_dec_ref_known(v___x_4839_, 1);
v___x_4841_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4063_, v_aig_4823_, v_goal_4064_, v_unusedHypotheses_4080_, v_reflectionResult_4065_, v_satExpr_4079_, v___x_4229_, v___x_4230_, v___f_4220_, v___y_4815_, v___f_4221_, v___f_4826_, v___x_4224_, v___x_4225_, v___f_4827_, v_a_4819_, v_a_4840_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
v___y_4802_ = v___y_4816_;
v___y_4803_ = v___y_4817_;
v___y_4804_ = v___x_4841_;
goto v___jp_4801_;
}
else
{
lean_object* v_a_4842_; 
lean_dec_ref(v___f_4827_);
lean_dec_ref(v___f_4826_);
lean_dec_ref(v_aig_4823_);
lean_dec(v_a_4819_);
lean_dec_ref(v_unusedHypotheses_4080_);
lean_dec_ref(v_satExpr_4079_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4842_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4842_);
lean_dec_ref_known(v___x_4839_, 1);
v___y_4797_ = v___y_4816_;
v___y_4798_ = v___y_4817_;
v_a_4799_ = v_a_4842_;
goto v___jp_4796_;
}
}
}
}
}
else
{
lean_object* v_a_4845_; 
lean_dec_ref(v_unusedHypotheses_4080_);
lean_dec_ref(v_satExpr_4079_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4845_ = lean_ctor_get(v___y_4818_, 0);
lean_inc(v_a_4845_);
lean_dec_ref_known(v___y_4818_, 1);
v___y_4797_ = v___y_4816_;
v___y_4798_ = v___y_4817_;
v_a_4799_ = v_a_4845_;
goto v___jp_4796_;
}
}
v___jp_4846_:
{
lean_object* v___x_4854_; double v___x_4855_; double v___x_4856_; double v___x_4857_; double v___x_4858_; double v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4854_ = lean_io_mono_nanos_now();
v___x_4855_ = lean_float_of_nat(v___y_4852_);
v___x_4856_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4857_ = lean_float_div(v___x_4855_, v___x_4856_);
v___x_4858_ = lean_float_of_nat(v___x_4854_);
v___x_4859_ = lean_float_div(v___x_4858_, v___x_4856_);
v___x_4860_ = lean_box_float(v___x_4857_);
v___x_4861_ = lean_box_float(v___x_4859_);
v___x_4862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4860_);
lean_ctor_set(v___x_4862_, 1, v___x_4861_);
v___x_4863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4863_, 0, v_a_4853_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
v___x_4864_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4226_, v___x_4229_, v___x_4230_, v_options_4215_, v___y_4851_, v___y_4848_, v___f_4222_, v___x_4863_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
v___y_4815_ = v___y_4847_;
v___y_4816_ = v___y_4849_;
v___y_4817_ = v___y_4850_;
v___y_4818_ = v___x_4864_;
goto v___jp_4814_;
}
v___jp_4865_:
{
lean_object* v___x_4870_; lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4899_; 
v___x_4870_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4077_);
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4899_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4899_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_io_mono_nanos_now();
v___x_4876_ = l_IO_lazyPure___redArg(v___f_4227_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_del_object(v___x_4873_);
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4876_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4876_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
lean_ctor_set_tag(v___x_4879_, 1);
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
v___y_4847_ = v___y_4866_;
v___y_4848_ = v_a_4871_;
v___y_4849_ = v___y_4867_;
v___y_4850_ = v___y_4868_;
v___y_4851_ = v___y_4869_;
v___y_4852_ = v___x_4875_;
v_a_4853_ = v___x_4882_;
goto v___jp_4846_;
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4898_; 
v_a_4885_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4887_ = v___x_4876_;
v_isShared_4888_ = v_isSharedCheck_4898_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4876_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4898_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4889_ = lean_io_error_to_string(v_a_4885_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set_tag(v___x_4887_, 3);
lean_ctor_set(v___x_4887_, 0, v___x_4889_);
v___x_4891_ = v___x_4887_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4892_ = l_Lean_MessageData_ofFormat(v___x_4891_);
lean_inc(v_ref_4217_);
v___x_4893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4893_, 0, v_ref_4217_);
lean_ctor_set(v___x_4893_, 1, v___x_4892_);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4893_);
v___x_4895_ = v___x_4873_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
v___y_4847_ = v___y_4866_;
v___y_4848_ = v_a_4871_;
v___y_4849_ = v___y_4867_;
v___y_4850_ = v___y_4868_;
v___y_4851_ = v___y_4869_;
v___y_4852_ = v___x_4875_;
v_a_4853_ = v___x_4895_;
goto v___jp_4846_;
}
}
}
}
}
}
v___jp_4900_:
{
lean_object* v___x_4901_; lean_object* v_a_4902_; lean_object* v___x_4903_; uint8_t v___x_4904_; 
v___x_4901_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4077_);
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc(v_a_4902_);
lean_dec_ref(v___x_4901_);
v___x_4903_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4904_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4215_, v___x_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; 
v___x_4905_ = lean_io_mono_nanos_now();
if (v___x_4667_ == 0)
{
lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4906_ = l_Lean_trace_profiler;
v___x_4907_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4215_, v___x_4906_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; 
v___x_4908_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4227_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
v___y_4815_ = v___x_4903_;
v___y_4816_ = v___x_4905_;
v___y_4817_ = v_a_4902_;
v___y_4818_ = v___x_4908_;
goto v___jp_4814_;
}
else
{
v___y_4866_ = v___x_4903_;
v___y_4867_ = v___x_4905_;
v___y_4868_ = v_a_4902_;
v___y_4869_ = v___x_4667_;
goto v___jp_4865_;
}
}
else
{
v___y_4866_ = v___x_4903_;
v___y_4867_ = v___x_4905_;
v___y_4868_ = v_a_4902_;
v___y_4869_ = v___x_4667_;
goto v___jp_4865_;
}
}
else
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_io_get_num_heartbeats();
if (v___x_4667_ == 0)
{
lean_object* v___x_4910_; uint8_t v___x_4911_; 
v___x_4910_ = l_Lean_trace_profiler;
v___x_4911_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4215_, v___x_4910_);
if (v___x_4911_ == 0)
{
lean_object* v___x_4912_; 
v___x_4912_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4227_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
v___y_4699_ = v___x_4903_;
v___y_4700_ = v_a_4902_;
v___y_4701_ = v___x_4909_;
v___y_4702_ = v___x_4912_;
goto v___jp_4698_;
}
else
{
v___y_4747_ = v___x_4903_;
v___y_4748_ = v___x_4667_;
v___y_4749_ = v_a_4902_;
v___y_4750_ = v___x_4909_;
goto v___jp_4746_;
}
}
else
{
v___y_4747_ = v___x_4903_;
v___y_4748_ = v___x_4667_;
v___y_4749_ = v_a_4902_;
v___y_4750_ = v___x_4909_;
goto v___jp_4746_;
}
}
}
}
v___jp_4081_:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_4084_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4100_; 
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4088_ = v___x_4085_;
v_isShared_4089_ = v_isSharedCheck_4100_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4085_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4100_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4090_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_4082_, v___y_4083_, v_a_4086_);
lean_dec(v_a_4086_);
lean_dec_ref(v___y_4083_);
v___x_4091_ = lean_unsigned_to_nat(0u);
v___x_4092_ = lean_array_get_size(v___x_4090_);
v___x_4093_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_4090_, v___x_4091_, v___x_4092_);
lean_dec_ref(v___x_4090_);
v___x_4094_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_4095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4095_, 0, v_goal_4064_);
lean_ctor_set(v___x_4095_, 1, v_unusedHypotheses_4080_);
lean_ctor_set(v___x_4095_, 2, v___x_4093_);
lean_ctor_set(v___x_4095_, 3, v___x_4094_);
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
if (v_isShared_4089_ == 0)
{
lean_ctor_set(v___x_4088_, 0, v___x_4096_);
v___x_4098_ = v___x_4088_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec_ref(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec_ref(v_unusedHypotheses_4080_);
lean_dec(v_goal_4064_);
v_a_4101_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4085_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4085_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
v___jp_4109_:
{
lean_object* v___x_4122_; 
lean_inc_ref(v___y_4110_);
v___x_4122_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_4110_, v_ctx_4063_, v_reflectionResult_4065_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4124_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref_known(v___x_4122_, 1);
v___x_4124_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_4079_, v_a_4123_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4134_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v___x_4124_, 1);
v___x_4126_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_4064_, v_a_4125_, v___y_4119_);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4134_ == 0)
{
lean_object* v_unused_4135_; 
v_unused_4135_ = lean_ctor_get(v___x_4126_, 0);
lean_dec(v_unused_4135_);
v___x_4128_ = v___x_4126_;
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
else
{
lean_dec(v___x_4126_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; lean_object* v___x_4132_; 
v___x_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___y_4110_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4130_);
v___x_4132_ = v___x_4128_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v___y_4110_);
lean_dec(v_goal_4064_);
v_a_4136_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4124_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4124_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v___y_4110_);
lean_dec_ref(v_satExpr_4079_);
lean_dec(v_goal_4064_);
v_a_4144_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4122_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4122_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
v___jp_4152_:
{
if (lean_obj_tag(v___y_4166_) == 0)
{
lean_object* v_a_4167_; 
v_a_4167_ = lean_ctor_get(v___y_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___y_4166_, 1);
if (lean_obj_tag(v_a_4167_) == 0)
{
lean_object* v_toCold_4168_; lean_object* v_options_4169_; uint8_t v_hasTrace_4170_; 
lean_inc_ref(v_unusedHypotheses_4080_);
lean_dec_ref(v_satExpr_4079_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec_ref(v_ctx_4063_);
v_toCold_4168_ = lean_ctor_get(v___y_4163_, 0);
v_options_4169_ = lean_ctor_get(v_toCold_4168_, 2);
v_hasTrace_4170_ = lean_ctor_get_uint8(v_options_4169_, sizeof(void*)*1);
if (v_hasTrace_4170_ == 0)
{
lean_object* v_a_4171_; 
v_a_4171_ = lean_ctor_get(v_a_4167_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v_a_4167_, 1);
v___y_4082_ = v___y_4153_;
v___y_4083_ = v_a_4171_;
v___y_4084_ = v___y_4158_;
goto v___jp_4081_;
}
else
{
lean_object* v_a_4172_; lean_object* v_inheritedTraceOptions_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v_a_4172_ = lean_ctor_get(v_a_4167_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v_a_4167_, 1);
v_inheritedTraceOptions_4173_ = lean_ctor_get(v_toCold_4168_, 11);
v___x_4174_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4164_);
v___x_4175_ = l_Lean_Name_append(v___x_4174_, v___y_4164_);
v___x_4176_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4173_, v_options_4169_, v___x_4175_);
lean_dec(v___x_4175_);
if (v___x_4176_ == 0)
{
v___y_4082_ = v___y_4153_;
v___y_4083_ = v_a_4172_;
v___y_4084_ = v___y_4158_;
goto v___jp_4081_;
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
lean_inc(v___y_4164_);
v___x_4178_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4164_, v___x_4177_, v___y_4162_, v___y_4154_, v___y_4163_, v___y_4156_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_dec_ref_known(v___x_4178_, 1);
v___y_4082_ = v___y_4153_;
v___y_4083_ = v_a_4172_;
v___y_4084_ = v___y_4158_;
goto v___jp_4081_;
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec(v_a_4172_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v_unusedHypotheses_4080_);
lean_dec(v_goal_4064_);
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4178_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4178_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4187_; lean_object* v_options_4188_; uint8_t v_hasTrace_4189_; 
lean_dec_ref(v___y_4153_);
v_toCold_4187_ = lean_ctor_get(v___y_4163_, 0);
v_options_4188_ = lean_ctor_get(v_toCold_4187_, 2);
v_hasTrace_4189_ = lean_ctor_get_uint8(v_options_4188_, sizeof(void*)*1);
if (v_hasTrace_4189_ == 0)
{
lean_object* v_a_4190_; 
v_a_4190_ = lean_ctor_get(v_a_4167_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v_a_4167_, 1);
v___y_4110_ = v_a_4190_;
v___y_4111_ = v___y_4161_;
v___y_4112_ = v___y_4158_;
v___y_4113_ = v___y_4159_;
v___y_4114_ = v___y_4155_;
v___y_4115_ = v___y_4157_;
v___y_4116_ = v___y_4165_;
v___y_4117_ = v___y_4160_;
v___y_4118_ = v___y_4162_;
v___y_4119_ = v___y_4154_;
v___y_4120_ = v___y_4163_;
v___y_4121_ = v___y_4156_;
goto v___jp_4109_;
}
else
{
lean_object* v_a_4191_; lean_object* v_inheritedTraceOptions_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; uint8_t v___x_4195_; 
v_a_4191_ = lean_ctor_get(v_a_4167_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v_a_4167_, 1);
v_inheritedTraceOptions_4192_ = lean_ctor_get(v_toCold_4187_, 11);
v___x_4193_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4164_);
v___x_4194_ = l_Lean_Name_append(v___x_4193_, v___y_4164_);
v___x_4195_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4192_, v_options_4188_, v___x_4194_);
lean_dec(v___x_4194_);
if (v___x_4195_ == 0)
{
v___y_4110_ = v_a_4191_;
v___y_4111_ = v___y_4161_;
v___y_4112_ = v___y_4158_;
v___y_4113_ = v___y_4159_;
v___y_4114_ = v___y_4155_;
v___y_4115_ = v___y_4157_;
v___y_4116_ = v___y_4165_;
v___y_4117_ = v___y_4160_;
v___y_4118_ = v___y_4162_;
v___y_4119_ = v___y_4154_;
v___y_4120_ = v___y_4163_;
v___y_4121_ = v___y_4156_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
lean_inc(v___y_4164_);
v___x_4197_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4164_, v___x_4196_, v___y_4162_, v___y_4154_, v___y_4163_, v___y_4156_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_dec_ref_known(v___x_4197_, 1);
v___y_4110_ = v_a_4191_;
v___y_4111_ = v___y_4161_;
v___y_4112_ = v___y_4158_;
v___y_4113_ = v___y_4159_;
v___y_4114_ = v___y_4155_;
v___y_4115_ = v___y_4157_;
v___y_4116_ = v___y_4165_;
v___y_4117_ = v___y_4160_;
v___y_4118_ = v___y_4162_;
v___y_4119_ = v___y_4154_;
v___y_4120_ = v___y_4163_;
v___y_4121_ = v___y_4156_;
goto v___jp_4109_;
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_a_4191_);
lean_dec_ref(v_satExpr_4079_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4197_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v___y_4153_);
lean_dec_ref(v_satExpr_4079_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4206_ = lean_ctor_get(v___y_4166_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___y_4166_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___y_4166_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___y_4166_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
v___jp_4231_:
{
lean_object* v___x_4251_; double v___x_4252_; double v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4251_ = lean_io_get_num_heartbeats();
v___x_4252_ = lean_float_of_nat(v___y_4235_);
v___x_4253_ = lean_float_of_nat(v___x_4251_);
v___x_4254_ = lean_box_float(v___x_4252_);
v___x_4255_ = lean_box_float(v___x_4253_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4254_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4257_, 0, v_a_4250_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
lean_inc(v___y_4247_);
v___x_4258_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4247_, v___x_4229_, v___x_4230_, v___y_4237_, v___y_4240_, v___y_4248_, v___f_4220_, v___x_4257_, v___y_4238_, v___y_4244_, v___y_4241_, v___y_4242_, v___y_4234_, v___y_4239_, v___y_4249_, v___y_4243_, v___y_4245_, v___y_4233_, v___y_4246_, v___y_4236_);
v___y_4153_ = v___y_4232_;
v___y_4154_ = v___y_4233_;
v___y_4155_ = v___y_4234_;
v___y_4156_ = v___y_4236_;
v___y_4157_ = v___y_4239_;
v___y_4158_ = v___y_4241_;
v___y_4159_ = v___y_4242_;
v___y_4160_ = v___y_4243_;
v___y_4161_ = v___y_4244_;
v___y_4162_ = v___y_4245_;
v___y_4163_ = v___y_4246_;
v___y_4164_ = v___y_4247_;
v___y_4165_ = v___y_4249_;
v___y_4166_ = v___x_4258_;
goto v___jp_4152_;
}
v___jp_4259_:
{
lean_object* v___x_4279_; double v___x_4280_; double v___x_4281_; double v___x_4282_; double v___x_4283_; double v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4279_ = lean_io_mono_nanos_now();
v___x_4280_ = lean_float_of_nat(v___y_4273_);
v___x_4281_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4282_ = lean_float_div(v___x_4280_, v___x_4281_);
v___x_4283_ = lean_float_of_nat(v___x_4279_);
v___x_4284_ = lean_float_div(v___x_4283_, v___x_4281_);
v___x_4285_ = lean_box_float(v___x_4282_);
v___x_4286_ = lean_box_float(v___x_4284_);
v___x_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4288_, 0, v_a_4278_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
lean_inc(v___y_4275_);
v___x_4289_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4275_, v___x_4229_, v___x_4230_, v___y_4264_, v___y_4267_, v___y_4276_, v___f_4220_, v___x_4288_, v___y_4265_, v___y_4271_, v___y_4268_, v___y_4269_, v___y_4262_, v___y_4266_, v___y_4277_, v___y_4270_, v___y_4272_, v___y_4261_, v___y_4274_, v___y_4263_);
v___y_4153_ = v___y_4260_;
v___y_4154_ = v___y_4261_;
v___y_4155_ = v___y_4262_;
v___y_4156_ = v___y_4263_;
v___y_4157_ = v___y_4266_;
v___y_4158_ = v___y_4268_;
v___y_4159_ = v___y_4269_;
v___y_4160_ = v___y_4270_;
v___y_4161_ = v___y_4271_;
v___y_4162_ = v___y_4272_;
v___y_4163_ = v___y_4274_;
v___y_4164_ = v___y_4275_;
v___y_4165_ = v___y_4277_;
v___y_4166_ = v___x_4289_;
goto v___jp_4152_;
}
v___jp_4290_:
{
lean_object* v___x_4314_; lean_object* v_a_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4314_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4297_);
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref(v___x_4314_);
v___x_4316_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4317_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4298_, v___x_4316_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_io_mono_nanos_now();
v___x_4319_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4291_, v___y_4296_, v___y_4312_, v___y_4311_, v___y_4294_, v___y_4299_, v___y_4302_, v___y_4309_, v___y_4297_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set_tag(v___x_4322_, 1);
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
v___y_4260_ = v___y_4292_;
v___y_4261_ = v___y_4293_;
v___y_4262_ = v___y_4295_;
v___y_4263_ = v___y_4297_;
v___y_4264_ = v___y_4298_;
v___y_4265_ = v___y_4300_;
v___y_4266_ = v___y_4301_;
v___y_4267_ = v___y_4303_;
v___y_4268_ = v___y_4304_;
v___y_4269_ = v___y_4305_;
v___y_4270_ = v___y_4306_;
v___y_4271_ = v___y_4307_;
v___y_4272_ = v___y_4308_;
v___y_4273_ = v___x_4318_;
v___y_4274_ = v___y_4309_;
v___y_4275_ = v___y_4310_;
v___y_4276_ = v_a_4315_;
v___y_4277_ = v___y_4313_;
v_a_4278_ = v___x_4325_;
goto v___jp_4259_;
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
v_a_4328_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4319_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4319_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
lean_ctor_set_tag(v___x_4330_, 0);
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
v___y_4260_ = v___y_4292_;
v___y_4261_ = v___y_4293_;
v___y_4262_ = v___y_4295_;
v___y_4263_ = v___y_4297_;
v___y_4264_ = v___y_4298_;
v___y_4265_ = v___y_4300_;
v___y_4266_ = v___y_4301_;
v___y_4267_ = v___y_4303_;
v___y_4268_ = v___y_4304_;
v___y_4269_ = v___y_4305_;
v___y_4270_ = v___y_4306_;
v___y_4271_ = v___y_4307_;
v___y_4272_ = v___y_4308_;
v___y_4273_ = v___x_4318_;
v___y_4274_ = v___y_4309_;
v___y_4275_ = v___y_4310_;
v___y_4276_ = v_a_4315_;
v___y_4277_ = v___y_4313_;
v_a_4278_ = v___x_4333_;
goto v___jp_4259_;
}
}
}
}
else
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = lean_io_get_num_heartbeats();
v___x_4337_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4291_, v___y_4296_, v___y_4312_, v___y_4311_, v___y_4294_, v___y_4299_, v___y_4302_, v___y_4309_, v___y_4297_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4337_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4337_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
lean_ctor_set_tag(v___x_4340_, 1);
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
v___y_4232_ = v___y_4292_;
v___y_4233_ = v___y_4293_;
v___y_4234_ = v___y_4295_;
v___y_4235_ = v___x_4336_;
v___y_4236_ = v___y_4297_;
v___y_4237_ = v___y_4298_;
v___y_4238_ = v___y_4300_;
v___y_4239_ = v___y_4301_;
v___y_4240_ = v___y_4303_;
v___y_4241_ = v___y_4304_;
v___y_4242_ = v___y_4305_;
v___y_4243_ = v___y_4306_;
v___y_4244_ = v___y_4307_;
v___y_4245_ = v___y_4308_;
v___y_4246_ = v___y_4309_;
v___y_4247_ = v___y_4310_;
v___y_4248_ = v_a_4315_;
v___y_4249_ = v___y_4313_;
v_a_4250_ = v___x_4343_;
goto v___jp_4231_;
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
v_a_4346_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4337_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4337_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
lean_ctor_set_tag(v___x_4348_, 0);
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
v___y_4232_ = v___y_4292_;
v___y_4233_ = v___y_4293_;
v___y_4234_ = v___y_4295_;
v___y_4235_ = v___x_4336_;
v___y_4236_ = v___y_4297_;
v___y_4237_ = v___y_4298_;
v___y_4238_ = v___y_4300_;
v___y_4239_ = v___y_4301_;
v___y_4240_ = v___y_4303_;
v___y_4241_ = v___y_4304_;
v___y_4242_ = v___y_4305_;
v___y_4243_ = v___y_4306_;
v___y_4244_ = v___y_4307_;
v___y_4245_ = v___y_4308_;
v___y_4246_ = v___y_4309_;
v___y_4247_ = v___y_4310_;
v___y_4248_ = v_a_4315_;
v___y_4249_ = v___y_4313_;
v_a_4250_ = v___x_4351_;
goto v___jp_4231_;
}
}
}
}
}
v___jp_4354_:
{
if (lean_obj_tag(v___y_4369_) == 0)
{
lean_object* v_toCold_4370_; lean_object* v_options_4371_; uint8_t v_hasTrace_4372_; 
v_toCold_4370_ = lean_ctor_get(v___y_4366_, 0);
v_options_4371_ = lean_ctor_get(v_toCold_4370_, 2);
v_hasTrace_4372_ = lean_ctor_get_uint8(v_options_4371_, sizeof(void*)*1);
if (v_hasTrace_4372_ == 0)
{
lean_object* v_config_4373_; lean_object* v_a_4374_; lean_object* v_solver_4375_; lean_object* v_lratPath_4376_; lean_object* v_timeout_4377_; uint8_t v_trimProofs_4378_; uint8_t v_binaryProofs_4379_; uint8_t v_solverMode_4380_; lean_object* v___x_4381_; 
v_config_4373_ = lean_ctor_get(v_ctx_4063_, 5);
v_a_4374_ = lean_ctor_get(v___y_4369_, 0);
lean_inc(v_a_4374_);
lean_dec_ref_known(v___y_4369_, 1);
v_solver_4375_ = lean_ctor_get(v_ctx_4063_, 3);
v_lratPath_4376_ = lean_ctor_get(v_ctx_4063_, 4);
v_timeout_4377_ = lean_ctor_get(v_config_4373_, 0);
v_trimProofs_4378_ = lean_ctor_get_uint8(v_config_4373_, sizeof(void*)*3);
v_binaryProofs_4379_ = lean_ctor_get_uint8(v_config_4373_, sizeof(void*)*3 + 1);
v_solverMode_4380_ = lean_ctor_get_uint8(v_config_4373_, sizeof(void*)*3 + 10);
lean_inc(v_timeout_4377_);
lean_inc_ref(v_lratPath_4376_);
lean_inc_ref(v_solver_4375_);
v___x_4381_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4374_, v_solver_4375_, v_lratPath_4376_, v_trimProofs_4378_, v_timeout_4377_, v_binaryProofs_4379_, v_solverMode_4380_, v___y_4366_, v___y_4358_);
v___y_4153_ = v___y_4355_;
v___y_4154_ = v___y_4356_;
v___y_4155_ = v___y_4357_;
v___y_4156_ = v___y_4358_;
v___y_4157_ = v___y_4360_;
v___y_4158_ = v___y_4361_;
v___y_4159_ = v___y_4362_;
v___y_4160_ = v___y_4363_;
v___y_4161_ = v___y_4364_;
v___y_4162_ = v___y_4365_;
v___y_4163_ = v___y_4366_;
v___y_4164_ = v___y_4367_;
v___y_4165_ = v___y_4368_;
v___y_4166_ = v___x_4381_;
goto v___jp_4152_;
}
else
{
lean_object* v_config_4382_; lean_object* v_a_4383_; lean_object* v_solver_4384_; lean_object* v_lratPath_4385_; lean_object* v_timeout_4386_; uint8_t v_trimProofs_4387_; uint8_t v_binaryProofs_4388_; uint8_t v_solverMode_4389_; lean_object* v_inheritedTraceOptions_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v_config_4382_ = lean_ctor_get(v_ctx_4063_, 5);
v_a_4383_ = lean_ctor_get(v___y_4369_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___y_4369_, 1);
v_solver_4384_ = lean_ctor_get(v_ctx_4063_, 3);
v_lratPath_4385_ = lean_ctor_get(v_ctx_4063_, 4);
v_timeout_4386_ = lean_ctor_get(v_config_4382_, 0);
v_trimProofs_4387_ = lean_ctor_get_uint8(v_config_4382_, sizeof(void*)*3);
v_binaryProofs_4388_ = lean_ctor_get_uint8(v_config_4382_, sizeof(void*)*3 + 1);
v_solverMode_4389_ = lean_ctor_get_uint8(v_config_4382_, sizeof(void*)*3 + 10);
v_inheritedTraceOptions_4390_ = lean_ctor_get(v_toCold_4370_, 11);
v___x_4391_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4367_);
v___x_4392_ = l_Lean_Name_append(v___x_4391_, v___y_4367_);
v___x_4393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4390_, v_options_4371_, v___x_4392_);
lean_dec(v___x_4392_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4394_ = l_Lean_trace_profiler;
v___x_4395_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4371_, v___x_4394_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; 
lean_inc(v_timeout_4386_);
lean_inc_ref(v_lratPath_4385_);
lean_inc_ref(v_solver_4384_);
v___x_4396_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4383_, v_solver_4384_, v_lratPath_4385_, v_trimProofs_4387_, v_timeout_4386_, v_binaryProofs_4388_, v_solverMode_4389_, v___y_4366_, v___y_4358_);
v___y_4153_ = v___y_4355_;
v___y_4154_ = v___y_4356_;
v___y_4155_ = v___y_4357_;
v___y_4156_ = v___y_4358_;
v___y_4157_ = v___y_4360_;
v___y_4158_ = v___y_4361_;
v___y_4159_ = v___y_4362_;
v___y_4160_ = v___y_4363_;
v___y_4161_ = v___y_4364_;
v___y_4162_ = v___y_4365_;
v___y_4163_ = v___y_4366_;
v___y_4164_ = v___y_4367_;
v___y_4165_ = v___y_4368_;
v___y_4166_ = v___x_4396_;
goto v___jp_4152_;
}
else
{
lean_inc_ref(v_lratPath_4385_);
lean_inc_ref(v_solver_4384_);
lean_inc(v_timeout_4386_);
v___y_4291_ = v_a_4383_;
v___y_4292_ = v___y_4355_;
v___y_4293_ = v___y_4356_;
v___y_4294_ = v_timeout_4386_;
v___y_4295_ = v___y_4357_;
v___y_4296_ = v_solver_4384_;
v___y_4297_ = v___y_4358_;
v___y_4298_ = v_options_4371_;
v___y_4299_ = v_binaryProofs_4388_;
v___y_4300_ = v___y_4359_;
v___y_4301_ = v___y_4360_;
v___y_4302_ = v_solverMode_4389_;
v___y_4303_ = v___x_4393_;
v___y_4304_ = v___y_4361_;
v___y_4305_ = v___y_4362_;
v___y_4306_ = v___y_4363_;
v___y_4307_ = v___y_4364_;
v___y_4308_ = v___y_4365_;
v___y_4309_ = v___y_4366_;
v___y_4310_ = v___y_4367_;
v___y_4311_ = v_trimProofs_4387_;
v___y_4312_ = v_lratPath_4385_;
v___y_4313_ = v___y_4368_;
goto v___jp_4290_;
}
}
else
{
lean_inc_ref(v_lratPath_4385_);
lean_inc_ref(v_solver_4384_);
lean_inc(v_timeout_4386_);
v___y_4291_ = v_a_4383_;
v___y_4292_ = v___y_4355_;
v___y_4293_ = v___y_4356_;
v___y_4294_ = v_timeout_4386_;
v___y_4295_ = v___y_4357_;
v___y_4296_ = v_solver_4384_;
v___y_4297_ = v___y_4358_;
v___y_4298_ = v_options_4371_;
v___y_4299_ = v_binaryProofs_4388_;
v___y_4300_ = v___y_4359_;
v___y_4301_ = v___y_4360_;
v___y_4302_ = v_solverMode_4389_;
v___y_4303_ = v___x_4393_;
v___y_4304_ = v___y_4361_;
v___y_4305_ = v___y_4362_;
v___y_4306_ = v___y_4363_;
v___y_4307_ = v___y_4364_;
v___y_4308_ = v___y_4365_;
v___y_4309_ = v___y_4366_;
v___y_4310_ = v___y_4367_;
v___y_4311_ = v_trimProofs_4387_;
v___y_4312_ = v_lratPath_4385_;
v___y_4313_ = v___y_4368_;
goto v___jp_4290_;
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
lean_dec_ref(v___y_4355_);
lean_dec_ref(v_satExpr_4079_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4397_ = lean_ctor_get(v___y_4369_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___y_4369_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___y_4369_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___y_4369_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
v___jp_4405_:
{
lean_object* v___x_4425_; double v___x_4426_; double v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4425_ = lean_io_get_num_heartbeats();
v___x_4426_ = lean_float_of_nat(v___y_4412_);
v___x_4427_ = lean_float_of_nat(v___x_4425_);
v___x_4428_ = lean_box_float(v___x_4426_);
v___x_4429_ = lean_box_float(v___x_4427_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4428_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4431_, 0, v_a_4424_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
lean_inc(v___y_4421_);
v___x_4432_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4421_, v___x_4229_, v___x_4230_, v___y_4408_, v___y_4422_, v___y_4409_, v___f_4221_, v___x_4431_, v___y_4413_, v___y_4418_, v___y_4415_, v___y_4416_, v___y_4410_, v___y_4414_, v___y_4423_, v___y_4417_, v___y_4419_, v___y_4407_, v___y_4420_, v___y_4411_);
v___y_4355_ = v___y_4406_;
v___y_4356_ = v___y_4407_;
v___y_4357_ = v___y_4410_;
v___y_4358_ = v___y_4411_;
v___y_4359_ = v___y_4413_;
v___y_4360_ = v___y_4414_;
v___y_4361_ = v___y_4415_;
v___y_4362_ = v___y_4416_;
v___y_4363_ = v___y_4417_;
v___y_4364_ = v___y_4418_;
v___y_4365_ = v___y_4419_;
v___y_4366_ = v___y_4420_;
v___y_4367_ = v___y_4421_;
v___y_4368_ = v___y_4423_;
v___y_4369_ = v___x_4432_;
goto v___jp_4354_;
}
v___jp_4433_:
{
lean_object* v___x_4453_; double v___x_4454_; double v___x_4455_; double v___x_4456_; double v___x_4457_; double v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4453_ = lean_io_mono_nanos_now();
v___x_4454_ = lean_float_of_nat(v___y_4436_);
v___x_4455_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4456_ = lean_float_div(v___x_4454_, v___x_4455_);
v___x_4457_ = lean_float_of_nat(v___x_4453_);
v___x_4458_ = lean_float_div(v___x_4457_, v___x_4455_);
v___x_4459_ = lean_box_float(v___x_4456_);
v___x_4460_ = lean_box_float(v___x_4458_);
v___x_4461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4459_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v___x_4462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4462_, 0, v_a_4452_);
lean_ctor_set(v___x_4462_, 1, v___x_4461_);
lean_inc(v___y_4449_);
v___x_4463_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4449_, v___x_4229_, v___x_4230_, v___y_4437_, v___y_4450_, v___y_4438_, v___f_4221_, v___x_4462_, v___y_4441_, v___y_4446_, v___y_4443_, v___y_4444_, v___y_4439_, v___y_4442_, v___y_4451_, v___y_4445_, v___y_4447_, v___y_4435_, v___y_4448_, v___y_4440_);
v___y_4355_ = v___y_4434_;
v___y_4356_ = v___y_4435_;
v___y_4357_ = v___y_4439_;
v___y_4358_ = v___y_4440_;
v___y_4359_ = v___y_4441_;
v___y_4360_ = v___y_4442_;
v___y_4361_ = v___y_4443_;
v___y_4362_ = v___y_4444_;
v___y_4363_ = v___y_4445_;
v___y_4364_ = v___y_4446_;
v___y_4365_ = v___y_4447_;
v___y_4366_ = v___y_4448_;
v___y_4367_ = v___y_4449_;
v___y_4368_ = v___y_4451_;
v___y_4369_ = v___x_4463_;
goto v___jp_4354_;
}
v___jp_4464_:
{
lean_object* v___x_4483_; lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4538_; 
v___x_4483_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4469_);
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4486_ = v___x_4483_;
v_isShared_4487_ = v_isSharedCheck_4538_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4483_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4538_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4488_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4489_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4467_, v___x_4488_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = lean_io_mono_nanos_now();
v___x_4491_ = l_IO_lazyPure___redArg(v___y_4478_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_del_object(v___x_4486_);
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
v___y_4434_ = v___y_4465_;
v___y_4435_ = v___y_4466_;
v___y_4436_ = v___x_4490_;
v___y_4437_ = v___y_4467_;
v___y_4438_ = v_a_4484_;
v___y_4439_ = v___y_4468_;
v___y_4440_ = v___y_4469_;
v___y_4441_ = v___y_4470_;
v___y_4442_ = v___y_4471_;
v___y_4443_ = v___y_4472_;
v___y_4444_ = v___y_4473_;
v___y_4445_ = v___y_4474_;
v___y_4446_ = v___y_4475_;
v___y_4447_ = v___y_4476_;
v___y_4448_ = v___y_4477_;
v___y_4449_ = v___y_4479_;
v___y_4450_ = v___y_4481_;
v___y_4451_ = v___y_4482_;
v_a_4452_ = v___x_4497_;
goto v___jp_4433_;
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
lean_inc(v___y_4480_);
v___x_4508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___y_4480_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 0, v___x_4508_);
v___x_4510_ = v___x_4486_;
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
v___y_4434_ = v___y_4465_;
v___y_4435_ = v___y_4466_;
v___y_4436_ = v___x_4490_;
v___y_4437_ = v___y_4467_;
v___y_4438_ = v_a_4484_;
v___y_4439_ = v___y_4468_;
v___y_4440_ = v___y_4469_;
v___y_4441_ = v___y_4470_;
v___y_4442_ = v___y_4471_;
v___y_4443_ = v___y_4472_;
v___y_4444_ = v___y_4473_;
v___y_4445_ = v___y_4474_;
v___y_4446_ = v___y_4475_;
v___y_4447_ = v___y_4476_;
v___y_4448_ = v___y_4477_;
v___y_4449_ = v___y_4479_;
v___y_4450_ = v___y_4481_;
v___y_4451_ = v___y_4482_;
v_a_4452_ = v___x_4510_;
goto v___jp_4433_;
}
}
}
}
}
else
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = lean_io_get_num_heartbeats();
v___x_4515_ = l_IO_lazyPure___redArg(v___y_4478_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_del_object(v___x_4486_);
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4515_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4515_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
lean_ctor_set_tag(v___x_4518_, 1);
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
v___y_4406_ = v___y_4465_;
v___y_4407_ = v___y_4466_;
v___y_4408_ = v___y_4467_;
v___y_4409_ = v_a_4484_;
v___y_4410_ = v___y_4468_;
v___y_4411_ = v___y_4469_;
v___y_4412_ = v___x_4514_;
v___y_4413_ = v___y_4470_;
v___y_4414_ = v___y_4471_;
v___y_4415_ = v___y_4472_;
v___y_4416_ = v___y_4473_;
v___y_4417_ = v___y_4474_;
v___y_4418_ = v___y_4475_;
v___y_4419_ = v___y_4476_;
v___y_4420_ = v___y_4477_;
v___y_4421_ = v___y_4479_;
v___y_4422_ = v___y_4481_;
v___y_4423_ = v___y_4482_;
v_a_4424_ = v___x_4521_;
goto v___jp_4405_;
}
}
}
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4537_; 
v_a_4524_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4526_ = v___x_4515_;
v_isShared_4527_ = v_isSharedCheck_4537_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4515_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4537_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4528_; lean_object* v___x_4530_; 
v___x_4528_ = lean_io_error_to_string(v_a_4524_);
if (v_isShared_4527_ == 0)
{
lean_ctor_set_tag(v___x_4526_, 3);
lean_ctor_set(v___x_4526_, 0, v___x_4528_);
v___x_4530_ = v___x_4526_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4528_);
v___x_4530_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4534_; 
v___x_4531_ = l_Lean_MessageData_ofFormat(v___x_4530_);
lean_inc(v___y_4480_);
v___x_4532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4532_, 0, v___y_4480_);
lean_ctor_set(v___x_4532_, 1, v___x_4531_);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 0, v___x_4532_);
v___x_4534_ = v___x_4486_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4532_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
v___y_4406_ = v___y_4465_;
v___y_4407_ = v___y_4466_;
v___y_4408_ = v___y_4467_;
v___y_4409_ = v_a_4484_;
v___y_4410_ = v___y_4468_;
v___y_4411_ = v___y_4469_;
v___y_4412_ = v___x_4514_;
v___y_4413_ = v___y_4470_;
v___y_4414_ = v___y_4471_;
v___y_4415_ = v___y_4472_;
v___y_4416_ = v___y_4473_;
v___y_4417_ = v___y_4474_;
v___y_4418_ = v___y_4475_;
v___y_4419_ = v___y_4476_;
v___y_4420_ = v___y_4477_;
v___y_4421_ = v___y_4479_;
v___y_4422_ = v___y_4481_;
v___y_4423_ = v___y_4482_;
v_a_4424_ = v___x_4534_;
goto v___jp_4405_;
}
}
}
}
}
}
}
v___jp_4539_:
{
lean_object* v_options_4557_; lean_object* v_inheritedTraceOptions_4558_; uint8_t v_hasTrace_4559_; lean_object* v___x_4560_; 
v_options_4557_ = lean_ctor_get(v_toCold_4554_, 2);
v_inheritedTraceOptions_4558_ = lean_ctor_get(v_toCold_4554_, 11);
v_hasTrace_4559_ = lean_ctor_get_uint8(v_options_4557_, sizeof(void*)*1);
v___x_4560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4559_ == 0)
{
lean_object* v___x_4561_; 
lean_dec_ref(v___y_4542_);
lean_inc(v___y_4556_);
lean_inc_ref(v___y_4553_);
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4551_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
lean_inc(v___y_4548_);
lean_inc_ref(v___y_4547_);
lean_inc(v___y_4546_);
lean_inc(v___y_4545_);
lean_inc_ref(v___y_4544_);
v___x_4561_ = lean_apply_12(v___y_4541_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4556_, lean_box(0));
v___y_4355_ = v___y_4540_;
v___y_4356_ = v___y_4552_;
v___y_4357_ = v___y_4547_;
v___y_4358_ = v___y_4556_;
v___y_4359_ = v___y_4543_;
v___y_4360_ = v___y_4548_;
v___y_4361_ = v___y_4545_;
v___y_4362_ = v___y_4546_;
v___y_4363_ = v___y_4550_;
v___y_4364_ = v___y_4544_;
v___y_4365_ = v___y_4551_;
v___y_4366_ = v___y_4553_;
v___y_4367_ = v___x_4560_;
v___y_4368_ = v___y_4549_;
v___y_4369_ = v___x_4561_;
goto v___jp_4354_;
}
else
{
lean_object* v___x_4562_; uint8_t v___x_4563_; 
v___x_4562_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4563_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4558_, v_options_4557_, v___x_4562_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; uint8_t v___x_4565_; 
v___x_4564_ = l_Lean_trace_profiler;
v___x_4565_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4557_, v___x_4564_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
lean_dec_ref(v___y_4542_);
lean_inc(v___y_4556_);
lean_inc_ref(v___y_4553_);
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4551_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
lean_inc(v___y_4548_);
lean_inc_ref(v___y_4547_);
lean_inc(v___y_4546_);
lean_inc(v___y_4545_);
lean_inc_ref(v___y_4544_);
v___x_4566_ = lean_apply_12(v___y_4541_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4556_, lean_box(0));
v___y_4355_ = v___y_4540_;
v___y_4356_ = v___y_4552_;
v___y_4357_ = v___y_4547_;
v___y_4358_ = v___y_4556_;
v___y_4359_ = v___y_4543_;
v___y_4360_ = v___y_4548_;
v___y_4361_ = v___y_4545_;
v___y_4362_ = v___y_4546_;
v___y_4363_ = v___y_4550_;
v___y_4364_ = v___y_4544_;
v___y_4365_ = v___y_4551_;
v___y_4366_ = v___y_4553_;
v___y_4367_ = v___x_4560_;
v___y_4368_ = v___y_4549_;
v___y_4369_ = v___x_4566_;
goto v___jp_4354_;
}
else
{
lean_dec_ref(v___y_4541_);
v___y_4465_ = v___y_4540_;
v___y_4466_ = v___y_4552_;
v___y_4467_ = v_options_4557_;
v___y_4468_ = v___y_4547_;
v___y_4469_ = v___y_4556_;
v___y_4470_ = v___y_4543_;
v___y_4471_ = v___y_4548_;
v___y_4472_ = v___y_4545_;
v___y_4473_ = v___y_4546_;
v___y_4474_ = v___y_4550_;
v___y_4475_ = v___y_4544_;
v___y_4476_ = v___y_4551_;
v___y_4477_ = v___y_4553_;
v___y_4478_ = v___y_4542_;
v___y_4479_ = v___x_4560_;
v___y_4480_ = v_ref_4555_;
v___y_4481_ = v___x_4563_;
v___y_4482_ = v___y_4549_;
goto v___jp_4464_;
}
}
else
{
lean_dec_ref(v___y_4541_);
v___y_4465_ = v___y_4540_;
v___y_4466_ = v___y_4552_;
v___y_4467_ = v_options_4557_;
v___y_4468_ = v___y_4547_;
v___y_4469_ = v___y_4556_;
v___y_4470_ = v___y_4543_;
v___y_4471_ = v___y_4548_;
v___y_4472_ = v___y_4545_;
v___y_4473_ = v___y_4546_;
v___y_4474_ = v___y_4550_;
v___y_4475_ = v___y_4544_;
v___y_4476_ = v___y_4551_;
v___y_4477_ = v___y_4553_;
v___y_4478_ = v___y_4542_;
v___y_4479_ = v___x_4560_;
v___y_4480_ = v_ref_4555_;
v___y_4481_ = v___x_4563_;
v___y_4482_ = v___y_4549_;
goto v___jp_4464_;
}
}
}
v___jp_4567_:
{
lean_object* v_config_4584_; uint8_t v_graphviz_4585_; 
v_config_4584_ = lean_ctor_get(v_ctx_4063_, 5);
v_graphviz_4585_ = lean_ctor_get_uint8(v_config_4584_, sizeof(void*)*3 + 8);
if (v_graphviz_4585_ == 0)
{
lean_object* v_toCold_4586_; lean_object* v_ref_4587_; 
lean_inc_ref(v_satExpr_4079_);
lean_dec_ref(v___y_4570_);
v_toCold_4586_ = lean_ctor_get(v___y_4582_, 0);
v_ref_4587_ = lean_ctor_get(v___y_4582_, 2);
v___y_4540_ = v___y_4568_;
v___y_4541_ = v___y_4569_;
v___y_4542_ = v___y_4571_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___y_4573_;
v___y_4545_ = v___y_4574_;
v___y_4546_ = v___y_4575_;
v___y_4547_ = v___y_4576_;
v___y_4548_ = v___y_4577_;
v___y_4549_ = v___y_4578_;
v___y_4550_ = v___y_4579_;
v___y_4551_ = v___y_4580_;
v___y_4552_ = v___y_4581_;
v___y_4553_ = v___y_4582_;
v_toCold_4554_ = v_toCold_4586_;
v_ref_4555_ = v_ref_4587_;
v___y_4556_ = v___y_4583_;
goto v___jp_4539_;
}
else
{
lean_object* v_toCold_4588_; lean_object* v_ref_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v_toCold_4588_ = lean_ctor_get(v___y_4582_, 0);
v_ref_4589_ = lean_ctor_get(v___y_4582_, 2);
v___x_4590_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_4591_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v___y_4570_);
v___x_4592_ = l_IO_FS_writeFile(v___x_4590_, v___x_4591_);
lean_dec_ref(v___x_4591_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_inc_ref(v_satExpr_4079_);
lean_dec_ref_known(v___x_4592_, 1);
v___y_4540_ = v___y_4568_;
v___y_4541_ = v___y_4569_;
v___y_4542_ = v___y_4571_;
v___y_4543_ = v___y_4572_;
v___y_4544_ = v___y_4573_;
v___y_4545_ = v___y_4574_;
v___y_4546_ = v___y_4575_;
v___y_4547_ = v___y_4576_;
v___y_4548_ = v___y_4577_;
v___y_4549_ = v___y_4578_;
v___y_4550_ = v___y_4579_;
v___y_4551_ = v___y_4580_;
v___y_4552_ = v___y_4581_;
v___y_4553_ = v___y_4582_;
v_toCold_4554_ = v_toCold_4588_;
v_ref_4555_ = v_ref_4589_;
v___y_4556_ = v___y_4583_;
goto v___jp_4539_;
}
else
{
lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4610_; 
lean_dec_ref(v___y_4571_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_isSharedCheck_4610_ = !lean_is_exclusive(v_reflectionResult_4065_);
if (v_isSharedCheck_4610_ == 0)
{
lean_object* v_unused_4611_; lean_object* v_unused_4612_; 
v_unused_4611_ = lean_ctor_get(v_reflectionResult_4065_, 1);
lean_dec(v_unused_4611_);
v_unused_4612_ = lean_ctor_get(v_reflectionResult_4065_, 0);
lean_dec(v_unused_4612_);
v___x_4594_ = v_reflectionResult_4065_;
v_isShared_4595_ = v_isSharedCheck_4610_;
goto v_resetjp_4593_;
}
else
{
lean_dec(v_reflectionResult_4065_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4610_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4609_; 
v_a_4596_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4598_ = v___x_4592_;
v_isShared_4599_ = v_isSharedCheck_4609_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4592_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4609_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4604_; 
v___x_4600_ = lean_io_error_to_string(v_a_4596_);
v___x_4601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
v___x_4602_ = l_Lean_MessageData_ofFormat(v___x_4601_);
lean_inc(v_ref_4589_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 1, v___x_4602_);
lean_ctor_set(v___x_4594_, 0, v_ref_4589_);
v___x_4604_ = v___x_4594_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_ref_4589_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
lean_object* v___x_4606_; 
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4604_);
v___x_4606_ = v___x_4598_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
}
}
v___jp_4613_:
{
lean_object* v_aig_4627_; lean_object* v_toCold_4628_; lean_object* v_options_4629_; lean_object* v_ref_4630_; lean_object* v_decls_4631_; lean_object* v_inheritedTraceOptions_4632_; uint8_t v_hasTrace_4633_; lean_object* v___f_4634_; lean_object* v___f_4635_; 
v_aig_4627_ = lean_ctor_get(v_entry_4614_, 0);
lean_inc_ref_n(v_aig_4627_, 2);
v_toCold_4628_ = lean_ctor_get(v___y_4625_, 0);
v_options_4629_ = lean_ctor_get(v_toCold_4628_, 2);
v_ref_4630_ = lean_ctor_get(v_entry_4614_, 1);
v_decls_4631_ = lean_ctor_get(v_aig_4627_, 0);
v_inheritedTraceOptions_4632_ = lean_ctor_get(v_toCold_4628_, 11);
v_hasTrace_4633_ = lean_ctor_get_uint8(v_options_4629_, sizeof(void*)*1);
lean_inc_ref(v_ref_4630_);
lean_inc_ref(v_entry_4614_);
v___f_4634_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed), 5, 4);
lean_closure_set(v___f_4634_, 0, v_aig_4627_);
lean_closure_set(v___f_4634_, 1, v___x_4223_);
lean_closure_set(v___f_4634_, 2, v_entry_4614_);
lean_closure_set(v___f_4634_, 3, v_ref_4630_);
lean_inc_ref(v___f_4634_);
v___f_4635_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4635_, 0, v___f_4634_);
if (v_hasTrace_4633_ == 0)
{
v___y_4568_ = v_aig_4627_;
v___y_4569_ = v___f_4635_;
v___y_4570_ = v_entry_4614_;
v___y_4571_ = v___f_4634_;
v___y_4572_ = v___y_4615_;
v___y_4573_ = v___y_4616_;
v___y_4574_ = v___y_4617_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4619_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4621_;
v___y_4579_ = v___y_4622_;
v___y_4580_ = v___y_4623_;
v___y_4581_ = v___y_4624_;
v___y_4582_ = v___y_4625_;
v___y_4583_ = v___y_4626_;
goto v___jp_4567_;
}
else
{
lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4636_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4637_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4632_, v_options_4629_, v___x_4636_);
if (v___x_4637_ == 0)
{
v___y_4568_ = v_aig_4627_;
v___y_4569_ = v___f_4635_;
v___y_4570_ = v_entry_4614_;
v___y_4571_ = v___f_4634_;
v___y_4572_ = v___y_4615_;
v___y_4573_ = v___y_4616_;
v___y_4574_ = v___y_4617_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4619_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4621_;
v___y_4579_ = v___y_4622_;
v___y_4580_ = v___y_4623_;
v___y_4581_ = v___y_4624_;
v___y_4582_ = v___y_4625_;
v___y_4583_ = v___y_4626_;
goto v___jp_4567_;
}
else
{
lean_object* v_aigSize_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v_aigSize_4638_ = lean_array_get_size(v_decls_4631_);
v___x_4639_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4640_ = l_Nat_reprFast(v_aigSize_4638_);
v___x_4641_ = lean_string_append(v___x_4639_, v___x_4640_);
lean_dec_ref(v___x_4640_);
v___x_4642_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4643_ = lean_string_append(v___x_4641_, v___x_4642_);
v___x_4644_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
v___x_4645_ = l_Lean_MessageData_ofFormat(v___x_4644_);
v___x_4646_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4226_, v___x_4645_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_dec_ref_known(v___x_4646_, 1);
v___y_4568_ = v_aig_4627_;
v___y_4569_ = v___f_4635_;
v___y_4570_ = v_entry_4614_;
v___y_4571_ = v___f_4634_;
v___y_4572_ = v___y_4615_;
v___y_4573_ = v___y_4616_;
v___y_4574_ = v___y_4617_;
v___y_4575_ = v___y_4618_;
v___y_4576_ = v___y_4619_;
v___y_4577_ = v___y_4620_;
v___y_4578_ = v___y_4621_;
v___y_4579_ = v___y_4622_;
v___y_4580_ = v___y_4623_;
v___y_4581_ = v___y_4624_;
v___y_4582_ = v___y_4625_;
v___y_4583_ = v___y_4626_;
goto v___jp_4567_;
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec_ref(v___f_4635_);
lean_dec_ref(v___f_4634_);
lean_dec_ref(v_aig_4627_);
lean_dec_ref(v_entry_4614_);
lean_dec_ref(v_reflectionResult_4065_);
lean_dec(v_goal_4064_);
lean_dec_ref(v_ctx_4063_);
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4649_ = v___x_4646_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4646_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_4925_, lean_object* v_goal_4926_, lean_object* v_reflectionResult_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_4925_, v_goal_4926_, v_reflectionResult_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_a_4936_);
lean_dec(v_a_4935_);
lean_dec_ref(v_a_4934_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
lean_dec(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_4942_, lean_object* v_msg_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4942_, v_msg_4943_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_4958_, lean_object* v_msg_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_){
_start:
{
lean_object* v_res_4973_; 
v_res_4973_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_4958_, v_msg_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
lean_dec(v___y_4969_);
lean_dec_ref(v___y_4968_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec(v___y_4960_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_mvarId_4974_, lean_object* v_val_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v___x_4989_; 
v___x_4989_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_4974_, v_val_4975_, v___y_4985_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_mvarId_4990_, lean_object* v_val_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_mvarId_4990_, v_val_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
lean_dec(v___y_4995_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec(v___y_4992_);
return v_res_5005_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(lean_object* v_00_u03b1_5006_, lean_object* v_x_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v___x_5021_; 
v___x_5021_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_5007_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___boxed(lean_object* v_00_u03b1_5022_, lean_object* v_x_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(v_00_u03b1_5022_, v_x_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v___y_5031_);
lean_dec_ref(v___y_5030_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
lean_dec(v___y_5027_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_00_u03b2_5038_, lean_object* v_x_5039_, lean_object* v_x_5040_, lean_object* v_x_5041_){
_start:
{
lean_object* v___x_5042_; 
v___x_5042_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_x_5039_, v_x_5040_, v_x_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(lean_object* v_oldTraces_5043_, lean_object* v_data_5044_, lean_object* v_ref_5045_, lean_object* v_msg_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v___x_5060_; 
v___x_5060_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_5043_, v_data_5044_, v_ref_5045_, v_msg_5046_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_5061_ = _args[0];
lean_object* v_data_5062_ = _args[1];
lean_object* v_ref_5063_ = _args[2];
lean_object* v_msg_5064_ = _args[3];
lean_object* v___y_5065_ = _args[4];
lean_object* v___y_5066_ = _args[5];
lean_object* v___y_5067_ = _args[6];
lean_object* v___y_5068_ = _args[7];
lean_object* v___y_5069_ = _args[8];
lean_object* v___y_5070_ = _args[9];
lean_object* v___y_5071_ = _args[10];
lean_object* v___y_5072_ = _args[11];
lean_object* v___y_5073_ = _args[12];
lean_object* v___y_5074_ = _args[13];
lean_object* v___y_5075_ = _args[14];
lean_object* v___y_5076_ = _args[15];
lean_object* v___y_5077_ = _args[16];
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(v_oldTraces_5061_, v_data_5062_, v_ref_5063_, v_msg_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___y_5072_);
lean_dec_ref(v___y_5071_);
lean_dec(v___y_5070_);
lean_dec_ref(v___y_5069_);
lean_dec(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(lean_object* v_acc_5079_, lean_object* v_decls_5080_, lean_object* v_hinv_5081_, lean_object* v_idx_5082_, lean_object* v_hidx_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v___x_5085_; 
v___x_5085_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_5079_, v_decls_5080_, v_idx_5082_, v_a_5084_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___boxed(lean_object* v_acc_5086_, lean_object* v_decls_5087_, lean_object* v_hinv_5088_, lean_object* v_idx_5089_, lean_object* v_hidx_5090_, lean_object* v_a_5091_){
_start:
{
lean_object* v_res_5092_; 
v_res_5092_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(v_acc_5086_, v_decls_5087_, v_hinv_5088_, v_idx_5089_, v_hidx_5090_, v_a_5091_);
lean_dec_ref(v_decls_5087_);
return v_res_5092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_5093_, lean_object* v_x_5094_, size_t v_x_5095_, size_t v_x_5096_, lean_object* v_x_5097_, lean_object* v_x_5098_){
_start:
{
lean_object* v___x_5099_; 
v___x_5099_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_5094_, v_x_5095_, v_x_5096_, v_x_5097_, v_x_5098_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_5100_, lean_object* v_x_5101_, lean_object* v_x_5102_, lean_object* v_x_5103_, lean_object* v_x_5104_, lean_object* v_x_5105_){
_start:
{
size_t v_x_658941__boxed_5106_; size_t v_x_658942__boxed_5107_; lean_object* v_res_5108_; 
v_x_658941__boxed_5106_ = lean_unbox_usize(v_x_5102_);
lean_dec(v_x_5102_);
v_x_658942__boxed_5107_ = lean_unbox_usize(v_x_5103_);
lean_dec(v_x_5103_);
v_res_5108_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(v_00_u03b2_5100_, v_x_5101_, v_x_658941__boxed_5106_, v_x_658942__boxed_5107_, v_x_5104_, v_x_5105_);
return v_res_5108_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(lean_object* v___x_5109_, lean_object* v_00_u03b2_5110_, lean_object* v_m_5111_, lean_object* v_a_5112_){
_start:
{
uint8_t v___x_5113_; 
v___x_5113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_5109_, v_m_5111_, v_a_5112_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___boxed(lean_object* v___x_5114_, lean_object* v_00_u03b2_5115_, lean_object* v_m_5116_, lean_object* v_a_5117_){
_start:
{
uint8_t v_res_5118_; lean_object* v_r_5119_; 
v_res_5118_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(v___x_5114_, v_00_u03b2_5115_, v_m_5116_, v_a_5117_);
lean_dec(v_a_5117_);
lean_dec_ref(v_m_5116_);
lean_dec(v___x_5114_);
v_r_5119_ = lean_box(v_res_5118_);
return v_r_5119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(lean_object* v___x_5120_, lean_object* v_00_u03b2_5121_, lean_object* v_m_5122_, lean_object* v_a_5123_, lean_object* v_b_5124_){
_start:
{
lean_object* v___x_5125_; 
v___x_5125_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_5120_, v_m_5122_, v_a_5123_, v_b_5124_);
return v___x_5125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___boxed(lean_object* v___x_5126_, lean_object* v_00_u03b2_5127_, lean_object* v_m_5128_, lean_object* v_a_5129_, lean_object* v_b_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(v___x_5126_, v_00_u03b2_5127_, v_m_5128_, v_a_5129_, v_b_5130_);
lean_dec(v___x_5126_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19(lean_object* v_00_u03b2_5132_, lean_object* v_n_5133_, lean_object* v_k_5134_, lean_object* v_v_5135_){
_start:
{
lean_object* v___x_5136_; 
v___x_5136_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v_n_5133_, v_k_5134_, v_v_5135_);
return v___x_5136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(lean_object* v_00_u03b2_5137_, size_t v_depth_5138_, lean_object* v_keys_5139_, lean_object* v_vals_5140_, lean_object* v_heq_5141_, lean_object* v_i_5142_, lean_object* v_entries_5143_){
_start:
{
lean_object* v___x_5144_; 
v___x_5144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_5138_, v_keys_5139_, v_vals_5140_, v_i_5142_, v_entries_5143_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___boxed(lean_object* v_00_u03b2_5145_, lean_object* v_depth_5146_, lean_object* v_keys_5147_, lean_object* v_vals_5148_, lean_object* v_heq_5149_, lean_object* v_i_5150_, lean_object* v_entries_5151_){
_start:
{
size_t v_depth_boxed_5152_; lean_object* v_res_5153_; 
v_depth_boxed_5152_ = lean_unbox_usize(v_depth_5146_);
lean_dec(v_depth_5146_);
v_res_5153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(v_00_u03b2_5145_, v_depth_boxed_5152_, v_keys_5147_, v_vals_5148_, v_heq_5149_, v_i_5150_, v_entries_5151_);
lean_dec_ref(v_vals_5148_);
lean_dec_ref(v_keys_5147_);
return v_res_5153_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(lean_object* v___x_5154_, lean_object* v_00_u03b2_5155_, lean_object* v_a_5156_, lean_object* v_x_5157_){
_start:
{
uint8_t v___x_5158_; 
v___x_5158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_5156_, v_x_5157_);
return v___x_5158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___boxed(lean_object* v___x_5159_, lean_object* v_00_u03b2_5160_, lean_object* v_a_5161_, lean_object* v_x_5162_){
_start:
{
uint8_t v_res_5163_; lean_object* v_r_5164_; 
v_res_5163_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(v___x_5159_, v_00_u03b2_5160_, v_a_5161_, v_x_5162_);
lean_dec(v_x_5162_);
lean_dec(v_a_5161_);
lean_dec(v___x_5159_);
v_r_5164_ = lean_box(v_res_5163_);
return v_r_5164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(lean_object* v___x_5165_, lean_object* v_00_u03b2_5166_, lean_object* v_data_5167_){
_start:
{
lean_object* v___x_5168_; 
v___x_5168_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_5165_, v_data_5167_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___boxed(lean_object* v___x_5169_, lean_object* v_00_u03b2_5170_, lean_object* v_data_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(v___x_5169_, v_00_u03b2_5170_, v_data_5171_);
lean_dec(v___x_5169_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24(lean_object* v_00_u03b2_5173_, lean_object* v_x_5174_, lean_object* v_x_5175_, lean_object* v_x_5176_, lean_object* v_x_5177_){
_start:
{
lean_object* v___x_5178_; 
v___x_5178_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_x_5174_, v_x_5175_, v_x_5176_, v_x_5177_);
return v___x_5178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(lean_object* v___x_5179_, lean_object* v_00_u03b2_5180_, lean_object* v_i_5181_, lean_object* v_source_5182_, lean_object* v_target_5183_){
_start:
{
lean_object* v___x_5184_; 
v___x_5184_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v_i_5181_, v_source_5182_, v_target_5183_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___boxed(lean_object* v___x_5185_, lean_object* v_00_u03b2_5186_, lean_object* v_i_5187_, lean_object* v_source_5188_, lean_object* v_target_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(v___x_5185_, v_00_u03b2_5186_, v_i_5187_, v_source_5188_, v_target_5189_);
lean_dec(v___x_5185_);
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31(lean_object* v_00_u03b2_5191_, lean_object* v_x_5192_, lean_object* v_x_5193_){
_start:
{
lean_object* v___x_5194_; 
v___x_5194_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_x_5192_, v_x_5193_);
return v___x_5194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(lean_object* v___y_5195_){
_start:
{
lean_object* v___x_5197_; lean_object* v_traceState_5198_; lean_object* v_traces_5199_; lean_object* v___x_5200_; lean_object* v_traceState_5201_; lean_object* v_env_5202_; lean_object* v_nextMacroScope_5203_; lean_object* v_ngen_5204_; lean_object* v_auxDeclNGen_5205_; lean_object* v_cache_5206_; lean_object* v_recordedDeps_5207_; lean_object* v_messages_5208_; lean_object* v_infoState_5209_; lean_object* v_snapshotTasks_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5231_; 
v___x_5197_ = lean_st_ref_get(v___y_5195_);
v_traceState_5198_ = lean_ctor_get(v___x_5197_, 4);
lean_inc_ref(v_traceState_5198_);
lean_dec(v___x_5197_);
v_traces_5199_ = lean_ctor_get(v_traceState_5198_, 0);
lean_inc_ref(v_traces_5199_);
lean_dec_ref(v_traceState_5198_);
v___x_5200_ = lean_st_ref_take(v___y_5195_);
v_traceState_5201_ = lean_ctor_get(v___x_5200_, 4);
v_env_5202_ = lean_ctor_get(v___x_5200_, 0);
v_nextMacroScope_5203_ = lean_ctor_get(v___x_5200_, 1);
v_ngen_5204_ = lean_ctor_get(v___x_5200_, 2);
v_auxDeclNGen_5205_ = lean_ctor_get(v___x_5200_, 3);
v_cache_5206_ = lean_ctor_get(v___x_5200_, 5);
v_recordedDeps_5207_ = lean_ctor_get(v___x_5200_, 6);
v_messages_5208_ = lean_ctor_get(v___x_5200_, 7);
v_infoState_5209_ = lean_ctor_get(v___x_5200_, 8);
v_snapshotTasks_5210_ = lean_ctor_get(v___x_5200_, 9);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5212_ = v___x_5200_;
v_isShared_5213_ = v_isSharedCheck_5231_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_snapshotTasks_5210_);
lean_inc(v_infoState_5209_);
lean_inc(v_messages_5208_);
lean_inc(v_recordedDeps_5207_);
lean_inc(v_cache_5206_);
lean_inc(v_traceState_5201_);
lean_inc(v_auxDeclNGen_5205_);
lean_inc(v_ngen_5204_);
lean_inc(v_nextMacroScope_5203_);
lean_inc(v_env_5202_);
lean_dec(v___x_5200_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5231_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
uint64_t v_tid_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5229_; 
v_tid_5214_ = lean_ctor_get_uint64(v_traceState_5201_, sizeof(void*)*1);
v_isSharedCheck_5229_ = !lean_is_exclusive(v_traceState_5201_);
if (v_isSharedCheck_5229_ == 0)
{
lean_object* v_unused_5230_; 
v_unused_5230_ = lean_ctor_get(v_traceState_5201_, 0);
lean_dec(v_unused_5230_);
v___x_5216_ = v_traceState_5201_;
v_isShared_5217_ = v_isSharedCheck_5229_;
goto v_resetjp_5215_;
}
else
{
lean_dec(v_traceState_5201_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5229_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5222_; 
v___x_5218_ = lean_unsigned_to_nat(32u);
v___x_5219_ = lean_mk_empty_array_with_capacity(v___x_5218_);
lean_dec_ref(v___x_5219_);
v___x_5220_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_5217_ == 0)
{
lean_ctor_set(v___x_5216_, 0, v___x_5220_);
v___x_5222_ = v___x_5216_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v___x_5220_);
lean_ctor_set_uint64(v_reuseFailAlloc_5228_, sizeof(void*)*1, v_tid_5214_);
v___x_5222_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5224_; 
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 4, v___x_5222_);
v___x_5224_ = v___x_5212_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_env_5202_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v_nextMacroScope_5203_);
lean_ctor_set(v_reuseFailAlloc_5227_, 2, v_ngen_5204_);
lean_ctor_set(v_reuseFailAlloc_5227_, 3, v_auxDeclNGen_5205_);
lean_ctor_set(v_reuseFailAlloc_5227_, 4, v___x_5222_);
lean_ctor_set(v_reuseFailAlloc_5227_, 5, v_cache_5206_);
lean_ctor_set(v_reuseFailAlloc_5227_, 6, v_recordedDeps_5207_);
lean_ctor_set(v_reuseFailAlloc_5227_, 7, v_messages_5208_);
lean_ctor_set(v_reuseFailAlloc_5227_, 8, v_infoState_5209_);
lean_ctor_set(v_reuseFailAlloc_5227_, 9, v_snapshotTasks_5210_);
v___x_5224_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5225_ = lean_st_ref_put(v___y_5195_, v___x_5224_);
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v_traces_5199_);
return v___x_5226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg___boxed(lean_object* v___y_5232_, lean_object* v___y_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5232_);
lean_dec(v___y_5232_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5245_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___boxed(lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
return v_res_5260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_){
_start:
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5274_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5274_);
return v___x_5275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec_ref(v_x_5276_);
return v_res_5289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(lean_object* v_e_5290_){
_start:
{
if (lean_obj_tag(v_e_5290_) == 0)
{
uint8_t v___x_5291_; 
v___x_5291_ = 2;
return v___x_5291_;
}
else
{
uint8_t v___x_5292_; 
v___x_5292_ = 0;
return v___x_5292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4___boxed(lean_object* v_e_5293_){
_start:
{
uint8_t v_res_5294_; lean_object* v_r_5295_; 
v_res_5294_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_e_5293_);
lean_dec_ref(v_e_5293_);
v_r_5295_ = lean_box(v_res_5294_);
return v_r_5295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(lean_object* v_oldTraces_5296_, lean_object* v_data_5297_, lean_object* v_ref_5298_, lean_object* v_msg_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_){
_start:
{
lean_object* v_toCold_5305_; lean_object* v_currRecDepth_5306_; lean_object* v_ref_5307_; uint16_t v_optionFlags_5308_; uint8_t v_suppressElabErrors_5309_; uint8_t v_checkDeprecated_5310_; uint8_t v_isRecordingDeps_5311_; lean_object* v_ref_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v_traceState_5315_; lean_object* v_traces_5316_; lean_object* v___x_5317_; size_t v_sz_5318_; size_t v___x_5319_; lean_object* v___x_5320_; lean_object* v_msg_5321_; lean_object* v___x_5322_; lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5361_; 
v_toCold_5305_ = lean_ctor_get(v___y_5302_, 0);
v_currRecDepth_5306_ = lean_ctor_get(v___y_5302_, 1);
v_ref_5307_ = lean_ctor_get(v___y_5302_, 2);
v_optionFlags_5308_ = lean_ctor_get_uint16(v___y_5302_, sizeof(void*)*3);
v_suppressElabErrors_5309_ = lean_ctor_get_uint8(v___y_5302_, sizeof(void*)*3 + 2);
v_checkDeprecated_5310_ = lean_ctor_get_uint8(v___y_5302_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5311_ = lean_ctor_get_uint8(v___y_5302_, sizeof(void*)*3 + 4);
v_ref_5312_ = l_Lean_replaceRef(v_ref_5298_, v_ref_5307_);
lean_inc(v_currRecDepth_5306_);
lean_inc_ref(v_toCold_5305_);
v___x_5313_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5313_, 0, v_toCold_5305_);
lean_ctor_set(v___x_5313_, 1, v_currRecDepth_5306_);
lean_ctor_set(v___x_5313_, 2, v_ref_5312_);
lean_ctor_set_uint16(v___x_5313_, sizeof(void*)*3, v_optionFlags_5308_);
lean_ctor_set_uint8(v___x_5313_, sizeof(void*)*3 + 2, v_suppressElabErrors_5309_);
lean_ctor_set_uint8(v___x_5313_, sizeof(void*)*3 + 3, v_checkDeprecated_5310_);
lean_ctor_set_uint8(v___x_5313_, sizeof(void*)*3 + 4, v_isRecordingDeps_5311_);
v___x_5314_ = lean_st_ref_get(v___y_5303_);
v_traceState_5315_ = lean_ctor_get(v___x_5314_, 4);
lean_inc_ref(v_traceState_5315_);
lean_dec(v___x_5314_);
v_traces_5316_ = lean_ctor_get(v_traceState_5315_, 0);
lean_inc_ref(v_traces_5316_);
lean_dec_ref(v_traceState_5315_);
v___x_5317_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5316_);
lean_dec_ref(v_traces_5316_);
v_sz_5318_ = lean_array_size(v___x_5317_);
v___x_5319_ = ((size_t)0ULL);
v___x_5320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_5318_, v___x_5319_, v___x_5317_);
v_msg_5321_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5321_, 0, v_data_5297_);
lean_ctor_set(v_msg_5321_, 1, v_msg_5299_);
lean_ctor_set(v_msg_5321_, 2, v___x_5320_);
v___x_5322_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_5321_, v___y_5300_, v___y_5301_, v___x_5313_, v___y_5303_);
lean_dec_ref_known(v___x_5313_, 3);
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5322_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5325_ = v___x_5322_;
v_isShared_5326_ = v_isSharedCheck_5361_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v___x_5322_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5361_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___x_5327_; lean_object* v_traceState_5328_; lean_object* v_env_5329_; lean_object* v_nextMacroScope_5330_; lean_object* v_ngen_5331_; lean_object* v_auxDeclNGen_5332_; lean_object* v_cache_5333_; lean_object* v_recordedDeps_5334_; lean_object* v_messages_5335_; lean_object* v_infoState_5336_; lean_object* v_snapshotTasks_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5360_; 
v___x_5327_ = lean_st_ref_take(v___y_5303_);
v_traceState_5328_ = lean_ctor_get(v___x_5327_, 4);
v_env_5329_ = lean_ctor_get(v___x_5327_, 0);
v_nextMacroScope_5330_ = lean_ctor_get(v___x_5327_, 1);
v_ngen_5331_ = lean_ctor_get(v___x_5327_, 2);
v_auxDeclNGen_5332_ = lean_ctor_get(v___x_5327_, 3);
v_cache_5333_ = lean_ctor_get(v___x_5327_, 5);
v_recordedDeps_5334_ = lean_ctor_get(v___x_5327_, 6);
v_messages_5335_ = lean_ctor_get(v___x_5327_, 7);
v_infoState_5336_ = lean_ctor_get(v___x_5327_, 8);
v_snapshotTasks_5337_ = lean_ctor_get(v___x_5327_, 9);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5339_ = v___x_5327_;
v_isShared_5340_ = v_isSharedCheck_5360_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_snapshotTasks_5337_);
lean_inc(v_infoState_5336_);
lean_inc(v_messages_5335_);
lean_inc(v_recordedDeps_5334_);
lean_inc(v_cache_5333_);
lean_inc(v_traceState_5328_);
lean_inc(v_auxDeclNGen_5332_);
lean_inc(v_ngen_5331_);
lean_inc(v_nextMacroScope_5330_);
lean_inc(v_env_5329_);
lean_dec(v___x_5327_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5360_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
uint64_t v_tid_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5358_; 
v_tid_5341_ = lean_ctor_get_uint64(v_traceState_5328_, sizeof(void*)*1);
v_isSharedCheck_5358_ = !lean_is_exclusive(v_traceState_5328_);
if (v_isSharedCheck_5358_ == 0)
{
lean_object* v_unused_5359_; 
v_unused_5359_ = lean_ctor_get(v_traceState_5328_, 0);
lean_dec(v_unused_5359_);
v___x_5343_ = v_traceState_5328_;
v_isShared_5344_ = v_isSharedCheck_5358_;
goto v_resetjp_5342_;
}
else
{
lean_dec(v_traceState_5328_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5358_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5345_ = lean_box(0);
v___x_5346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5346_, 0, v_ref_5298_);
lean_ctor_set(v___x_5346_, 1, v_a_5323_);
v___x_5347_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5296_, v___x_5346_);
if (v_isShared_5344_ == 0)
{
lean_ctor_set(v___x_5343_, 0, v___x_5347_);
v___x_5349_ = v___x_5343_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5347_);
lean_ctor_set_uint64(v_reuseFailAlloc_5357_, sizeof(void*)*1, v_tid_5341_);
v___x_5349_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
lean_object* v___x_5351_; 
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 4, v___x_5349_);
v___x_5351_ = v___x_5339_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_env_5329_);
lean_ctor_set(v_reuseFailAlloc_5356_, 1, v_nextMacroScope_5330_);
lean_ctor_set(v_reuseFailAlloc_5356_, 2, v_ngen_5331_);
lean_ctor_set(v_reuseFailAlloc_5356_, 3, v_auxDeclNGen_5332_);
lean_ctor_set(v_reuseFailAlloc_5356_, 4, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5356_, 5, v_cache_5333_);
lean_ctor_set(v_reuseFailAlloc_5356_, 6, v_recordedDeps_5334_);
lean_ctor_set(v_reuseFailAlloc_5356_, 7, v_messages_5335_);
lean_ctor_set(v_reuseFailAlloc_5356_, 8, v_infoState_5336_);
lean_ctor_set(v_reuseFailAlloc_5356_, 9, v_snapshotTasks_5337_);
v___x_5351_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
lean_object* v___x_5352_; lean_object* v___x_5354_; 
v___x_5352_ = lean_st_ref_put(v___y_5303_, v___x_5351_);
if (v_isShared_5326_ == 0)
{
lean_ctor_set(v___x_5325_, 0, v___x_5345_);
v___x_5354_ = v___x_5325_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5345_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_5362_, lean_object* v_data_5363_, lean_object* v_ref_5364_, lean_object* v_msg_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5362_, v_data_5363_, v_ref_5364_, v_msg_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_);
lean_dec(v___y_5369_);
lean_dec_ref(v___y_5368_);
lean_dec(v___y_5367_);
lean_dec_ref(v___y_5366_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(lean_object* v_x_5372_){
_start:
{
if (lean_obj_tag(v_x_5372_) == 0)
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
v_a_5374_ = lean_ctor_get(v_x_5372_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v_x_5372_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v_x_5372_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v_x_5372_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set_tag(v___x_5376_, 1);
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
v_a_5382_ = lean_ctor_get(v_x_5372_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v_x_5372_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v_x_5372_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v_x_5372_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
lean_ctor_set_tag(v___x_5384_, 0);
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg___boxed(lean_object* v_x_5390_, lean_object* v___y_5391_){
_start:
{
lean_object* v_res_5392_; 
v_res_5392_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5390_);
return v_res_5392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(lean_object* v_cls_5393_, uint8_t v_collapsed_5394_, lean_object* v_tag_5395_, lean_object* v_opts_5396_, uint8_t v_clsEnabled_5397_, lean_object* v_oldTraces_5398_, lean_object* v_msg_5399_, lean_object* v_resStartStop_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v_fst_5413_; lean_object* v_snd_5414_; lean_object* v___y_5416_; lean_object* v___y_5417_; lean_object* v_data_5418_; lean_object* v_fst_5429_; lean_object* v_snd_5430_; lean_object* v___x_5431_; uint8_t v___x_5432_; lean_object* v___y_5434_; lean_object* v_a_5435_; uint8_t v___y_5450_; double v___y_5482_; 
v_fst_5413_ = lean_ctor_get(v_resStartStop_5400_, 0);
lean_inc(v_fst_5413_);
v_snd_5414_ = lean_ctor_get(v_resStartStop_5400_, 1);
lean_inc(v_snd_5414_);
lean_dec_ref(v_resStartStop_5400_);
v_fst_5429_ = lean_ctor_get(v_snd_5414_, 0);
lean_inc(v_fst_5429_);
v_snd_5430_ = lean_ctor_get(v_snd_5414_, 1);
lean_inc(v_snd_5430_);
lean_dec(v_snd_5414_);
v___x_5431_ = l_Lean_trace_profiler;
v___x_5432_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5396_, v___x_5431_);
if (v___x_5432_ == 0)
{
v___y_5450_ = v___x_5432_;
goto v___jp_5449_;
}
else
{
lean_object* v___x_5487_; uint8_t v___x_5488_; 
v___x_5487_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5488_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5396_, v___x_5487_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5489_; lean_object* v___x_5490_; double v___x_5491_; double v___x_5492_; double v___x_5493_; 
v___x_5489_ = l_Lean_trace_profiler_threshold;
v___x_5490_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5396_, v___x_5489_);
v___x_5491_ = lean_float_of_nat(v___x_5490_);
v___x_5492_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_5493_ = lean_float_div(v___x_5491_, v___x_5492_);
v___y_5482_ = v___x_5493_;
goto v___jp_5481_;
}
else
{
lean_object* v___x_5494_; lean_object* v___x_5495_; double v___x_5496_; 
v___x_5494_ = l_Lean_trace_profiler_threshold;
v___x_5495_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5396_, v___x_5494_);
v___x_5496_ = lean_float_of_nat(v___x_5495_);
v___y_5482_ = v___x_5496_;
goto v___jp_5481_;
}
}
v___jp_5415_:
{
lean_object* v___x_5419_; 
lean_inc(v___y_5416_);
v___x_5419_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5398_, v_data_5418_, v___y_5416_, v___y_5417_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v___x_5420_; 
lean_dec_ref_known(v___x_5419_, 1);
v___x_5420_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5413_);
return v___x_5420_;
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
lean_dec(v_fst_5413_);
v_a_5421_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___x_5419_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5419_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
v___jp_5433_:
{
uint8_t v_result_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; double v___x_5439_; lean_object* v_data_5440_; 
v_result_5436_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_fst_5413_);
v___x_5437_ = lean_box(v_result_5436_);
v___x_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5438_, 0, v___x_5437_);
v___x_5439_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_5395_);
lean_inc_ref(v___x_5438_);
lean_inc(v_cls_5393_);
v_data_5440_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5440_, 0, v_cls_5393_);
lean_ctor_set(v_data_5440_, 1, v___x_5438_);
lean_ctor_set(v_data_5440_, 2, v_tag_5395_);
lean_ctor_set_float(v_data_5440_, sizeof(void*)*3, v___x_5439_);
lean_ctor_set_float(v_data_5440_, sizeof(void*)*3 + 8, v___x_5439_);
lean_ctor_set_uint8(v_data_5440_, sizeof(void*)*3 + 16, v_collapsed_5394_);
if (v___x_5432_ == 0)
{
lean_dec_ref_known(v___x_5438_, 1);
lean_dec(v_snd_5430_);
lean_dec(v_fst_5429_);
lean_dec_ref(v_tag_5395_);
lean_dec(v_cls_5393_);
v___y_5416_ = v___y_5434_;
v___y_5417_ = v_a_5435_;
v_data_5418_ = v_data_5440_;
goto v___jp_5415_;
}
else
{
lean_object* v_data_5441_; double v___x_5442_; double v___x_5443_; 
lean_dec_ref_known(v_data_5440_, 3);
v_data_5441_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5441_, 0, v_cls_5393_);
lean_ctor_set(v_data_5441_, 1, v___x_5438_);
lean_ctor_set(v_data_5441_, 2, v_tag_5395_);
v___x_5442_ = lean_unbox_float(v_fst_5429_);
lean_dec(v_fst_5429_);
lean_ctor_set_float(v_data_5441_, sizeof(void*)*3, v___x_5442_);
v___x_5443_ = lean_unbox_float(v_snd_5430_);
lean_dec(v_snd_5430_);
lean_ctor_set_float(v_data_5441_, sizeof(void*)*3 + 8, v___x_5443_);
lean_ctor_set_uint8(v_data_5441_, sizeof(void*)*3 + 16, v_collapsed_5394_);
v___y_5416_ = v___y_5434_;
v___y_5417_ = v_a_5435_;
v_data_5418_ = v_data_5441_;
goto v___jp_5415_;
}
}
v___jp_5444_:
{
lean_object* v_ref_5445_; lean_object* v___x_5446_; 
v_ref_5445_ = lean_ctor_get(v___y_5410_, 2);
lean_inc(v___y_5411_);
lean_inc_ref(v___y_5410_);
lean_inc(v___y_5409_);
lean_inc_ref(v___y_5408_);
lean_inc(v___y_5407_);
lean_inc_ref(v___y_5406_);
lean_inc(v___y_5405_);
lean_inc_ref(v___y_5404_);
lean_inc(v___y_5403_);
lean_inc(v___y_5402_);
lean_inc_ref(v___y_5401_);
lean_inc(v_fst_5413_);
v___x_5446_ = lean_apply_13(v_msg_5399_, v_fst_5413_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, lean_box(0));
if (lean_obj_tag(v___x_5446_) == 0)
{
lean_object* v_a_5447_; 
v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
lean_inc(v_a_5447_);
lean_dec_ref_known(v___x_5446_, 1);
v___y_5434_ = v_ref_5445_;
v_a_5435_ = v_a_5447_;
goto v___jp_5433_;
}
else
{
lean_object* v___x_5448_; 
lean_dec_ref_known(v___x_5446_, 1);
v___x_5448_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_5434_ = v_ref_5445_;
v_a_5435_ = v___x_5448_;
goto v___jp_5433_;
}
}
v___jp_5449_:
{
if (v_clsEnabled_5397_ == 0)
{
if (v___y_5450_ == 0)
{
lean_object* v___x_5451_; lean_object* v_traceState_5452_; lean_object* v_env_5453_; lean_object* v_nextMacroScope_5454_; lean_object* v_ngen_5455_; lean_object* v_auxDeclNGen_5456_; lean_object* v_cache_5457_; lean_object* v_recordedDeps_5458_; lean_object* v_messages_5459_; lean_object* v_infoState_5460_; lean_object* v_snapshotTasks_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5480_; 
lean_dec(v_snd_5430_);
lean_dec(v_fst_5429_);
lean_dec_ref(v_msg_5399_);
lean_dec_ref(v_tag_5395_);
lean_dec(v_cls_5393_);
v___x_5451_ = lean_st_ref_take(v___y_5411_);
v_traceState_5452_ = lean_ctor_get(v___x_5451_, 4);
v_env_5453_ = lean_ctor_get(v___x_5451_, 0);
v_nextMacroScope_5454_ = lean_ctor_get(v___x_5451_, 1);
v_ngen_5455_ = lean_ctor_get(v___x_5451_, 2);
v_auxDeclNGen_5456_ = lean_ctor_get(v___x_5451_, 3);
v_cache_5457_ = lean_ctor_get(v___x_5451_, 5);
v_recordedDeps_5458_ = lean_ctor_get(v___x_5451_, 6);
v_messages_5459_ = lean_ctor_get(v___x_5451_, 7);
v_infoState_5460_ = lean_ctor_get(v___x_5451_, 8);
v_snapshotTasks_5461_ = lean_ctor_get(v___x_5451_, 9);
v_isSharedCheck_5480_ = !lean_is_exclusive(v___x_5451_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5463_ = v___x_5451_;
v_isShared_5464_ = v_isSharedCheck_5480_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_snapshotTasks_5461_);
lean_inc(v_infoState_5460_);
lean_inc(v_messages_5459_);
lean_inc(v_recordedDeps_5458_);
lean_inc(v_cache_5457_);
lean_inc(v_traceState_5452_);
lean_inc(v_auxDeclNGen_5456_);
lean_inc(v_ngen_5455_);
lean_inc(v_nextMacroScope_5454_);
lean_inc(v_env_5453_);
lean_dec(v___x_5451_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5480_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
uint64_t v_tid_5465_; lean_object* v_traces_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5479_; 
v_tid_5465_ = lean_ctor_get_uint64(v_traceState_5452_, sizeof(void*)*1);
v_traces_5466_ = lean_ctor_get(v_traceState_5452_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v_traceState_5452_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5468_ = v_traceState_5452_;
v_isShared_5469_ = v_isSharedCheck_5479_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_traces_5466_);
lean_dec(v_traceState_5452_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5479_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5470_; lean_object* v___x_5472_; 
v___x_5470_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5398_, v_traces_5466_);
lean_dec_ref(v_traces_5466_);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v___x_5470_);
v___x_5472_ = v___x_5468_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v___x_5470_);
lean_ctor_set_uint64(v_reuseFailAlloc_5478_, sizeof(void*)*1, v_tid_5465_);
v___x_5472_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
lean_object* v___x_5474_; 
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 4, v___x_5472_);
v___x_5474_ = v___x_5463_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_env_5453_);
lean_ctor_set(v_reuseFailAlloc_5477_, 1, v_nextMacroScope_5454_);
lean_ctor_set(v_reuseFailAlloc_5477_, 2, v_ngen_5455_);
lean_ctor_set(v_reuseFailAlloc_5477_, 3, v_auxDeclNGen_5456_);
lean_ctor_set(v_reuseFailAlloc_5477_, 4, v___x_5472_);
lean_ctor_set(v_reuseFailAlloc_5477_, 5, v_cache_5457_);
lean_ctor_set(v_reuseFailAlloc_5477_, 6, v_recordedDeps_5458_);
lean_ctor_set(v_reuseFailAlloc_5477_, 7, v_messages_5459_);
lean_ctor_set(v_reuseFailAlloc_5477_, 8, v_infoState_5460_);
lean_ctor_set(v_reuseFailAlloc_5477_, 9, v_snapshotTasks_5461_);
v___x_5474_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
lean_object* v___x_5475_; lean_object* v___x_5476_; 
v___x_5475_ = lean_st_ref_put(v___y_5411_, v___x_5474_);
v___x_5476_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5413_);
return v___x_5476_;
}
}
}
}
}
else
{
goto v___jp_5444_;
}
}
else
{
goto v___jp_5444_;
}
}
v___jp_5481_:
{
double v___x_5483_; double v___x_5484_; double v___x_5485_; uint8_t v___x_5486_; 
v___x_5483_ = lean_unbox_float(v_snd_5430_);
v___x_5484_ = lean_unbox_float(v_fst_5429_);
v___x_5485_ = lean_float_sub(v___x_5483_, v___x_5484_);
v___x_5486_ = lean_float_decLt(v___y_5482_, v___x_5485_);
v___y_5450_ = v___x_5486_;
goto v___jp_5449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2___boxed(lean_object** _args){
lean_object* v_cls_5497_ = _args[0];
lean_object* v_collapsed_5498_ = _args[1];
lean_object* v_tag_5499_ = _args[2];
lean_object* v_opts_5500_ = _args[3];
lean_object* v_clsEnabled_5501_ = _args[4];
lean_object* v_oldTraces_5502_ = _args[5];
lean_object* v_msg_5503_ = _args[6];
lean_object* v_resStartStop_5504_ = _args[7];
lean_object* v___y_5505_ = _args[8];
lean_object* v___y_5506_ = _args[9];
lean_object* v___y_5507_ = _args[10];
lean_object* v___y_5508_ = _args[11];
lean_object* v___y_5509_ = _args[12];
lean_object* v___y_5510_ = _args[13];
lean_object* v___y_5511_ = _args[14];
lean_object* v___y_5512_ = _args[15];
lean_object* v___y_5513_ = _args[16];
lean_object* v___y_5514_ = _args[17];
lean_object* v___y_5515_ = _args[18];
lean_object* v___y_5516_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_5517_; uint8_t v_clsEnabled_boxed_5518_; lean_object* v_res_5519_; 
v_collapsed_boxed_5517_ = lean_unbox(v_collapsed_5498_);
v_clsEnabled_boxed_5518_ = lean_unbox(v_clsEnabled_5501_);
v_res_5519_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v_cls_5497_, v_collapsed_boxed_5517_, v_tag_5499_, v_opts_5500_, v_clsEnabled_boxed_5518_, v_oldTraces_5502_, v_msg_5503_, v_resStartStop_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_);
lean_dec(v___y_5515_);
lean_dec_ref(v___y_5514_);
lean_dec(v___y_5513_);
lean_dec_ref(v___y_5512_);
lean_dec(v___y_5511_);
lean_dec_ref(v___y_5510_);
lean_dec(v___y_5509_);
lean_dec_ref(v___y_5508_);
lean_dec(v___y_5507_);
lean_dec(v___y_5506_);
lean_dec_ref(v___y_5505_);
lean_dec_ref(v_opts_5500_);
return v_res_5519_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(lean_object* v_mvarId_5520_, lean_object* v_val_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v___x_5524_; lean_object* v_mctx_5525_; lean_object* v_cache_5526_; lean_object* v_zetaDeltaFVarIds_5527_; lean_object* v_postponed_5528_; lean_object* v_diag_5529_; lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5559_; 
v___x_5524_ = lean_st_ref_take(v___y_5522_);
v_mctx_5525_ = lean_ctor_get(v___x_5524_, 0);
v_cache_5526_ = lean_ctor_get(v___x_5524_, 1);
v_zetaDeltaFVarIds_5527_ = lean_ctor_get(v___x_5524_, 2);
v_postponed_5528_ = lean_ctor_get(v___x_5524_, 3);
v_diag_5529_ = lean_ctor_get(v___x_5524_, 4);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5524_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5531_ = v___x_5524_;
v_isShared_5532_ = v_isSharedCheck_5559_;
goto v_resetjp_5530_;
}
else
{
lean_inc(v_diag_5529_);
lean_inc(v_postponed_5528_);
lean_inc(v_zetaDeltaFVarIds_5527_);
lean_inc(v_cache_5526_);
lean_inc(v_mctx_5525_);
lean_dec(v___x_5524_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5559_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v_depth_5533_; lean_object* v_levelAssignDepth_5534_; lean_object* v_lmvarCounter_5535_; lean_object* v_mvarCounter_5536_; lean_object* v_lDecls_5537_; lean_object* v_decls_5538_; lean_object* v_userNames_5539_; lean_object* v_lAssignment_5540_; lean_object* v_eAssignment_5541_; lean_object* v_dAssignment_5542_; lean_object* v_instanceTypedMVars_5543_; lean_object* v_synthNormMemo_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5558_; 
v_depth_5533_ = lean_ctor_get(v_mctx_5525_, 0);
v_levelAssignDepth_5534_ = lean_ctor_get(v_mctx_5525_, 1);
v_lmvarCounter_5535_ = lean_ctor_get(v_mctx_5525_, 2);
v_mvarCounter_5536_ = lean_ctor_get(v_mctx_5525_, 3);
v_lDecls_5537_ = lean_ctor_get(v_mctx_5525_, 4);
v_decls_5538_ = lean_ctor_get(v_mctx_5525_, 5);
v_userNames_5539_ = lean_ctor_get(v_mctx_5525_, 6);
v_lAssignment_5540_ = lean_ctor_get(v_mctx_5525_, 7);
v_eAssignment_5541_ = lean_ctor_get(v_mctx_5525_, 8);
v_dAssignment_5542_ = lean_ctor_get(v_mctx_5525_, 9);
v_instanceTypedMVars_5543_ = lean_ctor_get(v_mctx_5525_, 10);
v_synthNormMemo_5544_ = lean_ctor_get(v_mctx_5525_, 11);
v_isSharedCheck_5558_ = !lean_is_exclusive(v_mctx_5525_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5546_ = v_mctx_5525_;
v_isShared_5547_ = v_isSharedCheck_5558_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_synthNormMemo_5544_);
lean_inc(v_instanceTypedMVars_5543_);
lean_inc(v_dAssignment_5542_);
lean_inc(v_eAssignment_5541_);
lean_inc(v_lAssignment_5540_);
lean_inc(v_userNames_5539_);
lean_inc(v_decls_5538_);
lean_inc(v_lDecls_5537_);
lean_inc(v_mvarCounter_5536_);
lean_inc(v_lmvarCounter_5535_);
lean_inc(v_levelAssignDepth_5534_);
lean_inc(v_depth_5533_);
lean_dec(v_mctx_5525_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5558_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5551_; 
v___x_5548_ = lean_box(0);
v___x_5549_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_5541_, v_mvarId_5520_, v_val_5521_);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 8, v___x_5549_);
v___x_5551_ = v___x_5546_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_depth_5533_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v_levelAssignDepth_5534_);
lean_ctor_set(v_reuseFailAlloc_5557_, 2, v_lmvarCounter_5535_);
lean_ctor_set(v_reuseFailAlloc_5557_, 3, v_mvarCounter_5536_);
lean_ctor_set(v_reuseFailAlloc_5557_, 4, v_lDecls_5537_);
lean_ctor_set(v_reuseFailAlloc_5557_, 5, v_decls_5538_);
lean_ctor_set(v_reuseFailAlloc_5557_, 6, v_userNames_5539_);
lean_ctor_set(v_reuseFailAlloc_5557_, 7, v_lAssignment_5540_);
lean_ctor_set(v_reuseFailAlloc_5557_, 8, v___x_5549_);
lean_ctor_set(v_reuseFailAlloc_5557_, 9, v_dAssignment_5542_);
lean_ctor_set(v_reuseFailAlloc_5557_, 10, v_instanceTypedMVars_5543_);
lean_ctor_set(v_reuseFailAlloc_5557_, 11, v_synthNormMemo_5544_);
v___x_5551_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
lean_object* v___x_5553_; 
if (v_isShared_5532_ == 0)
{
lean_ctor_set(v___x_5531_, 0, v___x_5551_);
v___x_5553_ = v___x_5531_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v_cache_5526_);
lean_ctor_set(v_reuseFailAlloc_5556_, 2, v_zetaDeltaFVarIds_5527_);
lean_ctor_set(v_reuseFailAlloc_5556_, 3, v_postponed_5528_);
lean_ctor_set(v_reuseFailAlloc_5556_, 4, v_diag_5529_);
v___x_5553_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5554_; lean_object* v___x_5555_; 
v___x_5554_ = lean_st_ref_put(v___y_5522_, v___x_5553_);
v___x_5555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5548_);
return v___x_5555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg___boxed(lean_object* v_mvarId_5560_, lean_object* v_val_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_){
_start:
{
lean_object* v_res_5564_; 
v_res_5564_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5560_, v_val_5561_, v___y_5562_);
lean_dec(v___y_5562_);
return v_res_5564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5570_, lean_object* v_goal_5571_, lean_object* v_reflectionResult_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_){
_start:
{
lean_object* v_cert_5586_; lean_object* v___y_5587_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5592_; lean_object* v___y_5593_; lean_object* v___y_5594_; lean_object* v___y_5595_; lean_object* v___y_5596_; lean_object* v___y_5597_; lean_object* v_toCold_5629_; lean_object* v_options_5630_; uint8_t v_hasTrace_5631_; 
v_toCold_5629_ = lean_ctor_get(v_a_5582_, 0);
v_options_5630_ = lean_ctor_get(v_toCold_5629_, 2);
v_hasTrace_5631_ = lean_ctor_get_uint8(v_options_5630_, sizeof(void*)*1);
if (v_hasTrace_5631_ == 0)
{
lean_object* v_config_5632_; lean_object* v_lratPath_5633_; uint8_t v_trimProofs_5634_; lean_object* v___x_5635_; 
v_config_5632_ = lean_ctor_get(v_ctx_5570_, 5);
v_lratPath_5633_ = lean_ctor_get(v_ctx_5570_, 4);
v_trimProofs_5634_ = lean_ctor_get_uint8(v_config_5632_, sizeof(void*)*3);
v___x_5635_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5633_, v_trimProofs_5634_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5635_) == 0)
{
lean_object* v_a_5636_; 
v_a_5636_ = lean_ctor_get(v___x_5635_, 0);
lean_inc(v_a_5636_);
lean_dec_ref_known(v___x_5635_, 1);
v_cert_5586_ = v_a_5636_;
v___y_5587_ = v_a_5573_;
v___y_5588_ = v_a_5574_;
v___y_5589_ = v_a_5575_;
v___y_5590_ = v_a_5576_;
v___y_5591_ = v_a_5577_;
v___y_5592_ = v_a_5578_;
v___y_5593_ = v_a_5579_;
v___y_5594_ = v_a_5580_;
v___y_5595_ = v_a_5581_;
v___y_5596_ = v_a_5582_;
v___y_5597_ = v_a_5583_;
goto v___jp_5585_;
}
else
{
lean_object* v_a_5637_; lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5644_; 
lean_dec_ref(v_reflectionResult_5572_);
lean_dec(v_goal_5571_);
lean_dec_ref(v_ctx_5570_);
v_a_5637_ = lean_ctor_get(v___x_5635_, 0);
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5635_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5639_ = v___x_5635_;
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
else
{
lean_inc(v_a_5637_);
lean_dec(v___x_5635_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5642_; 
if (v_isShared_5640_ == 0)
{
v___x_5642_ = v___x_5639_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5637_);
v___x_5642_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
return v___x_5642_;
}
}
}
}
else
{
lean_object* v_config_5645_; lean_object* v_lratPath_5646_; uint8_t v_trimProofs_5647_; lean_object* v_inheritedTraceOptions_5648_; lean_object* v___f_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; uint8_t v___x_5653_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v_a_5657_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v_a_5672_; lean_object* v___y_5675_; lean_object* v___y_5676_; lean_object* v_a_5677_; lean_object* v___y_5687_; lean_object* v___y_5688_; lean_object* v_a_5689_; 
v_config_5645_ = lean_ctor_get(v_ctx_5570_, 5);
v_lratPath_5646_ = lean_ctor_get(v_ctx_5570_, 4);
v_trimProofs_5647_ = lean_ctor_get_uint8(v_config_5645_, sizeof(void*)*3);
v_inheritedTraceOptions_5648_ = lean_ctor_get(v_toCold_5629_, 11);
v___f_5649_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__1));
v___x_5650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5653_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5648_, v_options_5630_, v___x_5652_);
if (v___x_5653_ == 0)
{
lean_object* v___x_5722_; uint8_t v___x_5723_; 
v___x_5722_ = l_Lean_trace_profiler;
v___x_5723_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5630_, v___x_5722_);
if (v___x_5723_ == 0)
{
lean_object* v___x_5724_; 
v___x_5724_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5646_, v_trimProofs_5647_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_a_5725_; 
v_a_5725_ = lean_ctor_get(v___x_5724_, 0);
lean_inc(v_a_5725_);
lean_dec_ref_known(v___x_5724_, 1);
v_cert_5586_ = v_a_5725_;
v___y_5587_ = v_a_5573_;
v___y_5588_ = v_a_5574_;
v___y_5589_ = v_a_5575_;
v___y_5590_ = v_a_5576_;
v___y_5591_ = v_a_5577_;
v___y_5592_ = v_a_5578_;
v___y_5593_ = v_a_5579_;
v___y_5594_ = v_a_5580_;
v___y_5595_ = v_a_5581_;
v___y_5596_ = v_a_5582_;
v___y_5597_ = v_a_5583_;
goto v___jp_5585_;
}
else
{
lean_object* v_a_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5733_; 
lean_dec_ref(v_reflectionResult_5572_);
lean_dec(v_goal_5571_);
lean_dec_ref(v_ctx_5570_);
v_a_5726_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5733_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5733_ == 0)
{
v___x_5728_ = v___x_5724_;
v_isShared_5729_ = v_isSharedCheck_5733_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_a_5726_);
lean_dec(v___x_5724_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5733_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v___x_5731_; 
if (v_isShared_5729_ == 0)
{
v___x_5731_ = v___x_5728_;
goto v_reusejp_5730_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_a_5726_);
v___x_5731_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5730_;
}
v_reusejp_5730_:
{
return v___x_5731_;
}
}
}
}
else
{
goto v___jp_5691_;
}
}
else
{
goto v___jp_5691_;
}
v___jp_5654_:
{
lean_object* v___x_5658_; double v___x_5659_; double v___x_5660_; double v___x_5661_; double v___x_5662_; double v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; 
v___x_5658_ = lean_io_mono_nanos_now();
v___x_5659_ = lean_float_of_nat(v___y_5656_);
v___x_5660_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5661_ = lean_float_div(v___x_5659_, v___x_5660_);
v___x_5662_ = lean_float_of_nat(v___x_5658_);
v___x_5663_ = lean_float_div(v___x_5662_, v___x_5660_);
v___x_5664_ = lean_box_float(v___x_5661_);
v___x_5665_ = lean_box_float(v___x_5663_);
v___x_5666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5664_);
lean_ctor_set(v___x_5666_, 1, v___x_5665_);
v___x_5667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5667_, 0, v_a_5657_);
lean_ctor_set(v___x_5667_, 1, v___x_5666_);
v___x_5668_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5650_, v_hasTrace_5631_, v___x_5651_, v_options_5630_, v___x_5653_, v___y_5655_, v___f_5649_, v___x_5667_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
return v___x_5668_;
}
v___jp_5669_:
{
lean_object* v___x_5673_; 
v___x_5673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5673_, 0, v_a_5672_);
v___y_5655_ = v___y_5670_;
v___y_5656_ = v___y_5671_;
v_a_5657_ = v___x_5673_;
goto v___jp_5654_;
}
v___jp_5674_:
{
lean_object* v___x_5678_; double v___x_5679_; double v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; 
v___x_5678_ = lean_io_get_num_heartbeats();
v___x_5679_ = lean_float_of_nat(v___y_5676_);
v___x_5680_ = lean_float_of_nat(v___x_5678_);
v___x_5681_ = lean_box_float(v___x_5679_);
v___x_5682_ = lean_box_float(v___x_5680_);
v___x_5683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5681_);
lean_ctor_set(v___x_5683_, 1, v___x_5682_);
v___x_5684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5684_, 0, v_a_5677_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5650_, v_hasTrace_5631_, v___x_5651_, v_options_5630_, v___x_5653_, v___y_5675_, v___f_5649_, v___x_5684_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
return v___x_5685_;
}
v___jp_5686_:
{
lean_object* v___x_5690_; 
v___x_5690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5690_, 0, v_a_5689_);
v___y_5675_ = v___y_5687_;
v___y_5676_ = v___y_5688_;
v_a_5677_ = v___x_5690_;
goto v___jp_5674_;
}
v___jp_5691_:
{
lean_object* v___x_5692_; lean_object* v_a_5693_; lean_object* v___x_5694_; uint8_t v___x_5695_; 
v___x_5692_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v_a_5583_);
v_a_5693_ = lean_ctor_get(v___x_5692_, 0);
lean_inc(v_a_5693_);
lean_dec_ref(v___x_5692_);
v___x_5694_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5695_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5630_, v___x_5694_);
if (v___x_5695_ == 0)
{
lean_object* v___x_5696_; lean_object* v___x_5697_; 
v___x_5696_ = lean_io_mono_nanos_now();
v___x_5697_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5646_, v_trimProofs_5647_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5697_) == 0)
{
lean_object* v_a_5698_; lean_object* v___x_5699_; 
v_a_5698_ = lean_ctor_get(v___x_5697_, 0);
lean_inc(v_a_5698_);
lean_dec_ref_known(v___x_5697_, 1);
lean_inc_ref(v_reflectionResult_5572_);
v___x_5699_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5698_, v_ctx_5570_, v_reflectionResult_5572_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5699_) == 0)
{
lean_object* v_a_5700_; lean_object* v_satExpr_5701_; lean_object* v___x_5702_; 
v_a_5700_ = lean_ctor_get(v___x_5699_, 0);
lean_inc(v_a_5700_);
lean_dec_ref_known(v___x_5699_, 1);
v_satExpr_5701_ = lean_ctor_get(v_reflectionResult_5572_, 0);
lean_inc_ref(v_satExpr_5701_);
lean_dec_ref(v_reflectionResult_5572_);
v___x_5702_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5701_, v_a_5700_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5702_) == 0)
{
lean_object* v_a_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; 
v_a_5703_ = lean_ctor_get(v___x_5702_, 0);
lean_inc(v_a_5703_);
lean_dec_ref_known(v___x_5702_, 1);
v___x_5704_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5571_, v_a_5703_, v_a_5581_);
lean_dec_ref(v___x_5704_);
v___x_5705_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5655_ = v_a_5693_;
v___y_5656_ = v___x_5696_;
v_a_5657_ = v___x_5705_;
goto v___jp_5654_;
}
else
{
lean_object* v_a_5706_; 
lean_dec(v_goal_5571_);
v_a_5706_ = lean_ctor_get(v___x_5702_, 0);
lean_inc(v_a_5706_);
lean_dec_ref_known(v___x_5702_, 1);
v___y_5670_ = v_a_5693_;
v___y_5671_ = v___x_5696_;
v_a_5672_ = v_a_5706_;
goto v___jp_5669_;
}
}
else
{
lean_object* v_a_5707_; 
lean_dec_ref(v_reflectionResult_5572_);
lean_dec(v_goal_5571_);
v_a_5707_ = lean_ctor_get(v___x_5699_, 0);
lean_inc(v_a_5707_);
lean_dec_ref_known(v___x_5699_, 1);
v___y_5670_ = v_a_5693_;
v___y_5671_ = v___x_5696_;
v_a_5672_ = v_a_5707_;
goto v___jp_5669_;
}
}
else
{
lean_object* v_a_5708_; 
lean_dec_ref(v_reflectionResult_5572_);
lean_dec(v_goal_5571_);
lean_dec_ref(v_ctx_5570_);
v_a_5708_ = lean_ctor_get(v___x_5697_, 0);
lean_inc(v_a_5708_);
lean_dec_ref_known(v___x_5697_, 1);
v___y_5670_ = v_a_5693_;
v___y_5671_ = v___x_5696_;
v_a_5672_ = v_a_5708_;
goto v___jp_5669_;
}
}
else
{
lean_object* v___x_5709_; lean_object* v___x_5710_; 
v___x_5709_ = lean_io_get_num_heartbeats();
v___x_5710_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5646_, v_trimProofs_5647_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5710_) == 0)
{
lean_object* v_a_5711_; lean_object* v___x_5712_; 
v_a_5711_ = lean_ctor_get(v___x_5710_, 0);
lean_inc(v_a_5711_);
lean_dec_ref_known(v___x_5710_, 1);
lean_inc_ref(v_reflectionResult_5572_);
v___x_5712_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5711_, v_ctx_5570_, v_reflectionResult_5572_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5712_) == 0)
{
lean_object* v_a_5713_; lean_object* v_satExpr_5714_; lean_object* v___x_5715_; 
v_a_5713_ = lean_ctor_get(v___x_5712_, 0);
lean_inc(v_a_5713_);
lean_dec_ref_known(v___x_5712_, 1);
v_satExpr_5714_ = lean_ctor_get(v_reflectionResult_5572_, 0);
lean_inc_ref(v_satExpr_5714_);
lean_dec_ref(v_reflectionResult_5572_);
v___x_5715_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5714_, v_a_5713_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
if (lean_obj_tag(v___x_5715_) == 0)
{
lean_object* v_a_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; 
v_a_5716_ = lean_ctor_get(v___x_5715_, 0);
lean_inc(v_a_5716_);
lean_dec_ref_known(v___x_5715_, 1);
v___x_5717_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5571_, v_a_5716_, v_a_5581_);
lean_dec_ref(v___x_5717_);
v___x_5718_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5675_ = v_a_5693_;
v___y_5676_ = v___x_5709_;
v_a_5677_ = v___x_5718_;
goto v___jp_5674_;
}
else
{
lean_object* v_a_5719_; 
lean_dec(v_goal_5571_);
v_a_5719_ = lean_ctor_get(v___x_5715_, 0);
lean_inc(v_a_5719_);
lean_dec_ref_known(v___x_5715_, 1);
v___y_5687_ = v_a_5693_;
v___y_5688_ = v___x_5709_;
v_a_5689_ = v_a_5719_;
goto v___jp_5686_;
}
}
else
{
lean_object* v_a_5720_; 
lean_dec_ref(v_reflectionResult_5572_);
lean_dec(v_goal_5571_);
v_a_5720_ = lean_ctor_get(v___x_5712_, 0);
lean_inc(v_a_5720_);
lean_dec_ref_known(v___x_5712_, 1);
v___y_5687_ = v_a_5693_;
v___y_5688_ = v___x_5709_;
v_a_5689_ = v_a_5720_;
goto v___jp_5686_;
}
}
else
{
lean_object* v_a_5721_; 
lean_dec_ref(v_reflectionResult_5572_);
lean_dec(v_goal_5571_);
lean_dec_ref(v_ctx_5570_);
v_a_5721_ = lean_ctor_get(v___x_5710_, 0);
lean_inc(v_a_5721_);
lean_dec_ref_known(v___x_5710_, 1);
v___y_5687_ = v_a_5693_;
v___y_5688_ = v___x_5709_;
v_a_5689_ = v_a_5721_;
goto v___jp_5686_;
}
}
}
}
v___jp_5585_:
{
lean_object* v___x_5598_; 
lean_inc_ref(v_reflectionResult_5572_);
v___x_5598_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_5586_, v_ctx_5570_, v_reflectionResult_5572_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_);
if (lean_obj_tag(v___x_5598_) == 0)
{
lean_object* v_a_5599_; lean_object* v_satExpr_5600_; lean_object* v___x_5601_; 
v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
lean_inc(v_a_5599_);
lean_dec_ref_known(v___x_5598_, 1);
v_satExpr_5600_ = lean_ctor_get(v_reflectionResult_5572_, 0);
lean_inc_ref(v_satExpr_5600_);
lean_dec_ref(v_reflectionResult_5572_);
v___x_5601_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5600_, v_a_5599_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_);
if (lean_obj_tag(v___x_5601_) == 0)
{
lean_object* v_a_5602_; lean_object* v___x_5603_; lean_object* v___x_5605_; uint8_t v_isShared_5606_; uint8_t v_isSharedCheck_5611_; 
v_a_5602_ = lean_ctor_get(v___x_5601_, 0);
lean_inc(v_a_5602_);
lean_dec_ref_known(v___x_5601_, 1);
v___x_5603_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5571_, v_a_5602_, v___y_5595_);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5603_);
if (v_isSharedCheck_5611_ == 0)
{
lean_object* v_unused_5612_; 
v_unused_5612_ = lean_ctor_get(v___x_5603_, 0);
lean_dec(v_unused_5612_);
v___x_5605_ = v___x_5603_;
v_isShared_5606_ = v_isSharedCheck_5611_;
goto v_resetjp_5604_;
}
else
{
lean_dec(v___x_5603_);
v___x_5605_ = lean_box(0);
v_isShared_5606_ = v_isSharedCheck_5611_;
goto v_resetjp_5604_;
}
v_resetjp_5604_:
{
lean_object* v___x_5607_; lean_object* v___x_5609_; 
v___x_5607_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
if (v_isShared_5606_ == 0)
{
lean_ctor_set(v___x_5605_, 0, v___x_5607_);
v___x_5609_ = v___x_5605_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v___x_5607_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
else
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5620_; 
lean_dec(v_goal_5571_);
v_a_5613_ = lean_ctor_get(v___x_5601_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5601_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5615_ = v___x_5601_;
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5601_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5618_; 
if (v_isShared_5616_ == 0)
{
v___x_5618_ = v___x_5615_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5613_);
v___x_5618_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
return v___x_5618_;
}
}
}
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
lean_dec_ref(v_reflectionResult_5572_);
lean_dec(v_goal_5571_);
v_a_5621_ = lean_ctor_get(v___x_5598_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5598_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5598_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5734_, lean_object* v_goal_5735_, lean_object* v_reflectionResult_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_){
_start:
{
lean_object* v_res_5749_; 
v_res_5749_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5734_, v_goal_5735_, v_reflectionResult_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec(v_a_5747_);
lean_dec_ref(v_a_5746_);
lean_dec(v_a_5745_);
lean_dec_ref(v_a_5744_);
lean_dec(v_a_5743_);
lean_dec_ref(v_a_5742_);
lean_dec(v_a_5741_);
lean_dec_ref(v_a_5740_);
lean_dec(v_a_5739_);
lean_dec(v_a_5738_);
lean_dec_ref(v_a_5737_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5750_, lean_object* v_goal_5751_, lean_object* v_reflectionResult_5752_, lean_object* v_x_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_){
_start:
{
lean_object* v___x_5766_; 
v___x_5766_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5750_, v_goal_5751_, v_reflectionResult_5752_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_);
return v___x_5766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5767_, lean_object* v_goal_5768_, lean_object* v_reflectionResult_5769_, lean_object* v_x_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_){
_start:
{
lean_object* v_res_5783_; 
v_res_5783_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5767_, v_goal_5768_, v_reflectionResult_5769_, v_x_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_);
lean_dec(v_a_5781_);
lean_dec_ref(v_a_5780_);
lean_dec(v_a_5779_);
lean_dec_ref(v_a_5778_);
lean_dec(v_a_5777_);
lean_dec_ref(v_a_5776_);
lean_dec(v_a_5775_);
lean_dec_ref(v_a_5774_);
lean_dec(v_a_5773_);
lean_dec(v_a_5772_);
lean_dec_ref(v_a_5771_);
lean_dec(v_x_5770_);
return v_res_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_mvarId_5784_, lean_object* v_val_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v___x_5798_; 
v___x_5798_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5784_, v_val_5785_, v___y_5794_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_mvarId_5799_, lean_object* v_val_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_){
_start:
{
lean_object* v_res_5813_; 
v_res_5813_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_mvarId_5799_, v_val_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5808_);
lean_dec(v___y_5807_);
lean_dec_ref(v___y_5806_);
lean_dec(v___y_5805_);
lean_dec_ref(v___y_5804_);
lean_dec(v___y_5803_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
return v_res_5813_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(lean_object* v_00_u03b1_5814_, lean_object* v_x_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
lean_object* v___x_5828_; 
v___x_5828_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5815_);
return v___x_5828_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5829_, lean_object* v_x_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_){
_start:
{
lean_object* v_res_5843_; 
v_res_5843_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(v_00_u03b1_5829_, v_x_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_);
lean_dec(v___y_5841_);
lean_dec_ref(v___y_5840_);
lean_dec(v___y_5839_);
lean_dec_ref(v___y_5838_);
lean_dec(v___y_5837_);
lean_dec_ref(v___y_5836_);
lean_dec(v___y_5835_);
lean_dec_ref(v___y_5834_);
lean_dec(v___y_5833_);
lean_dec(v___y_5832_);
lean_dec_ref(v___y_5831_);
return v_res_5843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(lean_object* v_oldTraces_5844_, lean_object* v_data_5845_, lean_object* v_ref_5846_, lean_object* v_msg_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_){
_start:
{
lean_object* v___x_5860_; 
v___x_5860_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5844_, v_data_5845_, v_ref_5846_, v_msg_5847_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_);
return v___x_5860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___boxed(lean_object* v_oldTraces_5861_, lean_object* v_data_5862_, lean_object* v_ref_5863_, lean_object* v_msg_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_){
_start:
{
lean_object* v_res_5877_; 
v_res_5877_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(v_oldTraces_5861_, v_data_5862_, v_ref_5863_, v_msg_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
lean_dec(v___y_5875_);
lean_dec_ref(v___y_5874_);
lean_dec(v___y_5873_);
lean_dec_ref(v___y_5872_);
lean_dec(v___y_5871_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5869_);
lean_dec_ref(v___y_5868_);
lean_dec(v___y_5867_);
lean_dec(v___y_5866_);
lean_dec_ref(v___y_5865_);
return v_res_5877_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Native(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_TacticContext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Native(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Native(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Prover_Bitblast(builtin);
}
#ifdef __cplusplus
}
#endif
