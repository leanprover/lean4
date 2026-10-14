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
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_toCNF_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_byte_array_push(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toCold_55_; lean_object* v_currRecDepth_56_; lean_object* v_ref_57_; uint8_t v_suppressElabErrors_58_; uint8_t v_isRecordingDeps_59_; lean_object* v_fileName_60_; lean_object* v_fileMap_61_; lean_object* v_options_62_; lean_object* v_currNamespace_63_; lean_object* v_openDecls_64_; lean_object* v_initHeartbeats_65_; lean_object* v_maxHeartbeats_66_; lean_object* v_quotContext_67_; lean_object* v_currMacroScope_68_; lean_object* v_cancelTk_x3f_69_; lean_object* v_inheritedTraceOptions_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; uint8_t v___x_79_; lean_object* v___y_81_; uint16_t v___y_82_; lean_object* v_fileName_83_; lean_object* v_fileMap_84_; lean_object* v_currNamespace_85_; lean_object* v_openDecls_86_; lean_object* v_initHeartbeats_87_; lean_object* v_maxHeartbeats_88_; lean_object* v_quotContext_89_; lean_object* v_currMacroScope_90_; lean_object* v_cancelTk_x3f_91_; lean_object* v_inheritedTraceOptions_92_; lean_object* v_currRecDepth_93_; lean_object* v_ref_94_; uint8_t v_suppressElabErrors_95_; uint8_t v_isRecordingDeps_96_; lean_object* v___y_97_; uint8_t v___y_104_; lean_object* v___y_105_; uint16_t v___y_106_; lean_object* v___y_129_; 
v_toCold_55_ = lean_ctor_get(v_a_52_, 0);
v_currRecDepth_56_ = lean_ctor_get(v_a_52_, 1);
v_ref_57_ = lean_ctor_get(v_a_52_, 2);
v_suppressElabErrors_58_ = lean_ctor_get_uint8(v_a_52_, sizeof(void*)*3 + 2);
v_isRecordingDeps_59_ = lean_ctor_get_uint8(v_a_52_, sizeof(void*)*3 + 3);
v_fileName_60_ = lean_ctor_get(v_toCold_55_, 0);
v_fileMap_61_ = lean_ctor_get(v_toCold_55_, 1);
v_options_62_ = lean_ctor_get(v_toCold_55_, 2);
v_currNamespace_63_ = lean_ctor_get(v_toCold_55_, 4);
v_openDecls_64_ = lean_ctor_get(v_toCold_55_, 5);
v_initHeartbeats_65_ = lean_ctor_get(v_toCold_55_, 6);
v_maxHeartbeats_66_ = lean_ctor_get(v_toCold_55_, 7);
v_quotContext_67_ = lean_ctor_get(v_toCold_55_, 8);
v_currMacroScope_68_ = lean_ctor_get(v_toCold_55_, 9);
v_cancelTk_x3f_69_ = lean_ctor_get(v_toCold_55_, 10);
v_inheritedTraceOptions_70_ = lean_ctor_get(v_toCold_55_, 11);
v___x_71_ = lean_box(0);
lean_inc(v_name_49_);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v_name_49_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_ctor_set(v___x_72_, 2, v_type_51_);
v___x_73_ = lean_box(1);
v___x_74_ = 1;
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v_name_49_);
lean_ctor_set(v___x_75_, 1, v___x_71_);
v___x_76_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_76_, 0, v___x_72_);
lean_ctor_set(v___x_76_, 1, v_value_50_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
lean_ctor_set(v___x_76_, 3, v___x_75_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*4, v___x_74_);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
v___x_78_ = 1;
v___x_79_ = 0;
if (v_isRecordingDeps_59_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__5));
lean_inc_ref(v_options_62_);
v___x_139_ = l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1(v_options_62_, v___x_138_, v_isRecordingDeps_59_);
v___y_129_ = v___x_139_;
goto v___jp_128_;
}
else
{
lean_object* v___x_140_; 
lean_inc_ref(v_options_62_);
v___x_140_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_62_);
v___y_129_ = v___x_140_;
goto v___jp_128_;
}
v___jp_80_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_98_ = l_Lean_maxRecDepth;
v___x_99_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v___y_81_, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_100_, 0, v_fileName_83_);
lean_ctor_set(v___x_100_, 1, v_fileMap_84_);
lean_ctor_set(v___x_100_, 2, v___y_81_);
lean_ctor_set(v___x_100_, 3, v___x_99_);
lean_ctor_set(v___x_100_, 4, v_currNamespace_85_);
lean_ctor_set(v___x_100_, 5, v_openDecls_86_);
lean_ctor_set(v___x_100_, 6, v_initHeartbeats_87_);
lean_ctor_set(v___x_100_, 7, v_maxHeartbeats_88_);
lean_ctor_set(v___x_100_, 8, v_quotContext_89_);
lean_ctor_set(v___x_100_, 9, v_currMacroScope_90_);
lean_ctor_set(v___x_100_, 10, v_cancelTk_x3f_91_);
lean_ctor_set(v___x_100_, 11, v_inheritedTraceOptions_92_);
lean_inc(v_ref_94_);
lean_inc(v_currRecDepth_93_);
v___x_101_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_currRecDepth_93_);
lean_ctor_set(v___x_101_, 2, v_ref_94_);
lean_ctor_set_uint16(v___x_101_, sizeof(void*)*3, v___y_82_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*3 + 2, v_suppressElabErrors_95_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*3 + 3, v_isRecordingDeps_96_);
v___x_102_ = l_Lean_addAndCompile(v___x_77_, v___x_78_, v___x_79_, v___x_101_, v___y_97_);
lean_dec_ref_known(v___x_101_, 3);
return v___x_102_;
}
v___jp_103_:
{
lean_object* v___x_107_; lean_object* v_env_108_; lean_object* v_nextMacroScope_109_; lean_object* v_ngen_110_; lean_object* v_auxDeclNGen_111_; lean_object* v_traceState_112_; lean_object* v_recordedDeps_113_; lean_object* v_messages_114_; lean_object* v_infoState_115_; lean_object* v_snapshotTasks_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_126_; 
v___x_107_ = lean_st_ref_take(v_a_53_);
v_env_108_ = lean_ctor_get(v___x_107_, 0);
v_nextMacroScope_109_ = lean_ctor_get(v___x_107_, 1);
v_ngen_110_ = lean_ctor_get(v___x_107_, 2);
v_auxDeclNGen_111_ = lean_ctor_get(v___x_107_, 3);
v_traceState_112_ = lean_ctor_get(v___x_107_, 4);
v_recordedDeps_113_ = lean_ctor_get(v___x_107_, 6);
v_messages_114_ = lean_ctor_get(v___x_107_, 7);
v_infoState_115_ = lean_ctor_get(v___x_107_, 8);
v_snapshotTasks_116_ = lean_ctor_get(v___x_107_, 9);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v___x_107_, 5);
lean_dec(v_unused_127_);
v___x_118_ = v___x_107_;
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snapshotTasks_116_);
lean_inc(v_infoState_115_);
lean_inc(v_messages_114_);
lean_inc(v_recordedDeps_113_);
lean_inc(v_traceState_112_);
lean_inc(v_auxDeclNGen_111_);
lean_inc(v_ngen_110_);
lean_inc(v_nextMacroScope_109_);
lean_inc(v_env_108_);
lean_dec(v___x_107_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = l_Lean_Kernel_enableDiag(v_env_108_, v___y_104_);
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___closed__2);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 5, v___x_121_);
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_nextMacroScope_109_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_ngen_110_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_auxDeclNGen_111_);
lean_ctor_set(v_reuseFailAlloc_125_, 4, v_traceState_112_);
lean_ctor_set(v_reuseFailAlloc_125_, 5, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 6, v_recordedDeps_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 7, v_messages_114_);
lean_ctor_set(v_reuseFailAlloc_125_, 8, v_infoState_115_);
lean_ctor_set(v_reuseFailAlloc_125_, 9, v_snapshotTasks_116_);
v___x_123_ = v_reuseFailAlloc_125_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; 
v___x_124_ = lean_st_ref_put(v_a_53_, v___x_123_);
lean_inc_ref(v_inheritedTraceOptions_70_);
lean_inc(v_cancelTk_x3f_69_);
lean_inc(v_currMacroScope_68_);
lean_inc(v_quotContext_67_);
lean_inc(v_maxHeartbeats_66_);
lean_inc(v_initHeartbeats_65_);
lean_inc(v_openDecls_64_);
lean_inc(v_currNamespace_63_);
lean_inc_ref(v_fileMap_61_);
lean_inc_ref(v_fileName_60_);
v___y_81_ = v___y_105_;
v___y_82_ = v___y_106_;
v_fileName_83_ = v_fileName_60_;
v_fileMap_84_ = v_fileMap_61_;
v_currNamespace_85_ = v_currNamespace_63_;
v_openDecls_86_ = v_openDecls_64_;
v_initHeartbeats_87_ = v_initHeartbeats_65_;
v_maxHeartbeats_88_ = v_maxHeartbeats_66_;
v_quotContext_89_ = v_quotContext_67_;
v_currMacroScope_90_ = v_currMacroScope_68_;
v_cancelTk_x3f_91_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_92_ = v_inheritedTraceOptions_70_;
v_currRecDepth_93_ = v_currRecDepth_56_;
v_ref_94_ = v_ref_57_;
v_suppressElabErrors_95_ = v_suppressElabErrors_58_;
v_isRecordingDeps_96_ = v_isRecordingDeps_59_;
v___y_97_ = v_a_53_;
goto v___jp_80_;
}
}
}
v___jp_128_:
{
uint16_t v___x_130_; lean_object* v___x_131_; lean_object* v_env_132_; uint8_t v___x_133_; uint16_t v___x_134_; uint16_t v___x_135_; uint16_t v___x_136_; uint8_t v___x_137_; 
v___x_130_ = l_Lean_OptionFlags_ofOptions(v___y_129_);
v___x_131_ = lean_st_ref_get(v_a_53_);
v_env_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_env_132_);
lean_dec(v___x_131_);
v___x_133_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_132_);
lean_dec_ref(v_env_132_);
v___x_134_ = 512;
v___x_135_ = lean_uint16_land(v___x_130_, v___x_134_);
v___x_136_ = 0;
v___x_137_ = lean_uint16_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
if (v___x_133_ == 0)
{
v___y_104_ = v___x_78_;
v___y_105_ = v___y_129_;
v___y_106_ = v___x_130_;
goto v___jp_103_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_70_);
lean_inc(v_cancelTk_x3f_69_);
lean_inc(v_currMacroScope_68_);
lean_inc(v_quotContext_67_);
lean_inc(v_maxHeartbeats_66_);
lean_inc(v_initHeartbeats_65_);
lean_inc(v_openDecls_64_);
lean_inc(v_currNamespace_63_);
lean_inc_ref(v_fileMap_61_);
lean_inc_ref(v_fileName_60_);
v___y_81_ = v___y_129_;
v___y_82_ = v___x_130_;
v_fileName_83_ = v_fileName_60_;
v_fileMap_84_ = v_fileMap_61_;
v_currNamespace_85_ = v_currNamespace_63_;
v_openDecls_86_ = v_openDecls_64_;
v_initHeartbeats_87_ = v_initHeartbeats_65_;
v_maxHeartbeats_88_ = v_maxHeartbeats_66_;
v_quotContext_89_ = v_quotContext_67_;
v_currMacroScope_90_ = v_currMacroScope_68_;
v_cancelTk_x3f_91_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_92_ = v_inheritedTraceOptions_70_;
v_currRecDepth_93_ = v_currRecDepth_56_;
v_ref_94_ = v_ref_57_;
v_suppressElabErrors_95_ = v_suppressElabErrors_58_;
v_isRecordingDeps_96_ = v_isRecordingDeps_59_;
v___y_97_ = v_a_53_;
goto v___jp_80_;
}
}
else
{
if (v___x_133_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_70_);
lean_inc(v_cancelTk_x3f_69_);
lean_inc(v_currMacroScope_68_);
lean_inc(v_quotContext_67_);
lean_inc(v_maxHeartbeats_66_);
lean_inc(v_initHeartbeats_65_);
lean_inc(v_openDecls_64_);
lean_inc(v_currNamespace_63_);
lean_inc_ref(v_fileMap_61_);
lean_inc_ref(v_fileName_60_);
v___y_81_ = v___y_129_;
v___y_82_ = v___x_130_;
v_fileName_83_ = v_fileName_60_;
v_fileMap_84_ = v_fileMap_61_;
v_currNamespace_85_ = v_currNamespace_63_;
v_openDecls_86_ = v_openDecls_64_;
v_initHeartbeats_87_ = v_initHeartbeats_65_;
v_maxHeartbeats_88_ = v_maxHeartbeats_66_;
v_quotContext_89_ = v_quotContext_67_;
v_currMacroScope_90_ = v_currMacroScope_68_;
v_cancelTk_x3f_91_ = v_cancelTk_x3f_69_;
v_inheritedTraceOptions_92_ = v_inheritedTraceOptions_70_;
v_currRecDepth_93_ = v_currRecDepth_56_;
v_ref_94_ = v_ref_57_;
v_suppressElabErrors_95_ = v_suppressElabErrors_58_;
v_isRecordingDeps_96_ = v_isRecordingDeps_59_;
v___y_97_ = v_a_53_;
goto v___jp_80_;
}
else
{
v___y_104_ = v___x_79_;
v___y_105_ = v___y_129_;
v___y_106_ = v___x_130_;
goto v___jp_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl___boxed(lean_object* v_name_141_, lean_object* v_value_142_, lean_object* v_type_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_name_141_, v_value_142_, v_type_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
return v_res_147_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(32u);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_151_ = ((size_t)5ULL);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_unsigned_to_nat(32u);
v___x_154_ = lean_mk_empty_array_with_capacity(v___x_153_);
v___x_155_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__0);
v___x_156_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_154_);
lean_ctor_set(v___x_156_, 2, v___x_152_);
lean_ctor_set(v___x_156_, 3, v___x_152_);
lean_ctor_set_usize(v___x_156_, 4, v___x_151_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; lean_object* v_traceState_160_; lean_object* v_traces_161_; lean_object* v___x_162_; lean_object* v_traceState_163_; lean_object* v_env_164_; lean_object* v_nextMacroScope_165_; lean_object* v_ngen_166_; lean_object* v_auxDeclNGen_167_; lean_object* v_cache_168_; lean_object* v_recordedDeps_169_; lean_object* v_messages_170_; lean_object* v_infoState_171_; lean_object* v_snapshotTasks_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_191_; 
v___x_159_ = lean_st_ref_get(v___y_157_);
v_traceState_160_ = lean_ctor_get(v___x_159_, 4);
lean_inc_ref(v_traceState_160_);
lean_dec(v___x_159_);
v_traces_161_ = lean_ctor_get(v_traceState_160_, 0);
lean_inc_ref(v_traces_161_);
lean_dec_ref(v_traceState_160_);
v___x_162_ = lean_st_ref_take(v___y_157_);
v_traceState_163_ = lean_ctor_get(v___x_162_, 4);
v_env_164_ = lean_ctor_get(v___x_162_, 0);
v_nextMacroScope_165_ = lean_ctor_get(v___x_162_, 1);
v_ngen_166_ = lean_ctor_get(v___x_162_, 2);
v_auxDeclNGen_167_ = lean_ctor_get(v___x_162_, 3);
v_cache_168_ = lean_ctor_get(v___x_162_, 5);
v_recordedDeps_169_ = lean_ctor_get(v___x_162_, 6);
v_messages_170_ = lean_ctor_get(v___x_162_, 7);
v_infoState_171_ = lean_ctor_get(v___x_162_, 8);
v_snapshotTasks_172_ = lean_ctor_get(v___x_162_, 9);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_191_ == 0)
{
v___x_174_ = v___x_162_;
v_isShared_175_ = v_isSharedCheck_191_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_snapshotTasks_172_);
lean_inc(v_infoState_171_);
lean_inc(v_messages_170_);
lean_inc(v_recordedDeps_169_);
lean_inc(v_cache_168_);
lean_inc(v_traceState_163_);
lean_inc(v_auxDeclNGen_167_);
lean_inc(v_ngen_166_);
lean_inc(v_nextMacroScope_165_);
lean_inc(v_env_164_);
lean_dec(v___x_162_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_191_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint64_t v_tid_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_189_; 
v_tid_176_ = lean_ctor_get_uint64(v_traceState_163_, sizeof(void*)*1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_traceState_163_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v_traceState_163_, 0);
lean_dec(v_unused_190_);
v___x_178_ = v_traceState_163_;
v_isShared_179_ = v_isSharedCheck_189_;
goto v_resetjp_177_;
}
else
{
lean_dec(v_traceState_163_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_189_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_180_);
lean_ctor_set_uint64(v_reuseFailAlloc_188_, sizeof(void*)*1, v_tid_176_);
v___x_182_ = v_reuseFailAlloc_188_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_182_);
v___x_184_ = v___x_174_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_env_164_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_nextMacroScope_165_);
lean_ctor_set(v_reuseFailAlloc_187_, 2, v_ngen_166_);
lean_ctor_set(v_reuseFailAlloc_187_, 3, v_auxDeclNGen_167_);
lean_ctor_set(v_reuseFailAlloc_187_, 4, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_187_, 5, v_cache_168_);
lean_ctor_set(v_reuseFailAlloc_187_, 6, v_recordedDeps_169_);
lean_ctor_set(v_reuseFailAlloc_187_, 7, v_messages_170_);
lean_ctor_set(v_reuseFailAlloc_187_, 8, v_infoState_171_);
lean_ctor_set(v_reuseFailAlloc_187_, 9, v_snapshotTasks_172_);
v___x_184_ = v_reuseFailAlloc_187_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_st_ref_put(v___y_157_, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v_traces_161_);
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___boxed(lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_192_);
lean_dec(v___y_192_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v___y_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___boxed(lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0(v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(lean_object* v_opts_207_, lean_object* v_opt_208_){
_start:
{
lean_object* v_name_209_; lean_object* v_defValue_210_; lean_object* v_map_211_; lean_object* v___x_212_; 
v_name_209_ = lean_ctor_get(v_opt_208_, 0);
v_defValue_210_ = lean_ctor_get(v_opt_208_, 1);
v_map_211_ = lean_ctor_get(v_opts_207_, 0);
v___x_212_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_211_, v_name_209_);
if (lean_obj_tag(v___x_212_) == 0)
{
uint8_t v___x_213_; 
v___x_213_ = lean_unbox(v_defValue_210_);
return v___x_213_;
}
else
{
lean_object* v_val_214_; 
v_val_214_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v___x_212_, 1);
if (lean_obj_tag(v_val_214_) == 1)
{
uint8_t v_v_215_; 
v_v_215_ = lean_ctor_get_uint8(v_val_214_, 0);
lean_dec_ref_known(v_val_214_, 0);
return v_v_215_;
}
else
{
uint8_t v___x_216_; 
lean_dec(v_val_214_);
v___x_216_ = lean_unbox(v_defValue_210_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1___boxed(lean_object* v_opts_217_, lean_object* v_opt_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_217_, v_opt_218_);
lean_dec_ref(v_opt_218_);
lean_dec_ref(v_opts_217_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__1));
v___x_225_ = l_Lean_MessageData_ofFormat(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(lean_object* v_x_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___closed__2);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0___boxed(lean_object* v_x_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__0(v_x_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec_ref(v_x_234_);
return v_res_240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__1));
v___x_245_ = l_Lean_MessageData_ofFormat(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___closed__2);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1___boxed(lean_object* v_x_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__1(v_x_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_x_254_);
return v_res_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__1));
v___x_265_ = l_Lean_MessageData_ofFormat(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(lean_object* v_x_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___closed__2);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2___boxed(lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___lam__2(v_x_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec_ref(v_x_274_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v_x_281_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v_x_281_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 1);
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
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
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_a_291_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v_x_281_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v_x_281_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 0);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg___boxed(lean_object* v_x_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_299_);
return v_res_301_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(lean_object* v_e_302_){
_start:
{
if (lean_obj_tag(v_e_302_) == 0)
{
uint8_t v___x_303_; 
v___x_303_ = 2;
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8___boxed(lean_object* v_e_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_e_305_);
lean_dec_ref(v_e_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(size_t v_sz_308_, size_t v_i_309_, lean_object* v_bs_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_lt(v_i_309_, v_sz_308_);
if (v___x_311_ == 0)
{
return v_bs_310_;
}
else
{
lean_object* v_v_312_; lean_object* v_msg_313_; lean_object* v___x_314_; lean_object* v_bs_x27_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v___x_318_; 
v_v_312_ = lean_array_uget_borrowed(v_bs_310_, v_i_309_);
v_msg_313_ = lean_ctor_get(v_v_312_, 1);
lean_inc_ref(v_msg_313_);
v___x_314_ = lean_unsigned_to_nat(0u);
v_bs_x27_315_ = lean_array_uset(v_bs_310_, v_i_309_, v___x_314_);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_add(v_i_309_, v___x_316_);
v___x_318_ = lean_array_uset(v_bs_x27_315_, v_i_309_, v_msg_313_);
v_i_309_ = v___x_317_;
v_bs_310_ = v___x_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_320_, lean_object* v_i_321_, lean_object* v_bs_322_){
_start:
{
size_t v_sz_boxed_323_; size_t v_i_boxed_324_; lean_object* v_res_325_; 
v_sz_boxed_323_ = lean_unbox_usize(v_sz_320_);
lean_dec(v_sz_320_);
v_i_boxed_324_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_res_325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_boxed_323_, v_i_boxed_324_, v_bs_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___x_332_; lean_object* v_env_333_; uint8_t v___x_334_; lean_object* v_env_335_; lean_object* v___x_336_; lean_object* v_toCold_337_; lean_object* v_mctx_338_; lean_object* v_lctx_339_; lean_object* v_options_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_332_ = lean_st_ref_get(v___y_330_);
v_env_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc_ref(v_env_333_);
lean_dec(v___x_332_);
v___x_334_ = 0;
v_env_335_ = l_Lean_Environment_setRecordingDeps(v_env_333_, v___x_334_);
v___x_336_ = lean_st_ref_get(v___y_328_);
v_toCold_337_ = lean_ctor_get(v___y_329_, 0);
v_mctx_338_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_mctx_338_);
lean_dec(v___x_336_);
v_lctx_339_ = lean_ctor_get(v___y_327_, 2);
v_options_340_ = lean_ctor_get(v_toCold_337_, 2);
lean_inc_ref(v_options_340_);
lean_inc_ref(v_lctx_339_);
v___x_341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_341_, 0, v_env_335_);
lean_ctor_set(v___x_341_, 1, v_mctx_338_);
lean_ctor_set(v___x_341_, 2, v_lctx_339_);
lean_ctor_set(v___x_341_, 3, v_options_340_);
v___x_342_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_msgData_326_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6___boxed(lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msgData_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(lean_object* v_oldTraces_351_, lean_object* v_data_352_, lean_object* v_ref_353_, lean_object* v_msg_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_toCold_360_; lean_object* v_currRecDepth_361_; lean_object* v_ref_362_; uint16_t v_optionFlags_363_; uint8_t v_suppressElabErrors_364_; uint8_t v_isRecordingDeps_365_; lean_object* v_ref_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_traceState_369_; lean_object* v_traces_370_; lean_object* v___x_371_; size_t v_sz_372_; size_t v___x_373_; lean_object* v___x_374_; lean_object* v_msg_375_; lean_object* v___x_376_; lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_415_; 
v_toCold_360_ = lean_ctor_get(v___y_357_, 0);
v_currRecDepth_361_ = lean_ctor_get(v___y_357_, 1);
v_ref_362_ = lean_ctor_get(v___y_357_, 2);
v_optionFlags_363_ = lean_ctor_get_uint16(v___y_357_, sizeof(void*)*3);
v_suppressElabErrors_364_ = lean_ctor_get_uint8(v___y_357_, sizeof(void*)*3 + 2);
v_isRecordingDeps_365_ = lean_ctor_get_uint8(v___y_357_, sizeof(void*)*3 + 3);
v_ref_366_ = l_Lean_replaceRef(v_ref_353_, v_ref_362_);
lean_inc(v_currRecDepth_361_);
lean_inc_ref(v_toCold_360_);
v___x_367_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_367_, 0, v_toCold_360_);
lean_ctor_set(v___x_367_, 1, v_currRecDepth_361_);
lean_ctor_set(v___x_367_, 2, v_ref_366_);
lean_ctor_set_uint16(v___x_367_, sizeof(void*)*3, v_optionFlags_363_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*3 + 2, v_suppressElabErrors_364_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*3 + 3, v_isRecordingDeps_365_);
v___x_368_ = lean_st_ref_get(v___y_358_);
v_traceState_369_ = lean_ctor_get(v___x_368_, 4);
lean_inc_ref(v_traceState_369_);
lean_dec(v___x_368_);
v_traces_370_ = lean_ctor_get(v_traceState_369_, 0);
lean_inc_ref(v_traces_370_);
lean_dec_ref(v_traceState_369_);
v___x_371_ = l_Lean_PersistentArray_toArray___redArg(v_traces_370_);
lean_dec_ref(v_traces_370_);
v_sz_372_ = lean_array_size(v___x_371_);
v___x_373_ = ((size_t)0ULL);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_372_, v___x_373_, v___x_371_);
v_msg_375_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_375_, 0, v_data_352_);
lean_ctor_set(v_msg_375_, 1, v_msg_354_);
lean_ctor_set(v_msg_375_, 2, v___x_374_);
v___x_376_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_375_, v___y_355_, v___y_356_, v___x_367_, v___y_358_);
lean_dec_ref_known(v___x_367_, 3);
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_415_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_415_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_415_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v_traceState_382_; lean_object* v_env_383_; lean_object* v_nextMacroScope_384_; lean_object* v_ngen_385_; lean_object* v_auxDeclNGen_386_; lean_object* v_cache_387_; lean_object* v_recordedDeps_388_; lean_object* v_messages_389_; lean_object* v_infoState_390_; lean_object* v_snapshotTasks_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_414_; 
v___x_381_ = lean_st_ref_take(v___y_358_);
v_traceState_382_ = lean_ctor_get(v___x_381_, 4);
v_env_383_ = lean_ctor_get(v___x_381_, 0);
v_nextMacroScope_384_ = lean_ctor_get(v___x_381_, 1);
v_ngen_385_ = lean_ctor_get(v___x_381_, 2);
v_auxDeclNGen_386_ = lean_ctor_get(v___x_381_, 3);
v_cache_387_ = lean_ctor_get(v___x_381_, 5);
v_recordedDeps_388_ = lean_ctor_get(v___x_381_, 6);
v_messages_389_ = lean_ctor_get(v___x_381_, 7);
v_infoState_390_ = lean_ctor_get(v___x_381_, 8);
v_snapshotTasks_391_ = lean_ctor_get(v___x_381_, 9);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_414_ == 0)
{
v___x_393_ = v___x_381_;
v_isShared_394_ = v_isSharedCheck_414_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_snapshotTasks_391_);
lean_inc(v_infoState_390_);
lean_inc(v_messages_389_);
lean_inc(v_recordedDeps_388_);
lean_inc(v_cache_387_);
lean_inc(v_traceState_382_);
lean_inc(v_auxDeclNGen_386_);
lean_inc(v_ngen_385_);
lean_inc(v_nextMacroScope_384_);
lean_inc(v_env_383_);
lean_dec(v___x_381_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_414_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint64_t v_tid_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_412_; 
v_tid_395_ = lean_ctor_get_uint64(v_traceState_382_, sizeof(void*)*1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_traceState_382_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v_traceState_382_, 0);
lean_dec(v_unused_413_);
v___x_397_ = v_traceState_382_;
v_isShared_398_ = v_isSharedCheck_412_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_traceState_382_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_412_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_399_ = lean_box(0);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_ref_353_);
lean_ctor_set(v___x_400_, 1, v_a_377_);
v___x_401_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_351_, v___x_400_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_401_);
v___x_403_ = v___x_397_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_401_);
lean_ctor_set_uint64(v_reuseFailAlloc_411_, sizeof(void*)*1, v_tid_395_);
v___x_403_ = v_reuseFailAlloc_411_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_405_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 4, v___x_403_);
v___x_405_ = v___x_393_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_env_383_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_nextMacroScope_384_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_ngen_385_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_auxDeclNGen_386_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 5, v_cache_387_);
lean_ctor_set(v_reuseFailAlloc_410_, 6, v_recordedDeps_388_);
lean_ctor_set(v_reuseFailAlloc_410_, 7, v_messages_389_);
lean_ctor_set(v_reuseFailAlloc_410_, 8, v_infoState_390_);
lean_ctor_set(v_reuseFailAlloc_410_, 9, v_snapshotTasks_391_);
v___x_405_ = v_reuseFailAlloc_410_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_st_ref_put(v___y_358_, v___x_405_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_399_);
v___x_408_ = v___x_379_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_399_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2___boxed(lean_object* v_oldTraces_416_, lean_object* v_data_417_, lean_object* v_ref_418_, lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_416_, v_data_417_, v_ref_418_, v_msg_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0(void){
_start:
{
lean_object* v___x_426_; double v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_float_of_nat(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__1));
v___x_430_ = l_Lean_stringToMessageData(v___x_429_);
return v___x_430_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3(void){
_start:
{
lean_object* v___x_431_; double v___x_432_; 
v___x_431_ = lean_unsigned_to_nat(1000u);
v___x_432_ = lean_float_of_nat(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(lean_object* v_cls_433_, uint8_t v_collapsed_434_, lean_object* v_tag_435_, lean_object* v_opts_436_, uint8_t v_clsEnabled_437_, lean_object* v_oldTraces_438_, lean_object* v_msg_439_, lean_object* v_resStartStop_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v_data_451_; lean_object* v_fst_454_; lean_object* v_snd_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___y_459_; lean_object* v_a_460_; uint8_t v___y_475_; double v___y_507_; 
v_fst_446_ = lean_ctor_get(v_resStartStop_440_, 0);
lean_inc(v_fst_446_);
v_snd_447_ = lean_ctor_get(v_resStartStop_440_, 1);
lean_inc(v_snd_447_);
lean_dec_ref(v_resStartStop_440_);
v_fst_454_ = lean_ctor_get(v_snd_447_, 0);
lean_inc(v_fst_454_);
v_snd_455_ = lean_ctor_get(v_snd_447_, 1);
lean_inc(v_snd_455_);
lean_dec(v_snd_447_);
v___x_456_ = l_Lean_trace_profiler;
v___x_457_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_436_, v___x_456_);
if (v___x_457_ == 0)
{
v___y_475_ = v___x_457_;
goto v___jp_474_;
}
else
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = l_Lean_trace_profiler_useHeartbeats;
v___x_513_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_436_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; double v___x_516_; double v___x_517_; double v___x_518_; 
v___x_514_ = l_Lean_trace_profiler_threshold;
v___x_515_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_436_, v___x_514_);
v___x_516_ = lean_float_of_nat(v___x_515_);
v___x_517_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_518_ = lean_float_div(v___x_516_, v___x_517_);
v___y_507_ = v___x_518_;
goto v___jp_506_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; double v___x_521_; 
v___x_519_ = l_Lean_trace_profiler_threshold;
v___x_520_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_436_, v___x_519_);
v___x_521_ = lean_float_of_nat(v___x_520_);
v___y_507_ = v___x_521_;
goto v___jp_506_;
}
}
v___jp_448_:
{
lean_object* v___x_452_; 
lean_inc(v___y_449_);
v___x_452_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_438_, v_data_451_, v___y_449_, v___y_450_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_453_; 
lean_dec_ref_known(v___x_452_, 1);
v___x_453_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_446_);
return v___x_453_;
}
else
{
lean_dec(v_fst_446_);
return v___x_452_;
}
}
v___jp_458_:
{
uint8_t v_result_461_; lean_object* v___x_462_; lean_object* v___x_463_; double v___x_464_; lean_object* v_data_465_; 
v_result_461_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4_spec__8(v_fst_446_);
v___x_462_ = lean_box(v_result_461_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
v___x_464_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_435_);
lean_inc_ref(v___x_463_);
lean_inc(v_cls_433_);
v_data_465_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_465_, 0, v_cls_433_);
lean_ctor_set(v_data_465_, 1, v___x_463_);
lean_ctor_set(v_data_465_, 2, v_tag_435_);
lean_ctor_set_float(v_data_465_, sizeof(void*)*3, v___x_464_);
lean_ctor_set_float(v_data_465_, sizeof(void*)*3 + 8, v___x_464_);
lean_ctor_set_uint8(v_data_465_, sizeof(void*)*3 + 16, v_collapsed_434_);
if (v___x_457_ == 0)
{
lean_dec_ref_known(v___x_463_, 1);
lean_dec(v_snd_455_);
lean_dec(v_fst_454_);
lean_dec_ref(v_tag_435_);
lean_dec(v_cls_433_);
v___y_449_ = v___y_459_;
v___y_450_ = v_a_460_;
v_data_451_ = v_data_465_;
goto v___jp_448_;
}
else
{
lean_object* v_data_466_; double v___x_467_; double v___x_468_; 
lean_dec_ref_known(v_data_465_, 3);
v_data_466_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_466_, 0, v_cls_433_);
lean_ctor_set(v_data_466_, 1, v___x_463_);
lean_ctor_set(v_data_466_, 2, v_tag_435_);
v___x_467_ = lean_unbox_float(v_fst_454_);
lean_dec(v_fst_454_);
lean_ctor_set_float(v_data_466_, sizeof(void*)*3, v___x_467_);
v___x_468_ = lean_unbox_float(v_snd_455_);
lean_dec(v_snd_455_);
lean_ctor_set_float(v_data_466_, sizeof(void*)*3 + 8, v___x_468_);
lean_ctor_set_uint8(v_data_466_, sizeof(void*)*3 + 16, v_collapsed_434_);
v___y_449_ = v___y_459_;
v___y_450_ = v_a_460_;
v_data_451_ = v_data_466_;
goto v___jp_448_;
}
}
v___jp_469_:
{
lean_object* v_ref_470_; lean_object* v___x_471_; 
v_ref_470_ = lean_ctor_get(v___y_443_, 2);
lean_inc(v___y_444_);
lean_inc_ref(v___y_443_);
lean_inc(v___y_442_);
lean_inc_ref(v___y_441_);
lean_inc(v_fst_446_);
v___x_471_ = lean_apply_6(v_msg_439_, v_fst_446_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, lean_box(0));
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___y_459_ = v_ref_470_;
v_a_460_ = v_a_472_;
goto v___jp_458_;
}
else
{
lean_object* v___x_473_; 
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_459_ = v_ref_470_;
v_a_460_ = v___x_473_;
goto v___jp_458_;
}
}
v___jp_474_:
{
if (v_clsEnabled_437_ == 0)
{
if (v___y_475_ == 0)
{
lean_object* v___x_476_; lean_object* v_traceState_477_; lean_object* v_env_478_; lean_object* v_nextMacroScope_479_; lean_object* v_ngen_480_; lean_object* v_auxDeclNGen_481_; lean_object* v_cache_482_; lean_object* v_recordedDeps_483_; lean_object* v_messages_484_; lean_object* v_infoState_485_; lean_object* v_snapshotTasks_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_snd_455_);
lean_dec(v_fst_454_);
lean_dec_ref(v_msg_439_);
lean_dec_ref(v_tag_435_);
lean_dec(v_cls_433_);
v___x_476_ = lean_st_ref_take(v___y_444_);
v_traceState_477_ = lean_ctor_get(v___x_476_, 4);
v_env_478_ = lean_ctor_get(v___x_476_, 0);
v_nextMacroScope_479_ = lean_ctor_get(v___x_476_, 1);
v_ngen_480_ = lean_ctor_get(v___x_476_, 2);
v_auxDeclNGen_481_ = lean_ctor_get(v___x_476_, 3);
v_cache_482_ = lean_ctor_get(v___x_476_, 5);
v_recordedDeps_483_ = lean_ctor_get(v___x_476_, 6);
v_messages_484_ = lean_ctor_get(v___x_476_, 7);
v_infoState_485_ = lean_ctor_get(v___x_476_, 8);
v_snapshotTasks_486_ = lean_ctor_get(v___x_476_, 9);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_505_ == 0)
{
v___x_488_ = v___x_476_;
v_isShared_489_ = v_isSharedCheck_505_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snapshotTasks_486_);
lean_inc(v_infoState_485_);
lean_inc(v_messages_484_);
lean_inc(v_recordedDeps_483_);
lean_inc(v_cache_482_);
lean_inc(v_traceState_477_);
lean_inc(v_auxDeclNGen_481_);
lean_inc(v_ngen_480_);
lean_inc(v_nextMacroScope_479_);
lean_inc(v_env_478_);
lean_dec(v___x_476_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_505_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
uint64_t v_tid_490_; lean_object* v_traces_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_504_; 
v_tid_490_ = lean_ctor_get_uint64(v_traceState_477_, sizeof(void*)*1);
v_traces_491_ = lean_ctor_get(v_traceState_477_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_traceState_477_);
if (v_isSharedCheck_504_ == 0)
{
v___x_493_ = v_traceState_477_;
v_isShared_494_ = v_isSharedCheck_504_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_traces_491_);
lean_dec(v_traceState_477_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_504_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_438_, v_traces_491_);
lean_dec_ref(v_traces_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_495_);
lean_ctor_set_uint64(v_reuseFailAlloc_503_, sizeof(void*)*1, v_tid_490_);
v___x_497_ = v_reuseFailAlloc_503_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_499_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v___x_497_);
v___x_499_ = v___x_488_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_env_478_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_nextMacroScope_479_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_ngen_480_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_auxDeclNGen_481_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_502_, 5, v_cache_482_);
lean_ctor_set(v_reuseFailAlloc_502_, 6, v_recordedDeps_483_);
lean_ctor_set(v_reuseFailAlloc_502_, 7, v_messages_484_);
lean_ctor_set(v_reuseFailAlloc_502_, 8, v_infoState_485_);
lean_ctor_set(v_reuseFailAlloc_502_, 9, v_snapshotTasks_486_);
v___x_499_ = v_reuseFailAlloc_502_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_st_ref_put(v___y_444_, v___x_499_);
v___x_501_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_446_);
return v___x_501_;
}
}
}
}
}
else
{
goto v___jp_469_;
}
}
else
{
goto v___jp_469_;
}
}
v___jp_506_:
{
double v___x_508_; double v___x_509_; double v___x_510_; uint8_t v___x_511_; 
v___x_508_ = lean_unbox_float(v_snd_455_);
v___x_509_ = lean_unbox_float(v_fst_454_);
v___x_510_ = lean_float_sub(v___x_508_, v___x_509_);
v___x_511_ = lean_float_decLt(v___y_507_, v___x_510_);
v___y_475_ = v___x_511_;
goto v___jp_474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___boxed(lean_object* v_cls_522_, lean_object* v_collapsed_523_, lean_object* v_tag_524_, lean_object* v_opts_525_, lean_object* v_clsEnabled_526_, lean_object* v_oldTraces_527_, lean_object* v_msg_528_, lean_object* v_resStartStop_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
uint8_t v_collapsed_boxed_535_; uint8_t v_clsEnabled_boxed_536_; lean_object* v_res_537_; 
v_collapsed_boxed_535_ = lean_unbox(v_collapsed_523_);
v_clsEnabled_boxed_536_ = lean_unbox(v_clsEnabled_526_);
v_res_537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v_cls_522_, v_collapsed_boxed_535_, v_tag_524_, v_opts_525_, v_clsEnabled_boxed_536_, v_oldTraces_527_, v_msg_528_, v_resStartStop_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_opts_525_);
return v_res_537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(lean_object* v_e_538_){
_start:
{
if (lean_obj_tag(v_e_538_) == 0)
{
uint8_t v___x_539_; 
v___x_539_ = 2;
return v___x_539_;
}
else
{
lean_object* v_a_540_; uint8_t v___x_541_; 
v_a_540_ = lean_ctor_get(v_e_538_, 0);
v___x_541_ = l_Lean_Expr_hasSyntheticSorry(v_a_540_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = 0;
return v___x_542_;
}
else
{
uint8_t v___x_543_; 
v___x_543_ = 1;
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4___boxed(lean_object* v_e_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_e_544_);
lean_dec_ref(v_e_544_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(lean_object* v_cls_547_, uint8_t v_collapsed_548_, lean_object* v_tag_549_, lean_object* v_opts_550_, uint8_t v_clsEnabled_551_, lean_object* v_oldTraces_552_, lean_object* v_msg_553_, lean_object* v_resStartStop_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v_data_565_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___y_581_; lean_object* v_a_582_; uint8_t v___y_597_; double v___y_629_; 
v_fst_560_ = lean_ctor_get(v_resStartStop_554_, 0);
lean_inc(v_fst_560_);
v_snd_561_ = lean_ctor_get(v_resStartStop_554_, 1);
lean_inc(v_snd_561_);
lean_dec_ref(v_resStartStop_554_);
v_fst_576_ = lean_ctor_get(v_snd_561_, 0);
lean_inc(v_fst_576_);
v_snd_577_ = lean_ctor_get(v_snd_561_, 1);
lean_inc(v_snd_577_);
lean_dec(v_snd_561_);
v___x_578_ = l_Lean_trace_profiler;
v___x_579_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_550_, v___x_578_);
if (v___x_579_ == 0)
{
v___y_597_ = v___x_579_;
goto v___jp_596_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_trace_profiler_useHeartbeats;
v___x_635_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_550_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; double v___x_638_; double v___x_639_; double v___x_640_; 
v___x_636_ = l_Lean_trace_profiler_threshold;
v___x_637_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_550_, v___x_636_);
v___x_638_ = lean_float_of_nat(v___x_637_);
v___x_639_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_640_ = lean_float_div(v___x_638_, v___x_639_);
v___y_629_ = v___x_640_;
goto v___jp_628_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; double v___x_643_; 
v___x_641_ = l_Lean_trace_profiler_threshold;
v___x_642_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_550_, v___x_641_);
v___x_643_ = lean_float_of_nat(v___x_642_);
v___y_629_ = v___x_643_;
goto v___jp_628_;
}
}
v___jp_562_:
{
lean_object* v___x_566_; 
lean_inc(v___y_564_);
v___x_566_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2(v_oldTraces_552_, v_data_565_, v___y_564_, v___y_563_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_567_; 
lean_dec_ref_known(v___x_566_, 1);
v___x_567_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_560_);
return v___x_567_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v_fst_560_);
v_a_568_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_566_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_566_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_580_:
{
uint8_t v_result_583_; lean_object* v___x_584_; lean_object* v___x_585_; double v___x_586_; lean_object* v_data_587_; 
v_result_583_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__4(v_fst_560_);
v___x_584_ = lean_box(v_result_583_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
v___x_586_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_549_);
lean_inc_ref(v___x_585_);
lean_inc(v_cls_547_);
v_data_587_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_587_, 0, v_cls_547_);
lean_ctor_set(v_data_587_, 1, v___x_585_);
lean_ctor_set(v_data_587_, 2, v_tag_549_);
lean_ctor_set_float(v_data_587_, sizeof(void*)*3, v___x_586_);
lean_ctor_set_float(v_data_587_, sizeof(void*)*3 + 8, v___x_586_);
lean_ctor_set_uint8(v_data_587_, sizeof(void*)*3 + 16, v_collapsed_548_);
if (v___x_579_ == 0)
{
lean_dec_ref_known(v___x_585_, 1);
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_dec_ref(v_tag_549_);
lean_dec(v_cls_547_);
v___y_563_ = v_a_582_;
v___y_564_ = v___y_581_;
v_data_565_ = v_data_587_;
goto v___jp_562_;
}
else
{
lean_object* v_data_588_; double v___x_589_; double v___x_590_; 
lean_dec_ref_known(v_data_587_, 3);
v_data_588_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_588_, 0, v_cls_547_);
lean_ctor_set(v_data_588_, 1, v___x_585_);
lean_ctor_set(v_data_588_, 2, v_tag_549_);
v___x_589_ = lean_unbox_float(v_fst_576_);
lean_dec(v_fst_576_);
lean_ctor_set_float(v_data_588_, sizeof(void*)*3, v___x_589_);
v___x_590_ = lean_unbox_float(v_snd_577_);
lean_dec(v_snd_577_);
lean_ctor_set_float(v_data_588_, sizeof(void*)*3 + 8, v___x_590_);
lean_ctor_set_uint8(v_data_588_, sizeof(void*)*3 + 16, v_collapsed_548_);
v___y_563_ = v_a_582_;
v___y_564_ = v___y_581_;
v_data_565_ = v_data_588_;
goto v___jp_562_;
}
}
v___jp_591_:
{
lean_object* v_ref_592_; lean_object* v___x_593_; 
v_ref_592_ = lean_ctor_get(v___y_557_, 2);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v_fst_560_);
v___x_593_ = lean_apply_6(v_msg_553_, v_fst_560_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, lean_box(0));
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___y_581_ = v_ref_592_;
v_a_582_ = v_a_594_;
goto v___jp_580_;
}
else
{
lean_object* v___x_595_; 
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_581_ = v_ref_592_;
v_a_582_ = v___x_595_;
goto v___jp_580_;
}
}
v___jp_596_:
{
if (v_clsEnabled_551_ == 0)
{
if (v___y_597_ == 0)
{
lean_object* v___x_598_; lean_object* v_traceState_599_; lean_object* v_env_600_; lean_object* v_nextMacroScope_601_; lean_object* v_ngen_602_; lean_object* v_auxDeclNGen_603_; lean_object* v_cache_604_; lean_object* v_recordedDeps_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_dec_ref(v_msg_553_);
lean_dec_ref(v_tag_549_);
lean_dec(v_cls_547_);
v___x_598_ = lean_st_ref_take(v___y_558_);
v_traceState_599_ = lean_ctor_get(v___x_598_, 4);
v_env_600_ = lean_ctor_get(v___x_598_, 0);
v_nextMacroScope_601_ = lean_ctor_get(v___x_598_, 1);
v_ngen_602_ = lean_ctor_get(v___x_598_, 2);
v_auxDeclNGen_603_ = lean_ctor_get(v___x_598_, 3);
v_cache_604_ = lean_ctor_get(v___x_598_, 5);
v_recordedDeps_605_ = lean_ctor_get(v___x_598_, 6);
v_messages_606_ = lean_ctor_get(v___x_598_, 7);
v_infoState_607_ = lean_ctor_get(v___x_598_, 8);
v_snapshotTasks_608_ = lean_ctor_get(v___x_598_, 9);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_627_ == 0)
{
v___x_610_ = v___x_598_;
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_recordedDeps_605_);
lean_inc(v_cache_604_);
lean_inc(v_traceState_599_);
lean_inc(v_auxDeclNGen_603_);
lean_inc(v_ngen_602_);
lean_inc(v_nextMacroScope_601_);
lean_inc(v_env_600_);
lean_dec(v___x_598_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint64_t v_tid_612_; lean_object* v_traces_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_626_; 
v_tid_612_ = lean_ctor_get_uint64(v_traceState_599_, sizeof(void*)*1);
v_traces_613_ = lean_ctor_get(v_traceState_599_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_traceState_599_);
if (v_isSharedCheck_626_ == 0)
{
v___x_615_ = v_traceState_599_;
v_isShared_616_ = v_isSharedCheck_626_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_traces_613_);
lean_dec(v_traceState_599_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_626_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_552_, v_traces_613_);
lean_dec_ref(v_traces_613_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_617_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_617_);
lean_ctor_set_uint64(v_reuseFailAlloc_625_, sizeof(void*)*1, v_tid_612_);
v___x_619_ = v_reuseFailAlloc_625_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 4, v___x_619_);
v___x_621_ = v___x_610_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_env_600_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_nextMacroScope_601_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_ngen_602_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_auxDeclNGen_603_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_624_, 5, v_cache_604_);
lean_ctor_set(v_reuseFailAlloc_624_, 6, v_recordedDeps_605_);
lean_ctor_set(v_reuseFailAlloc_624_, 7, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_624_, 8, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_624_, 9, v_snapshotTasks_608_);
v___x_621_ = v_reuseFailAlloc_624_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_st_ref_put(v___y_558_, v___x_621_);
v___x_623_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_fst_560_);
return v___x_623_;
}
}
}
}
}
else
{
goto v___jp_591_;
}
}
else
{
goto v___jp_591_;
}
}
v___jp_628_:
{
double v___x_630_; double v___x_631_; double v___x_632_; uint8_t v___x_633_; 
v___x_630_ = lean_unbox_float(v_snd_577_);
v___x_631_ = lean_unbox_float(v_fst_576_);
v___x_632_ = lean_float_sub(v___x_630_, v___x_631_);
v___x_633_ = lean_float_decLt(v___y_629_, v___x_632_);
v___y_597_ = v___x_633_;
goto v___jp_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2___boxed(lean_object* v_cls_644_, lean_object* v_collapsed_645_, lean_object* v_tag_646_, lean_object* v_opts_647_, lean_object* v_clsEnabled_648_, lean_object* v_oldTraces_649_, lean_object* v_msg_650_, lean_object* v_resStartStop_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_collapsed_boxed_657_; uint8_t v_clsEnabled_boxed_658_; lean_object* v_res_659_; 
v_collapsed_boxed_657_ = lean_unbox(v_collapsed_645_);
v_clsEnabled_boxed_658_ = lean_unbox(v_clsEnabled_648_);
v_res_659_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v_cls_644_, v_collapsed_boxed_657_, v_tag_646_, v_opts_647_, v_clsEnabled_boxed_658_, v_oldTraces_649_, v_msg_650_, v_resStartStop_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v_opts_647_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(lean_object* v_msg_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_ref_666_; lean_object* v___x_667_; lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
v_ref_666_ = lean_ctor_get(v___y_663_, 2);
v___x_667_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_676_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
lean_inc(v_ref_666_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_ref_666_);
lean_ctor_set(v___x_672_, 1, v_a_668_);
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 1);
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg___boxed(lean_object* v_msg_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
return v_res_683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_box(0);
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__9));
v___x_703_ = l_Lean_mkConst(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static double _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12(void){
_start:
{
lean_object* v___x_705_; double v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1000000000u);
v___x_706_ = lean_float_of_nat(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__16));
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__20));
v___x_724_ = l_Lean_mkConst(v___x_723_, v___x_722_);
return v___x_724_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_box(0);
v___x_732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__22));
v___x_733_ = l_Lean_mkConst(v___x_732_, v___x_731_);
return v___x_733_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_735_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_736_ = l_Lean_Name_append(v___x_735_, v___x_734_);
return v___x_736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_box(0);
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__26));
v___x_742_ = l_Lean_mkConst(v___x_741_, v___x_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(lean_object* v_cert_744_, lean_object* v_ctx_745_, lean_object* v_reflectionResult_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_satExpr_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_1127_; 
v_satExpr_752_ = lean_ctor_get(v_reflectionResult_746_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_reflectionResult_746_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_reflectionResult_746_, 1);
lean_dec(v_unused_1128_);
v___x_754_ = v_reflectionResult_746_;
v_isShared_755_ = v_isSharedCheck_1127_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_satExpr_752_);
lean_dec(v_reflectionResult_746_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_1127_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_toCold_756_; lean_object* v_options_757_; lean_object* v_exprDef_758_; lean_object* v_certDef_759_; lean_object* v_expr_760_; lean_object* v_ref_761_; lean_object* v_inheritedTraceOptions_762_; uint8_t v_hasTrace_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___y_775_; lean_object* v___y_776_; uint8_t v___y_777_; lean_object* v___y_778_; lean_object* v_a_779_; lean_object* v___y_794_; lean_object* v___y_795_; uint8_t v___y_796_; lean_object* v___y_797_; lean_object* v_a_798_; lean_object* v___y_801_; lean_object* v___y_802_; uint8_t v___y_803_; lean_object* v___y_804_; lean_object* v_a_805_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; uint8_t v___y_811_; lean_object* v_a_812_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; uint8_t v___y_825_; lean_object* v_a_826_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; uint8_t v___y_832_; lean_object* v_a_833_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; uint8_t v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_888_; uint8_t v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v_a_963_; uint8_t v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v_a_980_; uint8_t v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_1035_; 
v_toCold_756_ = lean_ctor_get(v_a_749_, 0);
v_options_757_ = lean_ctor_get(v_toCold_756_, 2);
v_exprDef_758_ = lean_ctor_get(v_ctx_745_, 0);
lean_inc(v_exprDef_758_);
v_certDef_759_ = lean_ctor_get(v_ctx_745_, 1);
lean_inc(v_certDef_759_);
lean_dec_ref(v_ctx_745_);
v_expr_760_ = lean_ctor_get(v_satExpr_752_, 2);
lean_inc_ref(v_expr_760_);
lean_dec_ref(v_satExpr_752_);
v_ref_761_ = lean_ctor_get(v_a_749_, 2);
v_inheritedTraceOptions_762_ = lean_ctor_get(v_toCold_756_, 11);
v_hasTrace_763_ = lean_ctor_get_uint8(v_options_757_, sizeof(void*)*1);
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v___x_765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___f_766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__4));
v___f_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__5));
v___x_768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__6));
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__7));
v___x_770_ = lean_box(0);
v___x_771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__10);
v___x_772_ = 1;
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_763_ == 0)
{
lean_object* v___x_1052_; 
lean_inc(v_exprDef_758_);
v___x_1052_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_758_, v_expr_760_, v___x_771_, v_a_749_, v_a_750_);
v___y_1035_ = v___x_1052_;
goto v___jp_1034_;
}
else
{
lean_object* v___f_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v_a_1059_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v_a_1074_; 
v___f_1053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__28));
v___x_1054_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_762_, v_options_757_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = l_Lean_trace_profiler;
v___x_1125_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_757_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_inc(v_exprDef_758_);
v___x_1126_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_758_, v_expr_760_, v___x_771_, v_a_749_, v_a_750_);
v___y_1035_ = v___x_1126_;
goto v___jp_1034_;
}
else
{
goto v___jp_1083_;
}
}
else
{
goto v___jp_1083_;
}
v___jp_1056_:
{
lean_object* v___x_1060_; double v___x_1061_; double v___x_1062_; double v___x_1063_; double v___x_1064_; double v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1060_ = lean_io_mono_nanos_now();
v___x_1061_ = lean_float_of_nat(v___y_1057_);
v___x_1062_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1063_ = lean_float_div(v___x_1061_, v___x_1062_);
v___x_1064_ = lean_float_of_nat(v___x_1060_);
v___x_1065_ = lean_float_div(v___x_1064_, v___x_1062_);
v___x_1066_ = lean_box_float(v___x_1063_);
v___x_1067_ = lean_box_float(v___x_1065_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_a_1059_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_765_, v___x_772_, v___x_773_, v_options_757_, v___x_1055_, v___y_1058_, v___f_1053_, v___x_1069_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
v___y_1035_ = v___x_1070_;
goto v___jp_1034_;
}
v___jp_1071_:
{
lean_object* v___x_1075_; double v___x_1076_; double v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1075_ = lean_io_get_num_heartbeats();
v___x_1076_ = lean_float_of_nat(v___y_1072_);
v___x_1077_ = lean_float_of_nat(v___x_1075_);
v___x_1078_ = lean_box_float(v___x_1076_);
v___x_1079_ = lean_box_float(v___x_1077_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_a_1074_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_765_, v___x_772_, v___x_773_, v_options_757_, v___x_1055_, v___y_1073_, v___f_1053_, v___x_1081_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
v___y_1035_ = v___x_1082_;
goto v___jp_1034_;
}
v___jp_1083_:
{
lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1084_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_750_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1087_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_757_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_io_mono_nanos_now();
lean_inc(v_exprDef_758_);
v___x_1089_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_758_, v_expr_760_, v___x_771_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 1);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v___y_1057_ = v___x_1088_;
v___y_1058_ = v_a_1085_;
v_a_1059_ = v___x_1095_;
goto v___jp_1056_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1089_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1089_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set_tag(v___x_1100_, 0);
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
v___y_1057_ = v___x_1088_;
v___y_1058_ = v_a_1085_;
v_a_1059_ = v___x_1103_;
goto v___jp_1056_;
}
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_io_get_num_heartbeats();
lean_inc(v_exprDef_758_);
v___x_1107_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_exprDef_758_, v_expr_760_, v___x_771_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 1);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v___y_1072_ = v___x_1106_;
v___y_1073_ = v_a_1085_;
v_a_1074_ = v___x_1113_;
goto v___jp_1071_;
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1107_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1107_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 0);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v___y_1072_ = v___x_1106_;
v___y_1073_ = v_a_1085_;
v_a_1074_ = v___x_1121_;
goto v___jp_1071_;
}
}
}
}
}
}
v___jp_774_:
{
lean_object* v___x_780_; double v___x_781_; double v___x_782_; double v___x_783_; double v___x_784_; double v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_780_ = lean_io_mono_nanos_now();
v___x_781_ = lean_float_of_nat(v___y_778_);
v___x_782_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_783_ = lean_float_div(v___x_781_, v___x_782_);
v___x_784_ = lean_float_of_nat(v___x_780_);
v___x_785_ = lean_float_div(v___x_784_, v___x_782_);
v___x_786_ = lean_box_float(v___x_783_);
v___x_787_ = lean_box_float(v___x_785_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_787_);
lean_ctor_set(v___x_754_, 0, v___x_786_);
v___x_789_ = v___x_754_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_792_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_a_779_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_765_, v___x_772_, v___x_773_, v___y_776_, v___y_777_, v___y_775_, v___f_767_, v___x_790_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_791_;
}
}
v___jp_793_:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_a_798_);
v___y_775_ = v___y_795_;
v___y_776_ = v___y_794_;
v___y_777_ = v___y_796_;
v___y_778_ = v___y_797_;
v_a_779_ = v___x_799_;
goto v___jp_774_;
}
v___jp_800_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_a_805_);
v___y_775_ = v___y_802_;
v___y_776_ = v___y_801_;
v___y_777_ = v___y_803_;
v___y_778_ = v___y_804_;
v_a_779_ = v___x_806_;
goto v___jp_774_;
}
v___jp_807_:
{
lean_object* v___x_813_; double v___x_814_; double v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_813_ = lean_io_get_num_heartbeats();
v___x_814_ = lean_float_of_nat(v___y_810_);
v___x_815_ = lean_float_of_nat(v___x_813_);
v___x_816_ = lean_box_float(v___x_814_);
v___x_817_ = lean_box_float(v___x_815_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_a_812_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2(v___x_765_, v___x_772_, v___x_773_, v___y_809_, v___y_811_, v___y_808_, v___f_767_, v___x_819_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_820_;
}
v___jp_821_:
{
lean_object* v___x_827_; 
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v_a_826_);
v___y_808_ = v___y_824_;
v___y_809_ = v___y_823_;
v___y_810_ = v___y_822_;
v___y_811_ = v___y_825_;
v_a_812_ = v___x_827_;
goto v___jp_807_;
}
v___jp_828_:
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_a_833_);
v___y_808_ = v___y_831_;
v___y_809_ = v___y_830_;
v___y_810_ = v___y_829_;
v___y_811_ = v___y_832_;
v_a_812_ = v___x_834_;
goto v___jp_807_;
}
v___jp_835_:
{
lean_object* v___x_843_; lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_886_; 
v___x_843_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_750_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_886_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_886_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_886_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = l_Lean_trace_profiler_useHeartbeats;
v___x_849_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_836_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = lean_io_mono_nanos_now();
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_842_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 1);
lean_ctor_set(v___x_846_, 0, v___y_842_);
v___x_853_ = v___x_846_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___y_842_);
v___x_853_ = v_reuseFailAlloc_867_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
lean_inc_ref(v___y_841_);
v___x_854_ = l_Lean_Meta_nativeEqTrue(v___x_851_, v___y_841_, v___x_853_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec_ref(v___x_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
if (lean_obj_tag(v_a_855_) == 0)
{
lean_object* v_prf_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec_ref(v___y_841_);
v_prf_856_ = lean_ctor_get(v_a_855_, 0);
lean_inc_ref(v_prf_856_);
lean_dec_ref_known(v_a_855_, 1);
v___x_857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_837_);
v___x_858_ = l_Lean_Name_mkStr5(v___x_768_, v___x_764_, v___x_769_, v___y_837_, v___x_857_);
v___x_859_ = l_Lean_mkConst(v___x_858_, v___x_770_);
v___x_860_ = l_Lean_mkApp3(v___x_859_, v___y_838_, v___y_840_, v_prf_856_);
v___y_801_ = v___y_836_;
v___y_802_ = v_a_844_;
v___y_803_ = v___y_839_;
v___y_804_ = v___x_850_;
v_a_805_ = v___x_860_;
goto v___jp_800_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_a_865_; 
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_838_);
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_862_ = l_Lean_indentExpr(v___y_841_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_863_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
v___y_794_ = v___y_836_;
v___y_795_ = v_a_844_;
v___y_796_ = v___y_839_;
v___y_797_ = v___x_850_;
v_a_798_ = v_a_865_;
goto v___jp_793_;
}
}
else
{
lean_object* v_a_866_; 
lean_dec_ref(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_838_);
v_a_866_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_854_, 1);
v___y_794_ = v___y_836_;
v___y_795_ = v_a_844_;
v___y_796_ = v___y_839_;
v___y_797_ = v___x_850_;
v_a_798_ = v_a_866_;
goto v___jp_793_;
}
}
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_del_object(v___x_754_);
v___x_868_ = lean_io_get_num_heartbeats();
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v___y_842_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 1);
lean_ctor_set(v___x_846_, 0, v___y_842_);
v___x_871_ = v___x_846_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___y_842_);
v___x_871_ = v_reuseFailAlloc_885_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; 
lean_inc_ref(v___y_841_);
v___x_872_ = l_Lean_Meta_nativeEqTrue(v___x_869_, v___y_841_, v___x_871_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec_ref(v___x_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
if (lean_obj_tag(v_a_873_) == 0)
{
lean_object* v_prf_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec_ref(v___y_841_);
v_prf_874_ = lean_ctor_get(v_a_873_, 0);
lean_inc_ref(v_prf_874_);
lean_dec_ref_known(v_a_873_, 1);
v___x_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__15));
lean_inc_ref(v___y_837_);
v___x_876_ = l_Lean_Name_mkStr5(v___x_768_, v___x_764_, v___x_769_, v___y_837_, v___x_875_);
v___x_877_ = l_Lean_mkConst(v___x_876_, v___x_770_);
v___x_878_ = l_Lean_mkApp3(v___x_877_, v___y_838_, v___y_840_, v_prf_874_);
v___y_829_ = v___x_868_;
v___y_830_ = v___y_836_;
v___y_831_ = v_a_844_;
v___y_832_ = v___y_839_;
v_a_833_ = v___x_878_;
goto v___jp_828_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_a_883_; 
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_838_);
v___x_879_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_880_ = l_Lean_indentExpr(v___y_841_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_881_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
v___y_822_ = v___x_868_;
v___y_823_ = v___y_836_;
v___y_824_ = v_a_844_;
v___y_825_ = v___y_839_;
v_a_826_ = v_a_883_;
goto v___jp_821_;
}
}
else
{
lean_object* v_a_884_; 
lean_dec_ref(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v___y_838_);
v_a_884_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_872_, 1);
v___y_822_ = v___x_868_;
v___y_823_ = v___y_836_;
v___y_824_ = v_a_844_;
v___y_825_ = v___y_839_;
v_a_826_ = v_a_884_;
goto v___jp_821_;
}
}
}
}
}
v___jp_887_:
{
if (lean_obj_tag(v___y_888_) == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref_known(v___y_888_, 1);
v___x_889_ = l_Lean_mkConst(v_exprDef_758_, v___x_770_);
v___x_890_ = l_Lean_mkConst(v_certDef_759_, v___x_770_);
v___x_891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__18));
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__21);
lean_inc_ref(v___x_890_);
lean_inc_ref(v___x_889_);
v___x_893_ = l_Lean_mkAppB(v___x_892_, v___x_889_, v___x_890_);
if (v_hasTrace_763_ == 0)
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_del_object(v___x_754_);
v___x_894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_761_);
v___x_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_895_, 0, v_ref_761_);
lean_inc_ref(v___x_893_);
v___x_896_ = l_Lean_Meta_nativeEqTrue(v___x_894_, v___x_893_, v___x_895_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec_ref_known(v___x_895_, 1);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_911_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_911_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_911_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_911_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
if (lean_obj_tag(v_a_897_) == 0)
{
lean_object* v_prf_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
lean_dec_ref(v___x_893_);
v_prf_901_ = lean_ctor_get(v_a_897_, 0);
lean_inc_ref(v_prf_901_);
lean_dec_ref_known(v_a_897_, 1);
v___x_902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_903_ = l_Lean_mkApp3(v___x_902_, v___x_889_, v___x_890_, v_prf_901_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_903_);
v___x_905_ = v___x_899_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_del_object(v___x_899_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v___x_889_);
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_908_ = l_Lean_indentExpr(v___x_893_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_909_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_910_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v___x_889_);
v_a_912_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_896_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_896_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_921_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_762_, v_options_757_, v___x_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = l_Lean_trace_profiler;
v___x_923_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_757_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_del_object(v___x_754_);
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__14));
lean_inc(v_ref_761_);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_ref_761_);
lean_inc_ref(v___x_893_);
v___x_926_ = l_Lean_Meta_nativeEqTrue(v___x_924_, v___x_893_, v___x_925_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec_ref_known(v___x_925_, 1);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_941_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_941_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_941_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_941_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
if (lean_obj_tag(v_a_927_) == 0)
{
lean_object* v_prf_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
lean_dec_ref(v___x_893_);
v_prf_931_ = lean_ctor_get(v_a_927_, 0);
lean_inc_ref(v_prf_931_);
lean_dec_ref_known(v_a_927_, 1);
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__23);
v___x_933_ = l_Lean_mkApp3(v___x_932_, v___x_889_, v___x_890_, v_prf_931_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_933_);
v___x_935_ = v___x_929_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_del_object(v___x_929_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v___x_889_);
v___x_937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__17);
v___x_938_ = l_Lean_indentExpr(v___x_893_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v___x_939_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_940_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v___x_889_);
v_a_942_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_926_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_926_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
v___y_836_ = v_options_757_;
v___y_837_ = v___x_891_;
v___y_838_ = v___x_889_;
v___y_839_ = v___x_921_;
v___y_840_ = v___x_890_;
v___y_841_ = v___x_893_;
v___y_842_ = v_ref_761_;
goto v___jp_835_;
}
}
else
{
v___y_836_ = v_options_757_;
v___y_837_ = v___x_891_;
v___y_838_ = v___x_889_;
v___y_839_ = v___x_921_;
v___y_840_ = v___x_890_;
v___y_841_ = v___x_893_;
v___y_842_ = v_ref_761_;
goto v___jp_835_;
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v_certDef_759_);
lean_dec(v_exprDef_758_);
lean_del_object(v___x_754_);
v_a_950_ = lean_ctor_get(v___y_888_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___y_888_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___y_888_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___y_888_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
v___jp_958_:
{
lean_object* v___x_964_; double v___x_965_; double v___x_966_; double v___x_967_; double v___x_968_; double v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_964_ = lean_io_mono_nanos_now();
v___x_965_ = lean_float_of_nat(v___y_962_);
v___x_966_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_967_ = lean_float_div(v___x_965_, v___x_966_);
v___x_968_ = lean_float_of_nat(v___x_964_);
v___x_969_ = lean_float_div(v___x_968_, v___x_966_);
v___x_970_ = lean_box_float(v___x_967_);
v___x_971_ = lean_box_float(v___x_969_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_a_963_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_765_, v___x_772_, v___x_773_, v___y_961_, v___y_959_, v___y_960_, v___f_766_, v___x_973_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
v___y_888_ = v___x_974_;
goto v___jp_887_;
}
v___jp_975_:
{
lean_object* v___x_981_; double v___x_982_; double v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_981_ = lean_io_get_num_heartbeats();
v___x_982_ = lean_float_of_nat(v___y_977_);
v___x_983_ = lean_float_of_nat(v___x_981_);
v___x_984_ = lean_box_float(v___x_982_);
v___x_985_ = lean_box_float(v___x_983_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_a_980_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4(v___x_765_, v___x_772_, v___x_773_, v___y_979_, v___y_976_, v___y_978_, v___f_766_, v___x_987_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
v___y_888_ = v___x_988_;
goto v___jp_887_;
}
v___jp_989_:
{
lean_object* v___x_994_; lean_object* v_a_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_994_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg(v_a_750_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref(v___x_994_);
v___x_996_ = l_Lean_trace_profiler_useHeartbeats;
v___x_997_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_993_, v___x_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_io_mono_nanos_now();
lean_inc(v_certDef_759_);
v___x_999_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_759_, v___y_991_, v___y_992_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 1);
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
v___y_959_ = v___y_990_;
v___y_960_ = v_a_995_;
v___y_961_ = v___y_993_;
v___y_962_ = v___x_998_;
v_a_963_ = v___x_1005_;
goto v___jp_958_;
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_a_1008_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_999_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set_tag(v___x_1010_, 0);
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
v___y_959_ = v___y_990_;
v___y_960_ = v_a_995_;
v___y_961_ = v___y_993_;
v___y_962_ = v___x_998_;
v_a_963_ = v___x_1013_;
goto v___jp_958_;
}
}
}
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_io_get_num_heartbeats();
lean_inc(v_certDef_759_);
v___x_1017_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_759_, v___y_991_, v___y_992_, v_a_749_, v_a_750_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 1);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v___y_976_ = v___y_990_;
v___y_977_ = v___x_1016_;
v___y_978_ = v_a_995_;
v___y_979_ = v___y_993_;
v_a_980_ = v___x_1023_;
goto v___jp_975_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1017_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1017_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 0);
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
v___y_976_ = v___y_990_;
v___y_977_ = v___x_1016_;
v___y_978_ = v_a_995_;
v___y_979_ = v___y_993_;
v_a_980_ = v___x_1031_;
goto v___jp_975_;
}
}
}
}
}
v___jp_1034_:
{
if (lean_obj_tag(v___y_1035_) == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref_known(v___y_1035_, 1);
v___x_1036_ = l_Lean_mkStrLit(v_cert_744_);
v___x_1037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__27);
if (v_hasTrace_763_ == 0)
{
lean_object* v___x_1038_; 
lean_inc(v_certDef_759_);
v___x_1038_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_759_, v___x_1036_, v___x_1037_, v_a_749_, v_a_750_);
v___y_888_ = v___x_1038_;
goto v___jp_887_;
}
else
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_1040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_762_, v_options_757_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1041_ = l_Lean_trace_profiler;
v___x_1042_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_757_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_inc(v_certDef_759_);
v___x_1043_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl(v_certDef_759_, v___x_1036_, v___x_1037_, v_a_749_, v_a_750_);
v___y_888_ = v___x_1043_;
goto v___jp_887_;
}
else
{
v___y_990_ = v___x_1040_;
v___y_991_ = v___x_1036_;
v___y_992_ = v___x_1037_;
v___y_993_ = v_options_757_;
goto v___jp_989_;
}
}
else
{
v___y_990_ = v___x_1040_;
v___y_991_ = v___x_1036_;
v___y_992_ = v___x_1037_;
v___y_993_ = v_options_757_;
goto v___jp_989_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v_certDef_759_);
lean_dec(v_exprDef_758_);
lean_del_object(v___x_754_);
lean_dec_ref(v_cert_744_);
v_a_1044_ = lean_ctor_get(v___y_1035_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___y_1035_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___y_1035_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___y_1035_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___boxed(lean_object* v_cert_1129_, lean_object* v_ctx_1130_, lean_object* v_reflectionResult_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_1129_, v_ctx_1130_, v_reflectionResult_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(lean_object* v_00_u03b1_1138_, lean_object* v_x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___redArg(v_x_1139_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1146_, lean_object* v_x_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__3(v_00_u03b1_1146_, v_x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(lean_object* v_00_u03b1_1154_, lean_object* v_msg_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___redArg(v_msg_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3___boxed(lean_object* v_00_u03b1_1162_, lean_object* v_msg_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3(v_00_u03b1_1162_, v_msg_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; lean_object* v_traceState_1173_; lean_object* v_traces_1174_; lean_object* v___x_1175_; lean_object* v_traceState_1176_; lean_object* v_env_1177_; lean_object* v_nextMacroScope_1178_; lean_object* v_ngen_1179_; lean_object* v_auxDeclNGen_1180_; lean_object* v_cache_1181_; lean_object* v_recordedDeps_1182_; lean_object* v_messages_1183_; lean_object* v_infoState_1184_; lean_object* v_snapshotTasks_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1206_; 
v___x_1172_ = lean_st_ref_get(v___y_1170_);
v_traceState_1173_ = lean_ctor_get(v___x_1172_, 4);
lean_inc_ref(v_traceState_1173_);
lean_dec(v___x_1172_);
v_traces_1174_ = lean_ctor_get(v_traceState_1173_, 0);
lean_inc_ref(v_traces_1174_);
lean_dec_ref(v_traceState_1173_);
v___x_1175_ = lean_st_ref_take(v___y_1170_);
v_traceState_1176_ = lean_ctor_get(v___x_1175_, 4);
v_env_1177_ = lean_ctor_get(v___x_1175_, 0);
v_nextMacroScope_1178_ = lean_ctor_get(v___x_1175_, 1);
v_ngen_1179_ = lean_ctor_get(v___x_1175_, 2);
v_auxDeclNGen_1180_ = lean_ctor_get(v___x_1175_, 3);
v_cache_1181_ = lean_ctor_get(v___x_1175_, 5);
v_recordedDeps_1182_ = lean_ctor_get(v___x_1175_, 6);
v_messages_1183_ = lean_ctor_get(v___x_1175_, 7);
v_infoState_1184_ = lean_ctor_get(v___x_1175_, 8);
v_snapshotTasks_1185_ = lean_ctor_get(v___x_1175_, 9);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1187_ = v___x_1175_;
v_isShared_1188_ = v_isSharedCheck_1206_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_snapshotTasks_1185_);
lean_inc(v_infoState_1184_);
lean_inc(v_messages_1183_);
lean_inc(v_recordedDeps_1182_);
lean_inc(v_cache_1181_);
lean_inc(v_traceState_1176_);
lean_inc(v_auxDeclNGen_1180_);
lean_inc(v_ngen_1179_);
lean_inc(v_nextMacroScope_1178_);
lean_inc(v_env_1177_);
lean_dec(v___x_1175_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1206_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
uint64_t v_tid_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1204_; 
v_tid_1189_ = lean_ctor_get_uint64(v_traceState_1176_, sizeof(void*)*1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_traceState_1176_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v_traceState_1176_, 0);
lean_dec(v_unused_1205_);
v___x_1191_ = v_traceState_1176_;
v_isShared_1192_ = v_isSharedCheck_1204_;
goto v_resetjp_1190_;
}
else
{
lean_dec(v_traceState_1176_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1204_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1193_ = lean_unsigned_to_nat(32u);
v___x_1194_ = lean_mk_empty_array_with_capacity(v___x_1193_);
lean_dec_ref(v___x_1194_);
v___x_1195_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1195_);
v___x_1197_ = v___x_1191_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1195_);
lean_ctor_set_uint64(v_reuseFailAlloc_1203_, sizeof(void*)*1, v_tid_1189_);
v___x_1197_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 4, v___x_1197_);
v___x_1199_ = v___x_1187_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_env_1177_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_nextMacroScope_1178_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_ngen_1179_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_auxDeclNGen_1180_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1202_, 5, v_cache_1181_);
lean_ctor_set(v_reuseFailAlloc_1202_, 6, v_recordedDeps_1182_);
lean_ctor_set(v_reuseFailAlloc_1202_, 7, v_messages_1183_);
lean_ctor_set(v_reuseFailAlloc_1202_, 8, v_infoState_1184_);
lean_ctor_set(v_reuseFailAlloc_1202_, 9, v_snapshotTasks_1185_);
v___x_1199_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_st_ref_put(v___y_1170_, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_traces_1174_);
return v___x_1201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg___boxed(lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1207_);
lean_dec(v___y_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___boxed(lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4(v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
return v_res_1237_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__1));
v___x_1242_ = l_Lean_MessageData_ofFormat(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(lean_object* v_x_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___closed__2);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0___boxed(lean_object* v_x_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__0(v_x_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v_x_1259_);
return v_res_1273_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__1));
v___x_1278_ = l_Lean_MessageData_ofFormat(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(lean_object* v_x_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___closed__2);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1___boxed(lean_object* v_x_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__1(v_x_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v_x_1295_);
return v_res_1309_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__1));
v___x_1314_ = l_Lean_MessageData_ofFormat(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(lean_object* v_x_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___closed__2);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2___boxed(lean_object* v_x_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__2(v_x_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v_x_1331_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3(lean_object* v_bvExpr_1346_, lean_object* v_x_1347_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bvExpr_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(lean_object* v___f_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_ref_1362_; lean_object* v___x_1363_; 
v_ref_1362_ = lean_ctor_get(v___y_1359_, 2);
v___x_1363_ = l_IO_lazyPure___redArg(v___f_1349_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1383_; 
v_a_1372_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1374_ = v___x_1363_;
v_isShared_1375_ = v_isSharedCheck_1383_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1363_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1383_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1376_ = lean_io_error_to_string(v_a_1372_);
v___x_1377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
v___x_1378_ = l_Lean_MessageData_ofFormat(v___x_1377_);
lean_inc(v_ref_1362_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_ref_1362_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1379_);
v___x_1381_ = v___x_1374_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed(lean_object* v___f_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_a_1400_ = lean_ctor_get(v_x_1398_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_x_1398_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v_x_1398_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v_x_1398_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 1);
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v_x_1398_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_x_1398_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v_x_1398_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v_x_1398_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 0);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg___boxed(lean_object* v_x_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(lean_object* v_e_1419_){
_start:
{
if (lean_obj_tag(v_e_1419_) == 0)
{
uint8_t v___x_1420_; 
v___x_1420_ = 2;
return v___x_1420_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = 0;
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19___boxed(lean_object* v_e_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_e_1422_);
lean_dec_ref(v_e_1422_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(lean_object* v_oldTraces_1425_, lean_object* v_data_1426_, lean_object* v_ref_1427_, lean_object* v_msg_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_toCold_1434_; lean_object* v_currRecDepth_1435_; lean_object* v_ref_1436_; uint16_t v_optionFlags_1437_; uint8_t v_suppressElabErrors_1438_; uint8_t v_isRecordingDeps_1439_; lean_object* v_ref_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_traceState_1443_; lean_object* v_traces_1444_; lean_object* v___x_1445_; size_t v_sz_1446_; size_t v___x_1447_; lean_object* v___x_1448_; lean_object* v_msg_1449_; lean_object* v___x_1450_; lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1489_; 
v_toCold_1434_ = lean_ctor_get(v___y_1431_, 0);
v_currRecDepth_1435_ = lean_ctor_get(v___y_1431_, 1);
v_ref_1436_ = lean_ctor_get(v___y_1431_, 2);
v_optionFlags_1437_ = lean_ctor_get_uint16(v___y_1431_, sizeof(void*)*3);
v_suppressElabErrors_1438_ = lean_ctor_get_uint8(v___y_1431_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1439_ = lean_ctor_get_uint8(v___y_1431_, sizeof(void*)*3 + 3);
v_ref_1440_ = l_Lean_replaceRef(v_ref_1427_, v_ref_1436_);
lean_inc(v_currRecDepth_1435_);
lean_inc_ref(v_toCold_1434_);
v___x_1441_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1441_, 0, v_toCold_1434_);
lean_ctor_set(v___x_1441_, 1, v_currRecDepth_1435_);
lean_ctor_set(v___x_1441_, 2, v_ref_1440_);
lean_ctor_set_uint16(v___x_1441_, sizeof(void*)*3, v_optionFlags_1437_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 2, v_suppressElabErrors_1438_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3 + 3, v_isRecordingDeps_1439_);
v___x_1442_ = lean_st_ref_get(v___y_1432_);
v_traceState_1443_ = lean_ctor_get(v___x_1442_, 4);
lean_inc_ref(v_traceState_1443_);
lean_dec(v___x_1442_);
v_traces_1444_ = lean_ctor_get(v_traceState_1443_, 0);
lean_inc_ref(v_traces_1444_);
lean_dec_ref(v_traceState_1443_);
v___x_1445_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1444_);
lean_dec_ref(v_traces_1444_);
v_sz_1446_ = lean_array_size(v___x_1445_);
v___x_1447_ = ((size_t)0ULL);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_1446_, v___x_1447_, v___x_1445_);
v_msg_1449_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1449_, 0, v_data_1426_);
lean_ctor_set(v_msg_1449_, 1, v_msg_1428_);
lean_ctor_set(v_msg_1449_, 2, v___x_1448_);
v___x_1450_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_1449_, v___y_1429_, v___y_1430_, v___x_1441_, v___y_1432_);
lean_dec_ref_known(v___x_1441_, 3);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1489_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1489_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v_traceState_1456_; lean_object* v_env_1457_; lean_object* v_nextMacroScope_1458_; lean_object* v_ngen_1459_; lean_object* v_auxDeclNGen_1460_; lean_object* v_cache_1461_; lean_object* v_recordedDeps_1462_; lean_object* v_messages_1463_; lean_object* v_infoState_1464_; lean_object* v_snapshotTasks_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1488_; 
v___x_1455_ = lean_st_ref_take(v___y_1432_);
v_traceState_1456_ = lean_ctor_get(v___x_1455_, 4);
v_env_1457_ = lean_ctor_get(v___x_1455_, 0);
v_nextMacroScope_1458_ = lean_ctor_get(v___x_1455_, 1);
v_ngen_1459_ = lean_ctor_get(v___x_1455_, 2);
v_auxDeclNGen_1460_ = lean_ctor_get(v___x_1455_, 3);
v_cache_1461_ = lean_ctor_get(v___x_1455_, 5);
v_recordedDeps_1462_ = lean_ctor_get(v___x_1455_, 6);
v_messages_1463_ = lean_ctor_get(v___x_1455_, 7);
v_infoState_1464_ = lean_ctor_get(v___x_1455_, 8);
v_snapshotTasks_1465_ = lean_ctor_get(v___x_1455_, 9);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1467_ = v___x_1455_;
v_isShared_1468_ = v_isSharedCheck_1488_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_snapshotTasks_1465_);
lean_inc(v_infoState_1464_);
lean_inc(v_messages_1463_);
lean_inc(v_recordedDeps_1462_);
lean_inc(v_cache_1461_);
lean_inc(v_traceState_1456_);
lean_inc(v_auxDeclNGen_1460_);
lean_inc(v_ngen_1459_);
lean_inc(v_nextMacroScope_1458_);
lean_inc(v_env_1457_);
lean_dec(v___x_1455_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1488_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
uint64_t v_tid_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1486_; 
v_tid_1469_ = lean_ctor_get_uint64(v_traceState_1456_, sizeof(void*)*1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_traceState_1456_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_traceState_1456_, 0);
lean_dec(v_unused_1487_);
v___x_1471_ = v_traceState_1456_;
v_isShared_1472_ = v_isSharedCheck_1486_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_traceState_1456_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1486_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1473_ = lean_box(0);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_ref_1427_);
lean_ctor_set(v___x_1474_, 1, v_a_1451_);
v___x_1475_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1425_, v___x_1474_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1475_);
v___x_1477_ = v___x_1471_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1475_);
lean_ctor_set_uint64(v_reuseFailAlloc_1485_, sizeof(void*)*1, v_tid_1469_);
v___x_1477_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 4, v___x_1477_);
v___x_1479_ = v___x_1467_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_env_1457_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_nextMacroScope_1458_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_ngen_1459_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_auxDeclNGen_1460_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1484_, 5, v_cache_1461_);
lean_ctor_set(v_reuseFailAlloc_1484_, 6, v_recordedDeps_1462_);
lean_ctor_set(v_reuseFailAlloc_1484_, 7, v_messages_1463_);
lean_ctor_set(v_reuseFailAlloc_1484_, 8, v_infoState_1464_);
lean_ctor_set(v_reuseFailAlloc_1484_, 9, v_snapshotTasks_1465_);
v___x_1479_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = lean_st_ref_put(v___y_1432_, v___x_1479_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1473_);
v___x_1482_ = v___x_1453_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1473_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg___boxed(lean_object* v_oldTraces_1490_, lean_object* v_data_1491_, lean_object* v_ref_1492_, lean_object* v_msg_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1490_, v_data_1491_, v_ref_1492_, v_msg_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(lean_object* v_cls_1500_, uint8_t v_collapsed_1501_, lean_object* v_tag_1502_, lean_object* v_opts_1503_, uint8_t v_clsEnabled_1504_, lean_object* v_oldTraces_1505_, lean_object* v_msg_1506_, lean_object* v_resStartStop_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_fst_1521_; lean_object* v_snd_1522_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v_data_1526_; lean_object* v_fst_1537_; lean_object* v_snd_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___y_1542_; lean_object* v_a_1543_; uint8_t v___y_1558_; double v___y_1590_; 
v_fst_1521_ = lean_ctor_get(v_resStartStop_1507_, 0);
lean_inc(v_fst_1521_);
v_snd_1522_ = lean_ctor_get(v_resStartStop_1507_, 1);
lean_inc(v_snd_1522_);
lean_dec_ref(v_resStartStop_1507_);
v_fst_1537_ = lean_ctor_get(v_snd_1522_, 0);
lean_inc(v_fst_1537_);
v_snd_1538_ = lean_ctor_get(v_snd_1522_, 1);
lean_inc(v_snd_1538_);
lean_dec(v_snd_1522_);
v___x_1539_ = l_Lean_trace_profiler;
v___x_1540_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1503_, v___x_1539_);
if (v___x_1540_ == 0)
{
v___y_1558_ = v___x_1540_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1596_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1503_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; double v___x_1599_; double v___x_1600_; double v___x_1601_; 
v___x_1597_ = l_Lean_trace_profiler_threshold;
v___x_1598_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1503_, v___x_1597_);
v___x_1599_ = lean_float_of_nat(v___x_1598_);
v___x_1600_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_1601_ = lean_float_div(v___x_1599_, v___x_1600_);
v___y_1590_ = v___x_1601_;
goto v___jp_1589_;
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; double v___x_1604_; 
v___x_1602_ = l_Lean_trace_profiler_threshold;
v___x_1603_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_1503_, v___x_1602_);
v___x_1604_ = lean_float_of_nat(v___x_1603_);
v___y_1590_ = v___x_1604_;
goto v___jp_1589_;
}
}
v___jp_1523_:
{
lean_object* v___x_1527_; 
lean_inc(v___y_1524_);
v___x_1527_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_1505_, v_data_1526_, v___y_1524_, v___y_1525_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1528_; 
lean_dec_ref_known(v___x_1527_, 1);
v___x_1528_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_1521_);
return v___x_1528_;
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_fst_1521_);
v_a_1529_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1527_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
v___jp_1541_:
{
uint8_t v_result_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; double v___x_1547_; lean_object* v_data_1548_; 
v_result_1544_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8_spec__19(v_fst_1521_);
v___x_1545_ = lean_box(v_result_1544_);
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
v___x_1547_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_1502_);
lean_inc_ref(v___x_1546_);
lean_inc(v_cls_1500_);
v_data_1548_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1548_, 0, v_cls_1500_);
lean_ctor_set(v_data_1548_, 1, v___x_1546_);
lean_ctor_set(v_data_1548_, 2, v_tag_1502_);
lean_ctor_set_float(v_data_1548_, sizeof(void*)*3, v___x_1547_);
lean_ctor_set_float(v_data_1548_, sizeof(void*)*3 + 8, v___x_1547_);
lean_ctor_set_uint8(v_data_1548_, sizeof(void*)*3 + 16, v_collapsed_1501_);
if (v___x_1540_ == 0)
{
lean_dec_ref_known(v___x_1546_, 1);
lean_dec(v_snd_1538_);
lean_dec(v_fst_1537_);
lean_dec_ref(v_tag_1502_);
lean_dec(v_cls_1500_);
v___y_1524_ = v___y_1542_;
v___y_1525_ = v_a_1543_;
v_data_1526_ = v_data_1548_;
goto v___jp_1523_;
}
else
{
lean_object* v_data_1549_; double v___x_1550_; double v___x_1551_; 
lean_dec_ref_known(v_data_1548_, 3);
v_data_1549_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1549_, 0, v_cls_1500_);
lean_ctor_set(v_data_1549_, 1, v___x_1546_);
lean_ctor_set(v_data_1549_, 2, v_tag_1502_);
v___x_1550_ = lean_unbox_float(v_fst_1537_);
lean_dec(v_fst_1537_);
lean_ctor_set_float(v_data_1549_, sizeof(void*)*3, v___x_1550_);
v___x_1551_ = lean_unbox_float(v_snd_1538_);
lean_dec(v_snd_1538_);
lean_ctor_set_float(v_data_1549_, sizeof(void*)*3 + 8, v___x_1551_);
lean_ctor_set_uint8(v_data_1549_, sizeof(void*)*3 + 16, v_collapsed_1501_);
v___y_1524_ = v___y_1542_;
v___y_1525_ = v_a_1543_;
v_data_1526_ = v_data_1549_;
goto v___jp_1523_;
}
}
v___jp_1552_:
{
lean_object* v_ref_1553_; lean_object* v___x_1554_; 
v_ref_1553_ = lean_ctor_get(v___y_1518_, 2);
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc_ref(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc(v___y_1510_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc(v_fst_1521_);
v___x_1554_ = lean_apply_14(v_msg_1506_, v_fst_1521_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, lean_box(0));
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___y_1542_ = v_ref_1553_;
v_a_1543_ = v_a_1555_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1556_; 
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_1542_ = v_ref_1553_;
v_a_1543_ = v___x_1556_;
goto v___jp_1541_;
}
}
v___jp_1557_:
{
if (v_clsEnabled_1504_ == 0)
{
if (v___y_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v_traceState_1560_; lean_object* v_env_1561_; lean_object* v_nextMacroScope_1562_; lean_object* v_ngen_1563_; lean_object* v_auxDeclNGen_1564_; lean_object* v_cache_1565_; lean_object* v_recordedDeps_1566_; lean_object* v_messages_1567_; lean_object* v_infoState_1568_; lean_object* v_snapshotTasks_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_snd_1538_);
lean_dec(v_fst_1537_);
lean_dec_ref(v_msg_1506_);
lean_dec_ref(v_tag_1502_);
lean_dec(v_cls_1500_);
v___x_1559_ = lean_st_ref_take(v___y_1519_);
v_traceState_1560_ = lean_ctor_get(v___x_1559_, 4);
v_env_1561_ = lean_ctor_get(v___x_1559_, 0);
v_nextMacroScope_1562_ = lean_ctor_get(v___x_1559_, 1);
v_ngen_1563_ = lean_ctor_get(v___x_1559_, 2);
v_auxDeclNGen_1564_ = lean_ctor_get(v___x_1559_, 3);
v_cache_1565_ = lean_ctor_get(v___x_1559_, 5);
v_recordedDeps_1566_ = lean_ctor_get(v___x_1559_, 6);
v_messages_1567_ = lean_ctor_get(v___x_1559_, 7);
v_infoState_1568_ = lean_ctor_get(v___x_1559_, 8);
v_snapshotTasks_1569_ = lean_ctor_get(v___x_1559_, 9);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1571_ = v___x_1559_;
v_isShared_1572_ = v_isSharedCheck_1588_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_snapshotTasks_1569_);
lean_inc(v_infoState_1568_);
lean_inc(v_messages_1567_);
lean_inc(v_recordedDeps_1566_);
lean_inc(v_cache_1565_);
lean_inc(v_traceState_1560_);
lean_inc(v_auxDeclNGen_1564_);
lean_inc(v_ngen_1563_);
lean_inc(v_nextMacroScope_1562_);
lean_inc(v_env_1561_);
lean_dec(v___x_1559_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1588_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
uint64_t v_tid_1573_; lean_object* v_traces_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1587_; 
v_tid_1573_ = lean_ctor_get_uint64(v_traceState_1560_, sizeof(void*)*1);
v_traces_1574_ = lean_ctor_get(v_traceState_1560_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_traceState_1560_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1576_ = v_traceState_1560_;
v_isShared_1577_ = v_isSharedCheck_1587_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_traces_1574_);
lean_dec(v_traceState_1560_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1587_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1505_, v_traces_1574_);
lean_dec_ref(v_traces_1574_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1578_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1578_);
lean_ctor_set_uint64(v_reuseFailAlloc_1586_, sizeof(void*)*1, v_tid_1573_);
v___x_1580_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 4, v___x_1580_);
v___x_1582_ = v___x_1571_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_env_1561_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_nextMacroScope_1562_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_ngen_1563_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_auxDeclNGen_1564_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1585_, 5, v_cache_1565_);
lean_ctor_set(v_reuseFailAlloc_1585_, 6, v_recordedDeps_1566_);
lean_ctor_set(v_reuseFailAlloc_1585_, 7, v_messages_1567_);
lean_ctor_set(v_reuseFailAlloc_1585_, 8, v_infoState_1568_);
lean_ctor_set(v_reuseFailAlloc_1585_, 9, v_snapshotTasks_1569_);
v___x_1582_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_st_ref_put(v___y_1519_, v___x_1582_);
v___x_1584_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_1521_);
return v___x_1584_;
}
}
}
}
}
else
{
goto v___jp_1552_;
}
}
else
{
goto v___jp_1552_;
}
}
v___jp_1589_:
{
double v___x_1591_; double v___x_1592_; double v___x_1593_; uint8_t v___x_1594_; 
v___x_1591_ = lean_unbox_float(v_snd_1538_);
v___x_1592_ = lean_unbox_float(v_fst_1537_);
v___x_1593_ = lean_float_sub(v___x_1591_, v___x_1592_);
v___x_1594_ = lean_float_decLt(v___y_1590_, v___x_1593_);
v___y_1558_ = v___x_1594_;
goto v___jp_1557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8___boxed(lean_object** _args){
lean_object* v_cls_1605_ = _args[0];
lean_object* v_collapsed_1606_ = _args[1];
lean_object* v_tag_1607_ = _args[2];
lean_object* v_opts_1608_ = _args[3];
lean_object* v_clsEnabled_1609_ = _args[4];
lean_object* v_oldTraces_1610_ = _args[5];
lean_object* v_msg_1611_ = _args[6];
lean_object* v_resStartStop_1612_ = _args[7];
lean_object* v___y_1613_ = _args[8];
lean_object* v___y_1614_ = _args[9];
lean_object* v___y_1615_ = _args[10];
lean_object* v___y_1616_ = _args[11];
lean_object* v___y_1617_ = _args[12];
lean_object* v___y_1618_ = _args[13];
lean_object* v___y_1619_ = _args[14];
lean_object* v___y_1620_ = _args[15];
lean_object* v___y_1621_ = _args[16];
lean_object* v___y_1622_ = _args[17];
lean_object* v___y_1623_ = _args[18];
lean_object* v___y_1624_ = _args[19];
lean_object* v___y_1625_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_1626_; uint8_t v_clsEnabled_boxed_1627_; lean_object* v_res_1628_; 
v_collapsed_boxed_1626_ = lean_unbox(v_collapsed_1606_);
v_clsEnabled_boxed_1627_ = lean_unbox(v_clsEnabled_1609_);
v_res_1628_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1605_, v_collapsed_boxed_1626_, v_tag_1607_, v_opts_1608_, v_clsEnabled_boxed_1627_, v_oldTraces_1610_, v_msg_1611_, v_resStartStop_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v_opts_1608_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(lean_object* v___f_1629_, lean_object* v_cls_1630_, uint8_t v___x_1631_, lean_object* v___x_1632_, lean_object* v___f_1633_, lean_object* v___f_1634_, lean_object* v_opts_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___y_1650_; lean_object* v___y_1651_; uint8_t v___y_1652_; lean_object* v_a_1653_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; lean_object* v_a_1666_; uint8_t v_hasTrace_1678_; 
v_hasTrace_1678_ = lean_ctor_get_uint8(v_opts_1635_, sizeof(void*)*1);
if (v_hasTrace_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec_ref(v___f_1634_);
lean_dec_ref(v___f_1633_);
lean_dec_ref(v___x_1632_);
lean_dec(v_cls_1630_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc(v___y_1639_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1637_);
v___x_1679_ = lean_apply_12(v___f_1629_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, lean_box(0));
return v___x_1679_;
}
else
{
lean_object* v_toCold_1680_; lean_object* v_ref_1681_; uint8_t v___y_1683_; uint8_t v_a_1741_; lean_object* v_options_1745_; uint8_t v_hasTrace_1746_; 
v_toCold_1680_ = lean_ctor_get(v___y_1646_, 0);
v_ref_1681_ = lean_ctor_get(v___y_1646_, 2);
v_options_1745_ = lean_ctor_get(v_toCold_1680_, 2);
v_hasTrace_1746_ = lean_ctor_get_uint8(v_options_1745_, sizeof(void*)*1);
if (v_hasTrace_1746_ == 0)
{
v_a_1741_ = v_hasTrace_1746_;
goto v___jp_1740_;
}
else
{
lean_object* v_inheritedTraceOptions_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_inheritedTraceOptions_1747_ = lean_ctor_get(v_toCold_1680_, 11);
v___x_1748_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v_cls_1630_);
v___x_1749_ = l_Lean_Name_append(v___x_1748_, v_cls_1630_);
v___x_1750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1747_, v_options_1745_, v___x_1749_);
lean_dec(v___x_1749_);
if (v___x_1750_ == 0)
{
v_a_1741_ = v___x_1750_;
goto v___jp_1740_;
}
else
{
lean_dec_ref(v___f_1629_);
v___y_1683_ = v___x_1750_;
goto v___jp_1682_;
}
}
v___jp_1682_:
{
lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1739_; 
v___x_1684_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_1647_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1739_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1739_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1690_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1635_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_io_mono_nanos_now();
v___x_1692_ = l_IO_lazyPure___redArg(v___f_1634_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1687_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
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
v___y_1663_ = v_a_1685_;
v___y_1664_ = v___x_1691_;
v___y_1665_ = v___y_1683_;
v_a_1666_ = v___x_1698_;
goto v___jp_1662_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1714_; 
v_a_1701_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1703_ = v___x_1692_;
v_isShared_1704_ = v_isSharedCheck_1714_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1692_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1714_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = lean_io_error_to_string(v_a_1701_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 3);
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1708_ = l_Lean_MessageData_ofFormat(v___x_1707_);
lean_inc(v_ref_1681_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v_ref_1681_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1709_);
v___x_1711_ = v___x_1687_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
v___y_1663_ = v_a_1685_;
v___y_1664_ = v___x_1691_;
v___y_1665_ = v___y_1683_;
v_a_1666_ = v___x_1711_;
goto v___jp_1662_;
}
}
}
}
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_io_get_num_heartbeats();
v___x_1716_ = l_IO_lazyPure___redArg(v___f_1634_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_del_object(v___x_1687_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set_tag(v___x_1719_, 1);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
v___y_1650_ = v_a_1685_;
v___y_1651_ = v___x_1715_;
v___y_1652_ = v___y_1683_;
v_a_1653_ = v___x_1722_;
goto v___jp_1649_;
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1738_; 
v_a_1725_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1727_ = v___x_1716_;
v_isShared_1728_ = v_isSharedCheck_1738_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1716_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1738_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_io_error_to_string(v_a_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 3);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1732_ = l_Lean_MessageData_ofFormat(v___x_1731_);
lean_inc(v_ref_1681_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_ref_1681_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1733_);
v___x_1735_ = v___x_1687_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
v___y_1650_ = v_a_1685_;
v___y_1651_ = v___x_1715_;
v___y_1652_ = v___y_1683_;
v_a_1653_ = v___x_1735_;
goto v___jp_1649_;
}
}
}
}
}
}
}
v___jp_1740_:
{
lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = l_Lean_trace_profiler;
v___x_1743_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_1635_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec_ref(v___f_1634_);
lean_dec_ref(v___f_1633_);
lean_dec_ref(v___x_1632_);
lean_dec(v_cls_1630_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc_ref(v___y_1640_);
lean_inc(v___y_1639_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1637_);
v___x_1744_ = lean_apply_12(v___f_1629_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, lean_box(0));
return v___x_1744_;
}
else
{
lean_dec_ref(v___f_1629_);
v___y_1683_ = v_a_1741_;
goto v___jp_1682_;
}
}
}
v___jp_1649_:
{
lean_object* v___x_1654_; double v___x_1655_; double v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1654_ = lean_io_get_num_heartbeats();
v___x_1655_ = lean_float_of_nat(v___y_1651_);
v___x_1656_ = lean_float_of_nat(v___x_1654_);
v___x_1657_ = lean_box_float(v___x_1655_);
v___x_1658_ = lean_box_float(v___x_1656_);
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v_a_1653_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1630_, v___x_1631_, v___x_1632_, v_opts_1635_, v___y_1652_, v___y_1650_, v___f_1633_, v___x_1660_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
return v___x_1661_;
}
v___jp_1662_:
{
lean_object* v___x_1667_; double v___x_1668_; double v___x_1669_; double v___x_1670_; double v___x_1671_; double v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1667_ = lean_io_mono_nanos_now();
v___x_1668_ = lean_float_of_nat(v___y_1664_);
v___x_1669_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_1670_ = lean_float_div(v___x_1668_, v___x_1669_);
v___x_1671_ = lean_float_of_nat(v___x_1667_);
v___x_1672_ = lean_float_div(v___x_1671_, v___x_1669_);
v___x_1673_ = lean_box_float(v___x_1670_);
v___x_1674_ = lean_box_float(v___x_1672_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_a_1666_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_1630_, v___x_1631_, v___x_1632_, v_opts_1635_, v___y_1665_, v___y_1663_, v___f_1633_, v___x_1676_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5___boxed(lean_object** _args){
lean_object* v___f_1751_ = _args[0];
lean_object* v_cls_1752_ = _args[1];
lean_object* v___x_1753_ = _args[2];
lean_object* v___x_1754_ = _args[3];
lean_object* v___f_1755_ = _args[4];
lean_object* v___f_1756_ = _args[5];
lean_object* v_opts_1757_ = _args[6];
lean_object* v___y_1758_ = _args[7];
lean_object* v___y_1759_ = _args[8];
lean_object* v___y_1760_ = _args[9];
lean_object* v___y_1761_ = _args[10];
lean_object* v___y_1762_ = _args[11];
lean_object* v___y_1763_ = _args[12];
lean_object* v___y_1764_ = _args[13];
lean_object* v___y_1765_ = _args[14];
lean_object* v___y_1766_ = _args[15];
lean_object* v___y_1767_ = _args[16];
lean_object* v___y_1768_ = _args[17];
lean_object* v___y_1769_ = _args[18];
lean_object* v___y_1770_ = _args[19];
_start:
{
uint8_t v___x_653048__boxed_1771_; lean_object* v_res_1772_; 
v___x_653048__boxed_1771_ = lean_unbox(v___x_1753_);
v_res_1772_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_1751_, v_cls_1752_, v___x_653048__boxed_1771_, v___x_1754_, v___f_1755_, v___f_1756_, v_opts_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v_opts_1757_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(lean_object* v_aig_1773_){
_start:
{
lean_object* v_decls_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_decls_1774_ = lean_ctor_get(v_aig_1773_, 0);
v___x_1775_ = lean_array_get_size(v_decls_1774_);
v___x_1776_ = 0;
v___x_1777_ = lean_box(v___x_1776_);
v___x_1778_ = lean_mk_array(v___x_1775_, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0___boxed(lean_object* v_aig_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1779_);
lean_dec_ref(v_aig_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(lean_object* v_aig_1783_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = ((lean_object*)(l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___closed__0));
v___x_1785_ = l___private_Std_Sat_AIG_CNF_0__Std_Sat_AIG_toCNF_Cache_init___at___00Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0_spec__0(v_aig_1783_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0___boxed(lean_object* v_aig_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1787_);
lean_dec_ref(v_aig_1787_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(lean_object* v_aig_1791_, lean_object* v___x_1792_, lean_object* v_entry_1793_, lean_object* v_ref_1794_, lean_object* v_x_1795_){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_state_1798_; lean_object* v_cnf_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1819_; 
v___x_1796_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1797_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1791_);
v_state_1798_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1792_, v___x_1796_, v_entry_1793_, v___x_1797_);
lean_dec_ref(v___x_1796_);
v_cnf_1799_ = lean_ctor_get(v_state_1798_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_state_1798_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v_state_1798_, 1);
lean_dec(v_unused_1820_);
v___x_1801_ = v_state_1798_;
v_isShared_1802_ = v_isSharedCheck_1819_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_cnf_1799_);
lean_dec(v_state_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1819_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_gate_1803_; uint8_t v_invert_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___y_1808_; uint8_t v___y_1809_; 
v_gate_1803_ = lean_ctor_get(v_ref_1794_, 0);
lean_inc(v_gate_1803_);
v_invert_1804_ = lean_ctor_get_uint8(v_ref_1794_, sizeof(void*)*1);
lean_dec_ref(v_ref_1794_);
v___x_1805_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1806_ = l_ByteArray_empty;
if (v_invert_1804_ == 0)
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = lean_array_push(v___x_1805_, v_gate_1803_);
v___x_1816_ = 1;
v___y_1808_ = v___x_1815_;
v___y_1809_ = v___x_1816_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = lean_array_push(v___x_1805_, v_gate_1803_);
v___x_1818_ = 0;
v___y_1808_ = v___x_1817_;
v___y_1809_ = v___x_1818_;
goto v___jp_1807_;
}
v___jp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_byte_array_push(v___x_1806_, v___y_1809_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1810_);
lean_ctor_set(v___x_1801_, 0, v___y_1808_);
v___x_1812_ = v___x_1801_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___y_1808_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_array_push(v_cnf_1799_, v___x_1812_);
return v___x_1813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed(lean_object* v_aig_1821_, lean_object* v___x_1822_, lean_object* v_entry_1823_, lean_object* v_ref_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6(v_aig_1821_, v___x_1822_, v_entry_1823_, v_ref_1824_, v_x_1825_);
lean_dec_ref(v___x_1822_);
lean_dec_ref(v_aig_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(lean_object* v___f_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_ref_1840_; lean_object* v___x_1841_; 
v_ref_1840_ = lean_ctor_get(v___y_1837_, 2);
v___x_1841_ = l_IO_lazyPure___redArg(v___f_1827_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1861_; 
v_a_1850_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1852_ = v___x_1841_;
v_isShared_1853_ = v_isSharedCheck_1861_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1841_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1861_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1854_ = lean_io_error_to_string(v_a_1850_);
v___x_1855_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
v___x_1856_ = l_Lean_MessageData_ofFormat(v___x_1855_);
lean_inc(v_ref_1840_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_ref_1840_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1857_);
v___x_1859_ = v___x_1852_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed(lean_object* v___f_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7(v___f_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1875_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__1));
v___x_1880_ = l_Lean_MessageData_ofFormat(v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___boxed(lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12(v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v_x_1897_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(lean_object* v_aig_1912_, lean_object* v___x_1913_, lean_object* v_a_1914_, lean_object* v_ref_1915_, uint8_t v___x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_state_1920_; lean_object* v_cnf_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1942_; 
v___x_1918_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_1919_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_1912_);
v_state_1920_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_1913_, v___x_1918_, v_a_1914_, v___x_1919_);
lean_dec_ref(v___x_1918_);
v_cnf_1921_ = lean_ctor_get(v_state_1920_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_state_1920_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_state_1920_, 1);
lean_dec(v_unused_1943_);
v___x_1923_ = v_state_1920_;
v_isShared_1924_ = v_isSharedCheck_1942_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_cnf_1921_);
lean_dec(v_state_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1942_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v_gate_1925_; uint8_t v_invert_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___y_1930_; uint8_t v___y_1931_; 
v_gate_1925_ = lean_ctor_get(v_ref_1915_, 0);
lean_inc(v_gate_1925_);
v_invert_1926_ = lean_ctor_get_uint8(v_ref_1915_, sizeof(void*)*1);
lean_dec_ref(v_ref_1915_);
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_1928_ = l_ByteArray_empty;
if (v_invert_1926_ == 0)
{
goto v___jp_1937_;
}
else
{
if (v___x_1916_ == 0)
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = lean_array_push(v___x_1927_, v_gate_1925_);
v___x_1941_ = 0;
v___y_1930_ = v___x_1940_;
v___y_1931_ = v___x_1941_;
goto v___jp_1929_;
}
else
{
goto v___jp_1937_;
}
}
v___jp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_byte_array_push(v___x_1928_, v___y_1931_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 1, v___x_1932_);
lean_ctor_set(v___x_1923_, 0, v___y_1930_);
v___x_1934_ = v___x_1923_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___y_1930_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_array_push(v_cnf_1921_, v___x_1934_);
return v___x_1935_;
}
}
v___jp_1937_:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_array_push(v___x_1927_, v_gate_1925_);
v___x_1939_ = 1;
v___y_1930_ = v___x_1938_;
v___y_1931_ = v___x_1939_;
goto v___jp_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed(lean_object* v_aig_1944_, lean_object* v___x_1945_, lean_object* v_a_1946_, lean_object* v_ref_1947_, lean_object* v___x_1948_, lean_object* v_x_1949_){
_start:
{
uint8_t v___x_653518__boxed_1950_; lean_object* v_res_1951_; 
v___x_653518__boxed_1950_ = lean_unbox(v___x_1948_);
v_res_1951_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8(v_aig_1944_, v___x_1945_, v_a_1946_, v_ref_1947_, v___x_653518__boxed_1950_, v_x_1949_);
lean_dec_ref(v___x_1945_);
lean_dec_ref(v_aig_1944_);
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
lean_object* v_l_2288_; lean_object* v_r_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___y_2293_; uint8_t v___y_2294_; uint8_t v___y_2295_; uint8_t v___y_2319_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
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
v___x_2301_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_2294_);
v___x_2302_ = lean_string_append(v___x_2300_, v___x_2301_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = ((lean_object*)(l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg___closed__1));
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
v___x_2305_ = lean_string_append(v___x_2304_, v___x_2296_);
lean_dec_ref(v___x_2296_);
v___x_2306_ = lean_string_append(v___x_2305_, v___x_2297_);
lean_inc(v___y_2293_);
v___x_2307_ = l_Nat_reprFast(v___y_2293_);
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
v_idx_2281_ = v___y_2293_;
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
v___y_2293_ = v___x_2320_;
v___y_2294_ = v___y_2319_;
v___y_2295_ = v___x_2324_;
goto v___jp_2292_;
}
else
{
v___y_2293_ = v___x_2320_;
v___y_2294_ = v___y_2319_;
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
lean_inc(v___y_2540_);
v___x_2542_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_2520_, v_data_2541_, v___y_2540_, v___y_2539_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
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
v___y_2539_ = v_a_2558_;
v___y_2540_ = v___y_2557_;
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
v___y_2539_ = v_a_2558_;
v___y_2540_ = v___y_2557_;
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
size_t v_x_654704__boxed_2783_; size_t v_x_654705__boxed_2784_; lean_object* v_res_2785_; 
v_x_654704__boxed_2783_ = lean_unbox_usize(v_x_2779_);
lean_dec(v_x_2779_);
v_x_654705__boxed_2784_ = lean_unbox_usize(v_x_2780_);
lean_dec(v_x_2780_);
v_res_2785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_2778_, v_x_654704__boxed_2783_, v_x_654705__boxed_2784_, v_x_2781_, v_x_2782_);
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
lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; uint8_t v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v_a_3030_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; uint8_t v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v_a_3057_; lean_object* v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; uint8_t v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; uint8_t v___y_3083_; uint8_t v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v_config_3131_; lean_object* v_solver_3132_; lean_object* v_lratPath_3133_; lean_object* v_timeout_3134_; uint8_t v_trimProofs_3135_; uint8_t v_binaryProofs_3136_; uint8_t v_graphviz_3137_; uint8_t v_solverMode_3138_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; uint8_t v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v_a_3193_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v_a_3223_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v_toCold_3316_; lean_object* v_ref_3317_; lean_object* v___y_3318_; 
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
v_toCold_2966_ = lean_ctor_get(v___y_2957_, 0);
v_options_2967_ = lean_ctor_get(v_toCold_2966_, 2);
v_hasTrace_2968_ = lean_ctor_get_uint8(v_options_2967_, sizeof(void*)*1);
if (v_hasTrace_2968_ == 0)
{
lean_object* v_a_2969_; 
lean_dec(v___y_2952_);
v_a_2969_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v_a_2965_, 1);
v___y_2925_ = v_a_2969_;
v___y_2926_ = v___y_2953_;
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
lean_inc(v___y_2952_);
v___x_2973_ = l_Lean_Name_append(v___x_2972_, v___y_2952_);
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2971_, v_options_2967_, v___x_2973_);
lean_dec(v___x_2973_);
if (v___x_2974_ == 0)
{
lean_dec(v___y_2952_);
v___y_2925_ = v_a_2970_;
v___y_2926_ = v___y_2953_;
goto v___jp_2924_;
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_2976_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2952_, v___x_2975_, v___y_2961_, v___y_2956_, v___y_2957_, v___y_2955_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_dec_ref_known(v___x_2976_, 1);
v___y_2925_ = v_a_2970_;
v___y_2926_ = v___y_2953_;
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
v_toCold_2985_ = lean_ctor_get(v___y_2957_, 0);
v_options_2986_ = lean_ctor_get(v_toCold_2985_, 2);
v_hasTrace_2987_ = lean_ctor_get_uint8(v_options_2986_, sizeof(void*)*1);
if (v_hasTrace_2987_ == 0)
{
lean_object* v_a_2988_; 
lean_dec(v___y_2952_);
v_a_2988_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v_a_2965_, 1);
v___y_2882_ = v_a_2988_;
v___y_2883_ = v___y_2963_;
v___y_2884_ = v___y_2953_;
v___y_2885_ = v___y_2958_;
v___y_2886_ = v___y_2959_;
v___y_2887_ = v___y_2960_;
v___y_2888_ = v___y_2954_;
v___y_2889_ = v___y_2962_;
v___y_2890_ = v___y_2961_;
v___y_2891_ = v___y_2956_;
v___y_2892_ = v___y_2957_;
v___y_2893_ = v___y_2955_;
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
lean_inc(v___y_2952_);
v___x_2992_ = l_Lean_Name_append(v___x_2991_, v___y_2952_);
v___x_2993_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2990_, v_options_2986_, v___x_2992_);
lean_dec(v___x_2992_);
if (v___x_2993_ == 0)
{
lean_dec(v___y_2952_);
v___y_2882_ = v_a_2989_;
v___y_2883_ = v___y_2963_;
v___y_2884_ = v___y_2953_;
v___y_2885_ = v___y_2958_;
v___y_2886_ = v___y_2959_;
v___y_2887_ = v___y_2960_;
v___y_2888_ = v___y_2954_;
v___y_2889_ = v___y_2962_;
v___y_2890_ = v___y_2961_;
v___y_2891_ = v___y_2956_;
v___y_2892_ = v___y_2957_;
v___y_2893_ = v___y_2955_;
goto v___jp_2881_;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_2995_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_2952_, v___x_2994_, v___y_2961_, v___y_2956_, v___y_2957_, v___y_2955_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec_ref_known(v___x_2995_, 1);
v___y_2882_ = v_a_2989_;
v___y_2883_ = v___y_2963_;
v___y_2884_ = v___y_2953_;
v___y_2885_ = v___y_2958_;
v___y_2886_ = v___y_2959_;
v___y_2887_ = v___y_2960_;
v___y_2888_ = v___y_2954_;
v___y_2889_ = v___y_2962_;
v___y_2890_ = v___y_2961_;
v___y_2891_ = v___y_2956_;
v___y_2892_ = v___y_2957_;
v___y_2893_ = v___y_2955_;
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
lean_dec(v___y_2952_);
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
v___x_3032_ = lean_float_of_nat(v___y_3017_);
v___x_3033_ = lean_float_of_nat(v___x_3031_);
v___x_3034_ = lean_box_float(v___x_3032_);
v___x_3035_ = lean_box_float(v___x_3033_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_a_3030_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
lean_inc(v___y_3013_);
v___x_3038_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3013_, v___x_2857_, v___x_2858_, v___y_3026_, v___y_3021_, v___y_3019_, v___f_2859_, v___x_3037_, v___y_3025_, v___y_3029_, v___y_3014_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3016_, v___y_3028_, v___y_3027_, v___y_3018_, v___y_3020_, v___y_3015_);
v___y_2952_ = v___y_3013_;
v___y_2953_ = v___y_3014_;
v___y_2954_ = v___y_3016_;
v___y_2955_ = v___y_3015_;
v___y_2956_ = v___y_3018_;
v___y_2957_ = v___y_3020_;
v___y_2958_ = v___y_3022_;
v___y_2959_ = v___y_3023_;
v___y_2960_ = v___y_3024_;
v___y_2961_ = v___y_3027_;
v___y_2962_ = v___y_3028_;
v___y_2963_ = v___y_3029_;
v___y_2964_ = v___x_3038_;
goto v___jp_2951_;
}
v___jp_3039_:
{
lean_object* v___x_3058_; double v___x_3059_; double v___x_3060_; double v___x_3061_; double v___x_3062_; double v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3058_ = lean_io_mono_nanos_now();
v___x_3059_ = lean_float_of_nat(v___y_3042_);
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
lean_inc(v___y_3040_);
v___x_3068_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3040_, v___x_2857_, v___x_2858_, v___y_3053_, v___y_3048_, v___y_3046_, v___f_2859_, v___x_3067_, v___y_3052_, v___y_3056_, v___y_3041_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3044_, v___y_3055_, v___y_3054_, v___y_3045_, v___y_3047_, v___y_3043_);
v___y_2952_ = v___y_3040_;
v___y_2953_ = v___y_3041_;
v___y_2954_ = v___y_3044_;
v___y_2955_ = v___y_3043_;
v___y_2956_ = v___y_3045_;
v___y_2957_ = v___y_3047_;
v___y_2958_ = v___y_3049_;
v___y_2959_ = v___y_3050_;
v___y_2960_ = v___y_3051_;
v___y_2961_ = v___y_3054_;
v___y_2962_ = v___y_3055_;
v___y_2963_ = v___y_3056_;
v___y_2964_ = v___x_3068_;
goto v___jp_2951_;
}
v___jp_3069_:
{
lean_object* v___x_3092_; lean_object* v_a_3093_; uint8_t v___x_3094_; 
v___x_3092_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3074_);
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref(v___x_3092_);
v___x_3094_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3087_, v___x_2860_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = lean_io_mono_nanos_now();
v___x_3096_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3075_, v___y_3085_, v___y_3077_, v___y_3084_, v___y_3090_, v___y_3083_, v___y_3072_, v___y_3081_, v___y_3074_);
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
v___y_3042_ = v___x_3095_;
v___y_3043_ = v___y_3074_;
v___y_3044_ = v___y_3073_;
v___y_3045_ = v___y_3076_;
v___y_3046_ = v_a_3093_;
v___y_3047_ = v___y_3081_;
v___y_3048_ = v___y_3078_;
v___y_3049_ = v___y_3079_;
v___y_3050_ = v___y_3080_;
v___y_3051_ = v___y_3082_;
v___y_3052_ = v___y_3086_;
v___y_3053_ = v___y_3087_;
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
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
v___y_3042_ = v___x_3095_;
v___y_3043_ = v___y_3074_;
v___y_3044_ = v___y_3073_;
v___y_3045_ = v___y_3076_;
v___y_3046_ = v_a_3093_;
v___y_3047_ = v___y_3081_;
v___y_3048_ = v___y_3078_;
v___y_3049_ = v___y_3079_;
v___y_3050_ = v___y_3080_;
v___y_3051_ = v___y_3082_;
v___y_3052_ = v___y_3086_;
v___y_3053_ = v___y_3087_;
v___y_3054_ = v___y_3088_;
v___y_3055_ = v___y_3089_;
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
v___x_3114_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3075_, v___y_3085_, v___y_3077_, v___y_3084_, v___y_3090_, v___y_3083_, v___y_3072_, v___y_3081_, v___y_3074_);
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
v___y_3015_ = v___y_3074_;
v___y_3016_ = v___y_3073_;
v___y_3017_ = v___x_3113_;
v___y_3018_ = v___y_3076_;
v___y_3019_ = v_a_3093_;
v___y_3020_ = v___y_3081_;
v___y_3021_ = v___y_3078_;
v___y_3022_ = v___y_3079_;
v___y_3023_ = v___y_3080_;
v___y_3024_ = v___y_3082_;
v___y_3025_ = v___y_3086_;
v___y_3026_ = v___y_3087_;
v___y_3027_ = v___y_3088_;
v___y_3028_ = v___y_3089_;
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
v___y_3015_ = v___y_3074_;
v___y_3016_ = v___y_3073_;
v___y_3017_ = v___x_3113_;
v___y_3018_ = v___y_3076_;
v___y_3019_ = v_a_3093_;
v___y_3020_ = v___y_3081_;
v___y_3021_ = v___y_3078_;
v___y_3022_ = v___y_3079_;
v___y_3023_ = v___y_3080_;
v___y_3024_ = v___y_3082_;
v___y_3025_ = v___y_3086_;
v___y_3026_ = v___y_3087_;
v___y_3027_ = v___y_3088_;
v___y_3028_ = v___y_3089_;
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
v_toCold_3154_ = lean_ctor_get(v___y_3145_, 0);
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
v___x_3158_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3157_, v_solver_3132_, v_lratPath_3133_, v_trimProofs_3135_, v_timeout_3134_, v_binaryProofs_3136_, v_solverMode_3138_, v___y_3145_, v___y_3142_);
v___y_2952_ = v___y_3140_;
v___y_2953_ = v___y_3141_;
v___y_2954_ = v___y_3143_;
v___y_2955_ = v___y_3142_;
v___y_2956_ = v___y_3144_;
v___y_2957_ = v___y_3145_;
v___y_2958_ = v___y_3146_;
v___y_2959_ = v___y_3147_;
v___y_2960_ = v___y_3148_;
v___y_2961_ = v___y_3150_;
v___y_2962_ = v___y_3151_;
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
lean_inc(v___y_3140_);
v___x_3162_ = l_Lean_Name_append(v___x_3161_, v___y_3140_);
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
v___x_3166_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3159_, v_solver_3132_, v_lratPath_3133_, v_trimProofs_3135_, v_timeout_3134_, v_binaryProofs_3136_, v_solverMode_3138_, v___y_3145_, v___y_3142_);
v___y_2952_ = v___y_3140_;
v___y_2953_ = v___y_3141_;
v___y_2954_ = v___y_3143_;
v___y_2955_ = v___y_3142_;
v___y_2956_ = v___y_3144_;
v___y_2957_ = v___y_3145_;
v___y_2958_ = v___y_3146_;
v___y_2959_ = v___y_3147_;
v___y_2960_ = v___y_3148_;
v___y_2961_ = v___y_3150_;
v___y_2962_ = v___y_3151_;
v___y_2963_ = v___y_3152_;
v___y_2964_ = v___x_3166_;
goto v___jp_2951_;
}
else
{
lean_inc(v_timeout_3134_);
lean_inc_ref(v_solver_3132_);
lean_inc_ref(v_lratPath_3133_);
v___y_3070_ = v___y_3140_;
v___y_3071_ = v___y_3141_;
v___y_3072_ = v_solverMode_3138_;
v___y_3073_ = v___y_3143_;
v___y_3074_ = v___y_3142_;
v___y_3075_ = v_a_3159_;
v___y_3076_ = v___y_3144_;
v___y_3077_ = v_lratPath_3133_;
v___y_3078_ = v___x_3163_;
v___y_3079_ = v___y_3146_;
v___y_3080_ = v___y_3147_;
v___y_3081_ = v___y_3145_;
v___y_3082_ = v___y_3148_;
v___y_3083_ = v_binaryProofs_3136_;
v___y_3084_ = v_trimProofs_3135_;
v___y_3085_ = v_solver_3132_;
v___y_3086_ = v___y_3149_;
v___y_3087_ = v_options_3155_;
v___y_3088_ = v___y_3150_;
v___y_3089_ = v___y_3151_;
v___y_3090_ = v_timeout_3134_;
v___y_3091_ = v___y_3152_;
goto v___jp_3069_;
}
}
else
{
lean_inc(v_timeout_3134_);
lean_inc_ref(v_solver_3132_);
lean_inc_ref(v_lratPath_3133_);
v___y_3070_ = v___y_3140_;
v___y_3071_ = v___y_3141_;
v___y_3072_ = v_solverMode_3138_;
v___y_3073_ = v___y_3143_;
v___y_3074_ = v___y_3142_;
v___y_3075_ = v_a_3159_;
v___y_3076_ = v___y_3144_;
v___y_3077_ = v_lratPath_3133_;
v___y_3078_ = v___x_3163_;
v___y_3079_ = v___y_3146_;
v___y_3080_ = v___y_3147_;
v___y_3081_ = v___y_3145_;
v___y_3082_ = v___y_3148_;
v___y_3083_ = v_binaryProofs_3136_;
v___y_3084_ = v_trimProofs_3135_;
v___y_3085_ = v_solver_3132_;
v___y_3086_ = v___y_3149_;
v___y_3087_ = v_options_3155_;
v___y_3088_ = v___y_3150_;
v___y_3089_ = v___y_3151_;
v___y_3090_ = v_timeout_3134_;
v___y_3091_ = v___y_3152_;
goto v___jp_3069_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v___y_3140_);
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
v___x_3195_ = lean_float_of_nat(v___y_3180_);
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
lean_inc(v___y_3176_);
v___x_3204_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3176_, v___x_2857_, v___x_2858_, v___y_3183_, v___y_3181_, v___y_3188_, v___f_2861_, v___x_3203_, v___y_3189_, v___y_3192_, v___y_3177_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3179_, v___y_3191_, v___y_3190_, v___y_3182_, v___y_3184_, v___y_3178_);
v___y_3140_ = v___y_3176_;
v___y_3141_ = v___y_3177_;
v___y_3142_ = v___y_3178_;
v___y_3143_ = v___y_3179_;
v___y_3144_ = v___y_3182_;
v___y_3145_ = v___y_3184_;
v___y_3146_ = v___y_3185_;
v___y_3147_ = v___y_3186_;
v___y_3148_ = v___y_3187_;
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
v___x_3225_ = lean_float_of_nat(v___y_3217_);
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
lean_inc(v___y_3206_);
v___x_3231_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3206_, v___x_2857_, v___x_2858_, v___y_3212_, v___y_3210_, v___y_3218_, v___f_2861_, v___x_3230_, v___y_3219_, v___y_3222_, v___y_3207_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3209_, v___y_3221_, v___y_3220_, v___y_3211_, v___y_3213_, v___y_3208_);
v___y_3140_ = v___y_3206_;
v___y_3141_ = v___y_3207_;
v___y_3142_ = v___y_3208_;
v___y_3143_ = v___y_3209_;
v___y_3144_ = v___y_3211_;
v___y_3145_ = v___y_3213_;
v___y_3146_ = v___y_3214_;
v___y_3147_ = v___y_3215_;
v___y_3148_ = v___y_3216_;
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
v___x_3249_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3236_);
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
v___x_3254_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3238_, v___x_2860_);
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
v___y_3178_ = v___y_3236_;
v___y_3179_ = v___y_3235_;
v___y_3180_ = v___x_3255_;
v___y_3181_ = v___y_3237_;
v___y_3182_ = v___y_3239_;
v___y_3183_ = v___y_3238_;
v___y_3184_ = v___y_3242_;
v___y_3185_ = v___y_3240_;
v___y_3186_ = v___y_3241_;
v___y_3187_ = v___y_3243_;
v___y_3188_ = v_a_3250_;
v___y_3189_ = v___y_3244_;
v___y_3190_ = v___y_3245_;
v___y_3191_ = v___y_3246_;
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
lean_inc(v___y_3247_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___y_3247_);
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
v___y_3178_ = v___y_3236_;
v___y_3179_ = v___y_3235_;
v___y_3180_ = v___x_3255_;
v___y_3181_ = v___y_3237_;
v___y_3182_ = v___y_3239_;
v___y_3183_ = v___y_3238_;
v___y_3184_ = v___y_3242_;
v___y_3185_ = v___y_3240_;
v___y_3186_ = v___y_3241_;
v___y_3187_ = v___y_3243_;
v___y_3188_ = v_a_3250_;
v___y_3189_ = v___y_3244_;
v___y_3190_ = v___y_3245_;
v___y_3191_ = v___y_3246_;
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
v___y_3208_ = v___y_3236_;
v___y_3209_ = v___y_3235_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3238_;
v___y_3213_ = v___y_3242_;
v___y_3214_ = v___y_3240_;
v___y_3215_ = v___y_3241_;
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___x_3279_;
v___y_3218_ = v_a_3250_;
v___y_3219_ = v___y_3244_;
v___y_3220_ = v___y_3245_;
v___y_3221_ = v___y_3246_;
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
lean_inc(v___y_3247_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___y_3247_);
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
v___y_3208_ = v___y_3236_;
v___y_3209_ = v___y_3235_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3238_;
v___y_3213_ = v___y_3242_;
v___y_3214_ = v___y_3240_;
v___y_3215_ = v___y_3241_;
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___x_3279_;
v___y_3218_ = v_a_3250_;
v___y_3219_ = v___y_3244_;
v___y_3220_ = v___y_3245_;
v___y_3221_ = v___y_3246_;
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
v___y_3140_ = v___x_3323_;
v___y_3141_ = v___y_3307_;
v___y_3142_ = v___y_3318_;
v___y_3143_ = v___y_3311_;
v___y_3144_ = v___y_3314_;
v___y_3145_ = v___y_3315_;
v___y_3146_ = v___y_3308_;
v___y_3147_ = v___y_3309_;
v___y_3148_ = v___y_3310_;
v___y_3149_ = v___y_3305_;
v___y_3150_ = v___y_3313_;
v___y_3151_ = v___y_3312_;
v___y_3152_ = v___y_3306_;
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
v___y_3140_ = v___x_3323_;
v___y_3141_ = v___y_3307_;
v___y_3142_ = v___y_3318_;
v___y_3143_ = v___y_3311_;
v___y_3144_ = v___y_3314_;
v___y_3145_ = v___y_3315_;
v___y_3146_ = v___y_3308_;
v___y_3147_ = v___y_3309_;
v___y_3148_ = v___y_3310_;
v___y_3149_ = v___y_3305_;
v___y_3150_ = v___y_3313_;
v___y_3151_ = v___y_3312_;
v___y_3152_ = v___y_3306_;
v___y_3153_ = v___x_3330_;
goto v___jp_3139_;
}
else
{
lean_dec_ref(v___f_2865_);
v___y_3233_ = v___x_3323_;
v___y_3234_ = v___y_3307_;
v___y_3235_ = v___y_3311_;
v___y_3236_ = v___y_3318_;
v___y_3237_ = v___x_3327_;
v___y_3238_ = v_options_3319_;
v___y_3239_ = v___y_3314_;
v___y_3240_ = v___y_3308_;
v___y_3241_ = v___y_3309_;
v___y_3242_ = v___y_3315_;
v___y_3243_ = v___y_3310_;
v___y_3244_ = v___y_3305_;
v___y_3245_ = v___y_3313_;
v___y_3246_ = v___y_3312_;
v___y_3247_ = v_ref_3317_;
v___y_3248_ = v___y_3306_;
goto v___jp_3232_;
}
}
else
{
lean_dec_ref(v___f_2865_);
v___y_3233_ = v___x_3323_;
v___y_3234_ = v___y_3307_;
v___y_3235_ = v___y_3311_;
v___y_3236_ = v___y_3318_;
v___y_3237_ = v___x_3327_;
v___y_3238_ = v_options_3319_;
v___y_3239_ = v___y_3314_;
v___y_3240_ = v___y_3308_;
v___y_3241_ = v___y_3309_;
v___y_3242_ = v___y_3315_;
v___y_3243_ = v___y_3310_;
v___y_3244_ = v___y_3305_;
v___y_3245_ = v___y_3313_;
v___y_3246_ = v___y_3312_;
v___y_3247_ = v_ref_3317_;
v___y_3248_ = v___y_3306_;
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
uint8_t v___x_654956__boxed_3380_; lean_object* v_res_3381_; 
v___x_654956__boxed_3380_ = lean_unbox(v___x_3356_);
v_res_3381_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_3350_, v_aig_3351_, v_goal_3352_, v_unusedHypotheses_3353_, v_reflectionResult_3354_, v_satExpr_3355_, v___x_654956__boxed_3380_, v___x_3357_, v___f_3358_, v___x_3359_, v___f_3360_, v___f_3361_, v___x_3362_, v___x_3363_, v___f_3364_, v_a_3365_, v_____r_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9(lean_object* v_aig_3382_, lean_object* v___x_3383_, lean_object* v_a_3384_, lean_object* v_ref_3385_, uint8_t v___x_3386_, lean_object* v_x_3387_){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v_state_3390_; lean_object* v_cnf_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3412_; 
v___x_3388_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
v___x_3389_ = l_Std_Sat_AIG_toCNF_State_empty___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__0(v_aig_3382_);
v_state_3390_ = l_Std_Sat_AIG_toCNF_x27___redArg(v___x_3383_, v___x_3388_, v_a_3384_, v___x_3389_);
lean_dec_ref(v___x_3388_);
v_cnf_3391_ = lean_ctor_get(v_state_3390_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_state_3390_);
if (v_isSharedCheck_3412_ == 0)
{
lean_object* v_unused_3413_; 
v_unused_3413_ = lean_ctor_get(v_state_3390_, 1);
lean_dec(v_unused_3413_);
v___x_3393_ = v_state_3390_;
v_isShared_3394_ = v_isSharedCheck_3412_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_cnf_3391_);
lean_dec(v_state_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3412_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v_gate_3395_; uint8_t v_invert_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___y_3400_; uint8_t v___y_3401_; 
v_gate_3395_ = lean_ctor_get(v_ref_3385_, 0);
lean_inc(v_gate_3395_);
v_invert_3396_ = lean_ctor_get_uint8(v_ref_3385_, sizeof(void*)*1);
lean_dec_ref(v_ref_3385_);
v___x_3397_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___closed__0));
v___x_3398_ = l_ByteArray_empty;
if (v_invert_3396_ == 0)
{
if (v___x_3386_ == 0)
{
goto v___jp_3407_;
}
else
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = lean_array_push(v___x_3397_, v_gate_3395_);
v___x_3411_ = 1;
v___y_3400_ = v___x_3410_;
v___y_3401_ = v___x_3411_;
goto v___jp_3399_;
}
}
else
{
goto v___jp_3407_;
}
v___jp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3402_ = lean_byte_array_push(v___x_3398_, v___y_3401_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v___x_3402_);
lean_ctor_set(v___x_3393_, 0, v___y_3400_);
v___x_3404_ = v___x_3393_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___y_3400_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_array_push(v_cnf_3391_, v___x_3404_);
return v___x_3405_;
}
}
v___jp_3407_:
{
lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3408_ = lean_array_push(v___x_3397_, v_gate_3395_);
v___x_3409_ = 0;
v___y_3400_ = v___x_3408_;
v___y_3401_ = v___x_3409_;
goto v___jp_3399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9___boxed(lean_object* v_aig_3414_, lean_object* v___x_3415_, lean_object* v_a_3416_, lean_object* v_ref_3417_, lean_object* v___x_3418_, lean_object* v_x_3419_){
_start:
{
uint8_t v___x_655932__boxed_3420_; lean_object* v_res_3421_; 
v___x_655932__boxed_3420_ = lean_unbox(v___x_3418_);
v_res_3421_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9(v_aig_3414_, v___x_3415_, v_a_3416_, v_ref_3417_, v___x_655932__boxed_3420_, v_x_3419_);
lean_dec_ref(v___x_3415_);
lean_dec_ref(v_aig_3414_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(lean_object* v_ctx_3422_, lean_object* v_aig_3423_, lean_object* v_goal_3424_, lean_object* v_unusedHypotheses_3425_, lean_object* v_reflectionResult_3426_, lean_object* v_satExpr_3427_, uint8_t v___x_3428_, lean_object* v___x_3429_, lean_object* v___f_3430_, lean_object* v___x_3431_, lean_object* v___f_3432_, lean_object* v___f_3433_, lean_object* v___x_3434_, lean_object* v___x_3435_, lean_object* v___f_3436_, lean_object* v_a_3437_, lean_object* v_____r_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; uint8_t v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v_a_3601_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; uint8_t v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v_a_3628_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; uint8_t v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; uint8_t v___y_3650_; uint8_t v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; uint8_t v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v_config_3702_; lean_object* v_solver_3703_; lean_object* v_lratPath_3704_; lean_object* v_timeout_3705_; uint8_t v_trimProofs_3706_; uint8_t v_binaryProofs_3707_; uint8_t v_graphviz_3708_; uint8_t v_solverMode_3709_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; uint8_t v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v_a_3764_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; uint8_t v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v_a_3794_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; uint8_t v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v_toCold_3887_; lean_object* v_ref_3888_; lean_object* v___y_3889_; 
v_config_3702_ = lean_ctor_get(v_ctx_3422_, 5);
v_solver_3703_ = lean_ctor_get(v_ctx_3422_, 3);
v_lratPath_3704_ = lean_ctor_get(v_ctx_3422_, 4);
v_timeout_3705_ = lean_ctor_get(v_config_3702_, 0);
v_trimProofs_3706_ = lean_ctor_get_uint8(v_config_3702_, sizeof(void*)*3);
v_binaryProofs_3707_ = lean_ctor_get_uint8(v_config_3702_, sizeof(void*)*3 + 1);
v_graphviz_3708_ = lean_ctor_get_uint8(v_config_3702_, sizeof(void*)*3 + 8);
v_solverMode_3709_ = lean_ctor_get_uint8(v_config_3702_, sizeof(void*)*3 + 10);
if (v_graphviz_3708_ == 0)
{
lean_object* v_toCold_3902_; lean_object* v_ref_3903_; 
lean_dec_ref(v_a_3437_);
v_toCold_3902_ = lean_ctor_get(v___y_3449_, 0);
v_ref_3903_ = lean_ctor_get(v___y_3449_, 2);
v___y_3876_ = v___y_3439_;
v___y_3877_ = v___y_3440_;
v___y_3878_ = v___y_3441_;
v___y_3879_ = v___y_3442_;
v___y_3880_ = v___y_3443_;
v___y_3881_ = v___y_3444_;
v___y_3882_ = v___y_3445_;
v___y_3883_ = v___y_3446_;
v___y_3884_ = v___y_3447_;
v___y_3885_ = v___y_3448_;
v___y_3886_ = v___y_3449_;
v_toCold_3887_ = v_toCold_3902_;
v_ref_3888_ = v_ref_3903_;
v___y_3889_ = v___y_3450_;
goto v___jp_3875_;
}
else
{
lean_object* v_toCold_3904_; lean_object* v_ref_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v_toCold_3904_ = lean_ctor_get(v___y_3449_, 0);
v_ref_3905_ = lean_ctor_get(v___y_3449_, 2);
v___x_3906_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_3907_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v_a_3437_);
v___x_3908_ = l_IO_FS_writeFile(v___x_3906_, v___x_3907_);
lean_dec_ref(v___x_3907_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_dec_ref_known(v___x_3908_, 1);
v___y_3876_ = v___y_3439_;
v___y_3877_ = v___y_3440_;
v___y_3878_ = v___y_3441_;
v___y_3879_ = v___y_3442_;
v___y_3880_ = v___y_3443_;
v___y_3881_ = v___y_3444_;
v___y_3882_ = v___y_3445_;
v___y_3883_ = v___y_3446_;
v___y_3884_ = v___y_3447_;
v___y_3885_ = v___y_3448_;
v___y_3886_ = v___y_3449_;
v_toCold_3887_ = v_toCold_3904_;
v_ref_3888_ = v_ref_3905_;
v___y_3889_ = v___y_3450_;
goto v___jp_3875_;
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3920_; 
lean_dec_ref(v___f_3436_);
lean_dec_ref(v___x_3435_);
lean_dec_ref(v___x_3434_);
lean_dec_ref(v___f_3433_);
lean_dec_ref(v___f_3432_);
lean_dec_ref(v___f_3430_);
lean_dec_ref(v___x_3429_);
lean_dec_ref(v_satExpr_3427_);
lean_dec_ref(v_reflectionResult_3426_);
lean_dec_ref(v_unusedHypotheses_3425_);
lean_dec(v_goal_3424_);
lean_dec_ref(v_aig_3423_);
lean_dec_ref(v_ctx_3422_);
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3911_ = v___x_3908_;
v_isShared_3912_ = v_isSharedCheck_3920_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3908_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3920_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3913_ = lean_io_error_to_string(v_a_3909_);
v___x_3914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
v___x_3915_ = l_Lean_MessageData_ofFormat(v___x_3914_);
lean_inc(v_ref_3905_);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v_ref_3905_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v___x_3916_);
v___x_3918_ = v___x_3911_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
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
v___jp_3452_:
{
lean_object* v___x_3465_; 
lean_inc_ref(v___y_3453_);
v___x_3465_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_3453_, v_ctx_3422_, v_reflectionResult_3426_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_3427_, v_a_3466_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3477_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v___x_3469_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_3424_, v_a_3468_, v___y_3462_);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3469_, 0);
lean_dec(v_unused_3478_);
v___x_3471_ = v___x_3469_;
v_isShared_3472_ = v_isSharedCheck_3477_;
goto v_resetjp_3470_;
}
else
{
lean_dec(v___x_3469_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3477_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v___y_3453_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3473_);
v___x_3475_ = v___x_3471_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref(v___y_3453_);
lean_dec(v_goal_3424_);
v_a_3479_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3467_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3467_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref(v___y_3453_);
lean_dec_ref(v_satExpr_3427_);
lean_dec(v_goal_3424_);
v_a_3487_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3465_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3465_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
v___jp_3495_:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_3497_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3513_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3513_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3513_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3503_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v_aig_3423_, v___y_3496_, v_a_3499_);
lean_dec(v_a_3499_);
lean_dec_ref(v___y_3496_);
v___x_3504_ = lean_unsigned_to_nat(0u);
v___x_3505_ = lean_array_get_size(v___x_3503_);
v___x_3506_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_3503_, v___x_3504_, v___x_3505_);
lean_dec_ref(v___x_3503_);
v___x_3507_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_3508_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3508_, 0, v_goal_3424_);
lean_ctor_set(v___x_3508_, 1, v_unusedHypotheses_3425_);
lean_ctor_set(v___x_3508_, 2, v___x_3506_);
lean_ctor_set(v___x_3508_, 3, v___x_3507_);
v___x_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v___x_3509_);
v___x_3511_ = v___x_3501_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec_ref(v___y_3496_);
lean_dec_ref(v_unusedHypotheses_3425_);
lean_dec(v_goal_3424_);
lean_dec_ref(v_aig_3423_);
v_a_3514_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3498_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3498_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
v___jp_3522_:
{
if (lean_obj_tag(v___y_3535_) == 0)
{
lean_object* v_a_3536_; 
v_a_3536_ = lean_ctor_get(v___y_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___y_3535_, 1);
if (lean_obj_tag(v_a_3536_) == 0)
{
lean_object* v_toCold_3537_; lean_object* v_options_3538_; uint8_t v_hasTrace_3539_; 
lean_dec_ref(v_satExpr_3427_);
lean_dec_ref(v_reflectionResult_3426_);
lean_dec_ref(v_ctx_3422_);
v_toCold_3537_ = lean_ctor_get(v___y_3530_, 0);
v_options_3538_ = lean_ctor_get(v_toCold_3537_, 2);
v_hasTrace_3539_ = lean_ctor_get_uint8(v_options_3538_, sizeof(void*)*1);
if (v_hasTrace_3539_ == 0)
{
lean_object* v_a_3540_; 
lean_dec(v___y_3534_);
v_a_3540_ = lean_ctor_get(v_a_3536_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v_a_3536_, 1);
v___y_3496_ = v_a_3540_;
v___y_3497_ = v___y_3533_;
goto v___jp_3495_;
}
else
{
lean_object* v_a_3541_; lean_object* v_inheritedTraceOptions_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_a_3541_ = lean_ctor_get(v_a_3536_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v_a_3536_, 1);
v_inheritedTraceOptions_3542_ = lean_ctor_get(v_toCold_3537_, 11);
v___x_3543_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3534_);
v___x_3544_ = l_Lean_Name_append(v___x_3543_, v___y_3534_);
v___x_3545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3542_, v_options_3538_, v___x_3544_);
lean_dec(v___x_3544_);
if (v___x_3545_ == 0)
{
lean_dec(v___y_3534_);
v___y_3496_ = v_a_3541_;
v___y_3497_ = v___y_3533_;
goto v___jp_3495_;
}
else
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
v___x_3547_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3534_, v___x_3546_, v___y_3529_, v___y_3527_, v___y_3530_, v___y_3523_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref_known(v___x_3547_, 1);
v___y_3496_ = v_a_3541_;
v___y_3497_ = v___y_3533_;
goto v___jp_3495_;
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec(v_a_3541_);
lean_dec_ref(v_unusedHypotheses_3425_);
lean_dec(v_goal_3424_);
lean_dec_ref(v_aig_3423_);
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3547_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3556_; lean_object* v_options_3557_; uint8_t v_hasTrace_3558_; 
lean_dec_ref(v_unusedHypotheses_3425_);
lean_dec_ref(v_aig_3423_);
v_toCold_3556_ = lean_ctor_get(v___y_3530_, 0);
v_options_3557_ = lean_ctor_get(v_toCold_3556_, 2);
v_hasTrace_3558_ = lean_ctor_get_uint8(v_options_3557_, sizeof(void*)*1);
if (v_hasTrace_3558_ == 0)
{
lean_object* v_a_3559_; 
lean_dec(v___y_3534_);
v_a_3559_ = lean_ctor_get(v_a_3536_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v_a_3536_, 1);
v___y_3453_ = v_a_3559_;
v___y_3454_ = v___y_3526_;
v___y_3455_ = v___y_3533_;
v___y_3456_ = v___y_3524_;
v___y_3457_ = v___y_3531_;
v___y_3458_ = v___y_3532_;
v___y_3459_ = v___y_3525_;
v___y_3460_ = v___y_3528_;
v___y_3461_ = v___y_3529_;
v___y_3462_ = v___y_3527_;
v___y_3463_ = v___y_3530_;
v___y_3464_ = v___y_3523_;
goto v___jp_3452_;
}
else
{
lean_object* v_a_3560_; lean_object* v_inheritedTraceOptions_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_a_3560_ = lean_ctor_get(v_a_3536_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v_a_3536_, 1);
v_inheritedTraceOptions_3561_ = lean_ctor_get(v_toCold_3556_, 11);
v___x_3562_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3534_);
v___x_3563_ = l_Lean_Name_append(v___x_3562_, v___y_3534_);
v___x_3564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3561_, v_options_3557_, v___x_3563_);
lean_dec(v___x_3563_);
if (v___x_3564_ == 0)
{
lean_dec(v___y_3534_);
v___y_3453_ = v_a_3560_;
v___y_3454_ = v___y_3526_;
v___y_3455_ = v___y_3533_;
v___y_3456_ = v___y_3524_;
v___y_3457_ = v___y_3531_;
v___y_3458_ = v___y_3532_;
v___y_3459_ = v___y_3525_;
v___y_3460_ = v___y_3528_;
v___y_3461_ = v___y_3529_;
v___y_3462_ = v___y_3527_;
v___y_3463_ = v___y_3530_;
v___y_3464_ = v___y_3523_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
v___x_3566_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_3534_, v___x_3565_, v___y_3529_, v___y_3527_, v___y_3530_, v___y_3523_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_dec_ref_known(v___x_3566_, 1);
v___y_3453_ = v_a_3560_;
v___y_3454_ = v___y_3526_;
v___y_3455_ = v___y_3533_;
v___y_3456_ = v___y_3524_;
v___y_3457_ = v___y_3531_;
v___y_3458_ = v___y_3532_;
v___y_3459_ = v___y_3525_;
v___y_3460_ = v___y_3528_;
v___y_3461_ = v___y_3529_;
v___y_3462_ = v___y_3527_;
v___y_3463_ = v___y_3530_;
v___y_3464_ = v___y_3523_;
goto v___jp_3452_;
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_a_3560_);
lean_dec_ref(v_satExpr_3427_);
lean_dec_ref(v_reflectionResult_3426_);
lean_dec(v_goal_3424_);
lean_dec_ref(v_ctx_3422_);
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v___y_3534_);
lean_dec_ref(v_satExpr_3427_);
lean_dec_ref(v_reflectionResult_3426_);
lean_dec_ref(v_unusedHypotheses_3425_);
lean_dec(v_goal_3424_);
lean_dec_ref(v_aig_3423_);
lean_dec_ref(v_ctx_3422_);
v_a_3575_ = lean_ctor_get(v___y_3535_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___y_3535_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___y_3535_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___y_3535_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
v___jp_3583_:
{
lean_object* v___x_3602_; double v___x_3603_; double v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3602_ = lean_io_get_num_heartbeats();
v___x_3603_ = lean_float_of_nat(v___y_3594_);
v___x_3604_ = lean_float_of_nat(v___x_3602_);
v___x_3605_ = lean_box_float(v___x_3603_);
v___x_3606_ = lean_box_float(v___x_3604_);
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v_a_3601_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
lean_inc(v___y_3599_);
v___x_3609_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3599_, v___x_3428_, v___x_3429_, v___y_3596_, v___y_3589_, v___y_3590_, v___f_3430_, v___x_3608_, v___y_3597_, v___y_3588_, v___y_3600_, v___y_3585_, v___y_3595_, v___y_3598_, v___y_3586_, v___y_3591_, v___y_3592_, v___y_3587_, v___y_3593_, v___y_3584_);
v___y_3523_ = v___y_3584_;
v___y_3524_ = v___y_3585_;
v___y_3525_ = v___y_3586_;
v___y_3526_ = v___y_3588_;
v___y_3527_ = v___y_3587_;
v___y_3528_ = v___y_3591_;
v___y_3529_ = v___y_3592_;
v___y_3530_ = v___y_3593_;
v___y_3531_ = v___y_3595_;
v___y_3532_ = v___y_3598_;
v___y_3533_ = v___y_3600_;
v___y_3534_ = v___y_3599_;
v___y_3535_ = v___x_3609_;
goto v___jp_3522_;
}
v___jp_3610_:
{
lean_object* v___x_3629_; double v___x_3630_; double v___x_3631_; double v___x_3632_; double v___x_3633_; double v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3629_ = lean_io_mono_nanos_now();
v___x_3630_ = lean_float_of_nat(v___y_3611_);
v___x_3631_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3632_ = lean_float_div(v___x_3630_, v___x_3631_);
v___x_3633_ = lean_float_of_nat(v___x_3629_);
v___x_3634_ = lean_float_div(v___x_3633_, v___x_3631_);
v___x_3635_ = lean_box_float(v___x_3632_);
v___x_3636_ = lean_box_float(v___x_3634_);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3635_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v_a_3628_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
lean_inc(v___y_3626_);
v___x_3639_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_3626_, v___x_3428_, v___x_3429_, v___y_3623_, v___y_3617_, v___y_3618_, v___f_3430_, v___x_3638_, v___y_3624_, v___y_3616_, v___y_3627_, v___y_3613_, v___y_3622_, v___y_3625_, v___y_3614_, v___y_3619_, v___y_3620_, v___y_3615_, v___y_3621_, v___y_3612_);
v___y_3523_ = v___y_3612_;
v___y_3524_ = v___y_3613_;
v___y_3525_ = v___y_3614_;
v___y_3526_ = v___y_3616_;
v___y_3527_ = v___y_3615_;
v___y_3528_ = v___y_3619_;
v___y_3529_ = v___y_3620_;
v___y_3530_ = v___y_3621_;
v___y_3531_ = v___y_3622_;
v___y_3532_ = v___y_3625_;
v___y_3533_ = v___y_3627_;
v___y_3534_ = v___y_3626_;
v___y_3535_ = v___x_3639_;
goto v___jp_3522_;
}
v___jp_3640_:
{
lean_object* v___x_3663_; lean_object* v_a_3664_; uint8_t v___x_3665_; 
v___x_3663_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3642_);
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref(v___x_3663_);
v___x_3665_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3658_, v___x_3431_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_io_mono_nanos_now();
v___x_3667_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3644_, v___y_3646_, v___y_3654_, v___y_3647_, v___y_3641_, v___y_3656_, v___y_3651_, v___y_3655_, v___y_3642_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set_tag(v___x_3670_, 1);
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
v___y_3611_ = v___x_3666_;
v___y_3612_ = v___y_3642_;
v___y_3613_ = v___y_3643_;
v___y_3614_ = v___y_3645_;
v___y_3615_ = v___y_3649_;
v___y_3616_ = v___y_3648_;
v___y_3617_ = v___y_3650_;
v___y_3618_ = v_a_3664_;
v___y_3619_ = v___y_3652_;
v___y_3620_ = v___y_3653_;
v___y_3621_ = v___y_3655_;
v___y_3622_ = v___y_3657_;
v___y_3623_ = v___y_3658_;
v___y_3624_ = v___y_3659_;
v___y_3625_ = v___y_3660_;
v___y_3626_ = v___y_3661_;
v___y_3627_ = v___y_3662_;
v_a_3628_ = v___x_3673_;
goto v___jp_3610_;
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
v_a_3676_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3667_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3667_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 0);
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
v___y_3611_ = v___x_3666_;
v___y_3612_ = v___y_3642_;
v___y_3613_ = v___y_3643_;
v___y_3614_ = v___y_3645_;
v___y_3615_ = v___y_3649_;
v___y_3616_ = v___y_3648_;
v___y_3617_ = v___y_3650_;
v___y_3618_ = v_a_3664_;
v___y_3619_ = v___y_3652_;
v___y_3620_ = v___y_3653_;
v___y_3621_ = v___y_3655_;
v___y_3622_ = v___y_3657_;
v___y_3623_ = v___y_3658_;
v___y_3624_ = v___y_3659_;
v___y_3625_ = v___y_3660_;
v___y_3626_ = v___y_3661_;
v___y_3627_ = v___y_3662_;
v_a_3628_ = v___x_3681_;
goto v___jp_3610_;
}
}
}
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_io_get_num_heartbeats();
v___x_3685_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_3644_, v___y_3646_, v___y_3654_, v___y_3647_, v___y_3641_, v___y_3656_, v___y_3651_, v___y_3655_, v___y_3642_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3685_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3685_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
lean_ctor_set_tag(v___x_3688_, 1);
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
v___y_3584_ = v___y_3642_;
v___y_3585_ = v___y_3643_;
v___y_3586_ = v___y_3645_;
v___y_3587_ = v___y_3649_;
v___y_3588_ = v___y_3648_;
v___y_3589_ = v___y_3650_;
v___y_3590_ = v_a_3664_;
v___y_3591_ = v___y_3652_;
v___y_3592_ = v___y_3653_;
v___y_3593_ = v___y_3655_;
v___y_3594_ = v___x_3684_;
v___y_3595_ = v___y_3657_;
v___y_3596_ = v___y_3658_;
v___y_3597_ = v___y_3659_;
v___y_3598_ = v___y_3660_;
v___y_3599_ = v___y_3661_;
v___y_3600_ = v___y_3662_;
v_a_3601_ = v___x_3691_;
goto v___jp_3583_;
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_a_3694_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3685_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3685_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set_tag(v___x_3696_, 0);
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
v___y_3584_ = v___y_3642_;
v___y_3585_ = v___y_3643_;
v___y_3586_ = v___y_3645_;
v___y_3587_ = v___y_3649_;
v___y_3588_ = v___y_3648_;
v___y_3589_ = v___y_3650_;
v___y_3590_ = v_a_3664_;
v___y_3591_ = v___y_3652_;
v___y_3592_ = v___y_3653_;
v___y_3593_ = v___y_3655_;
v___y_3594_ = v___x_3684_;
v___y_3595_ = v___y_3657_;
v___y_3596_ = v___y_3658_;
v___y_3597_ = v___y_3659_;
v___y_3598_ = v___y_3660_;
v___y_3599_ = v___y_3661_;
v___y_3600_ = v___y_3662_;
v_a_3601_ = v___x_3699_;
goto v___jp_3583_;
}
}
}
}
}
v___jp_3710_:
{
if (lean_obj_tag(v___y_3724_) == 0)
{
lean_object* v_toCold_3725_; lean_object* v_options_3726_; uint8_t v_hasTrace_3727_; 
v_toCold_3725_ = lean_ctor_get(v___y_3718_, 0);
v_options_3726_ = lean_ctor_get(v_toCold_3725_, 2);
v_hasTrace_3727_ = lean_ctor_get_uint8(v_options_3726_, sizeof(void*)*1);
if (v_hasTrace_3727_ == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
lean_dec_ref(v___f_3430_);
lean_dec_ref(v___x_3429_);
v_a_3728_ = lean_ctor_get(v___y_3724_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___y_3724_, 1);
lean_inc(v_timeout_3705_);
lean_inc_ref(v_lratPath_3704_);
lean_inc_ref(v_solver_3703_);
v___x_3729_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3728_, v_solver_3703_, v_lratPath_3704_, v_trimProofs_3706_, v_timeout_3705_, v_binaryProofs_3707_, v_solverMode_3709_, v___y_3718_, v___y_3711_);
v___y_3523_ = v___y_3711_;
v___y_3524_ = v___y_3712_;
v___y_3525_ = v___y_3713_;
v___y_3526_ = v___y_3714_;
v___y_3527_ = v___y_3715_;
v___y_3528_ = v___y_3716_;
v___y_3529_ = v___y_3717_;
v___y_3530_ = v___y_3718_;
v___y_3531_ = v___y_3719_;
v___y_3532_ = v___y_3721_;
v___y_3533_ = v___y_3722_;
v___y_3534_ = v___y_3723_;
v___y_3535_ = v___x_3729_;
goto v___jp_3522_;
}
else
{
lean_object* v_a_3730_; lean_object* v_inheritedTraceOptions_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v_a_3730_ = lean_ctor_get(v___y_3724_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___y_3724_, 1);
v_inheritedTraceOptions_3731_ = lean_ctor_get(v_toCold_3725_, 11);
v___x_3732_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_3723_);
v___x_3733_ = l_Lean_Name_append(v___x_3732_, v___y_3723_);
v___x_3734_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3731_, v_options_3726_, v___x_3733_);
lean_dec(v___x_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3735_ = l_Lean_trace_profiler;
v___x_3736_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3726_, v___x_3735_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; 
lean_dec_ref(v___f_3430_);
lean_dec_ref(v___x_3429_);
lean_inc(v_timeout_3705_);
lean_inc_ref(v_lratPath_3704_);
lean_inc_ref(v_solver_3703_);
v___x_3737_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_3730_, v_solver_3703_, v_lratPath_3704_, v_trimProofs_3706_, v_timeout_3705_, v_binaryProofs_3707_, v_solverMode_3709_, v___y_3718_, v___y_3711_);
v___y_3523_ = v___y_3711_;
v___y_3524_ = v___y_3712_;
v___y_3525_ = v___y_3713_;
v___y_3526_ = v___y_3714_;
v___y_3527_ = v___y_3715_;
v___y_3528_ = v___y_3716_;
v___y_3529_ = v___y_3717_;
v___y_3530_ = v___y_3718_;
v___y_3531_ = v___y_3719_;
v___y_3532_ = v___y_3721_;
v___y_3533_ = v___y_3722_;
v___y_3534_ = v___y_3723_;
v___y_3535_ = v___x_3737_;
goto v___jp_3522_;
}
else
{
lean_inc_ref(v_lratPath_3704_);
lean_inc_ref(v_solver_3703_);
lean_inc(v_timeout_3705_);
v___y_3641_ = v_timeout_3705_;
v___y_3642_ = v___y_3711_;
v___y_3643_ = v___y_3712_;
v___y_3644_ = v_a_3730_;
v___y_3645_ = v___y_3713_;
v___y_3646_ = v_solver_3703_;
v___y_3647_ = v_trimProofs_3706_;
v___y_3648_ = v___y_3714_;
v___y_3649_ = v___y_3715_;
v___y_3650_ = v___x_3734_;
v___y_3651_ = v_solverMode_3709_;
v___y_3652_ = v___y_3716_;
v___y_3653_ = v___y_3717_;
v___y_3654_ = v_lratPath_3704_;
v___y_3655_ = v___y_3718_;
v___y_3656_ = v_binaryProofs_3707_;
v___y_3657_ = v___y_3719_;
v___y_3658_ = v_options_3726_;
v___y_3659_ = v___y_3720_;
v___y_3660_ = v___y_3721_;
v___y_3661_ = v___y_3723_;
v___y_3662_ = v___y_3722_;
goto v___jp_3640_;
}
}
else
{
lean_inc_ref(v_lratPath_3704_);
lean_inc_ref(v_solver_3703_);
lean_inc(v_timeout_3705_);
v___y_3641_ = v_timeout_3705_;
v___y_3642_ = v___y_3711_;
v___y_3643_ = v___y_3712_;
v___y_3644_ = v_a_3730_;
v___y_3645_ = v___y_3713_;
v___y_3646_ = v_solver_3703_;
v___y_3647_ = v_trimProofs_3706_;
v___y_3648_ = v___y_3714_;
v___y_3649_ = v___y_3715_;
v___y_3650_ = v___x_3734_;
v___y_3651_ = v_solverMode_3709_;
v___y_3652_ = v___y_3716_;
v___y_3653_ = v___y_3717_;
v___y_3654_ = v_lratPath_3704_;
v___y_3655_ = v___y_3718_;
v___y_3656_ = v_binaryProofs_3707_;
v___y_3657_ = v___y_3719_;
v___y_3658_ = v_options_3726_;
v___y_3659_ = v___y_3720_;
v___y_3660_ = v___y_3721_;
v___y_3661_ = v___y_3723_;
v___y_3662_ = v___y_3722_;
goto v___jp_3640_;
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v___y_3723_);
lean_dec_ref(v___f_3430_);
lean_dec_ref(v___x_3429_);
lean_dec_ref(v_satExpr_3427_);
lean_dec_ref(v_reflectionResult_3426_);
lean_dec_ref(v_unusedHypotheses_3425_);
lean_dec(v_goal_3424_);
lean_dec_ref(v_aig_3423_);
lean_dec_ref(v_ctx_3422_);
v_a_3738_ = lean_ctor_get(v___y_3724_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___y_3724_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___y_3724_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___y_3724_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
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
v___jp_3746_:
{
lean_object* v___x_3765_; double v___x_3766_; double v___x_3767_; double v___x_3768_; double v___x_3769_; double v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3765_ = lean_io_mono_nanos_now();
v___x_3766_ = lean_float_of_nat(v___y_3749_);
v___x_3767_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_3768_ = lean_float_div(v___x_3766_, v___x_3767_);
v___x_3769_ = lean_float_of_nat(v___x_3765_);
v___x_3770_ = lean_float_div(v___x_3769_, v___x_3767_);
v___x_3771_ = lean_box_float(v___x_3768_);
v___x_3772_ = lean_box_float(v___x_3770_);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_a_3764_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
lean_inc_ref(v___x_3429_);
lean_inc(v___y_3761_);
v___x_3775_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3761_, v___x_3428_, v___x_3429_, v___y_3747_, v___y_3754_, v___y_3763_, v___f_3432_, v___x_3774_, v___y_3759_, v___y_3753_, v___y_3762_, v___y_3750_, v___y_3758_, v___y_3760_, v___y_3751_, v___y_3755_, v___y_3756_, v___y_3752_, v___y_3757_, v___y_3748_);
v___y_3711_ = v___y_3748_;
v___y_3712_ = v___y_3750_;
v___y_3713_ = v___y_3751_;
v___y_3714_ = v___y_3753_;
v___y_3715_ = v___y_3752_;
v___y_3716_ = v___y_3755_;
v___y_3717_ = v___y_3756_;
v___y_3718_ = v___y_3757_;
v___y_3719_ = v___y_3758_;
v___y_3720_ = v___y_3759_;
v___y_3721_ = v___y_3760_;
v___y_3722_ = v___y_3762_;
v___y_3723_ = v___y_3761_;
v___y_3724_ = v___x_3775_;
goto v___jp_3710_;
}
v___jp_3776_:
{
lean_object* v___x_3795_; double v___x_3796_; double v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3795_ = lean_io_get_num_heartbeats();
v___x_3796_ = lean_float_of_nat(v___y_3790_);
v___x_3797_ = lean_float_of_nat(v___x_3795_);
v___x_3798_ = lean_box_float(v___x_3796_);
v___x_3799_ = lean_box_float(v___x_3797_);
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v_a_3794_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
lean_inc_ref(v___x_3429_);
lean_inc(v___y_3791_);
v___x_3802_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_3791_, v___x_3428_, v___x_3429_, v___y_3777_, v___y_3783_, v___y_3793_, v___f_3432_, v___x_3801_, v___y_3788_, v___y_3782_, v___y_3792_, v___y_3779_, v___y_3787_, v___y_3789_, v___y_3780_, v___y_3784_, v___y_3785_, v___y_3781_, v___y_3786_, v___y_3778_);
v___y_3711_ = v___y_3778_;
v___y_3712_ = v___y_3779_;
v___y_3713_ = v___y_3780_;
v___y_3714_ = v___y_3782_;
v___y_3715_ = v___y_3781_;
v___y_3716_ = v___y_3784_;
v___y_3717_ = v___y_3785_;
v___y_3718_ = v___y_3786_;
v___y_3719_ = v___y_3787_;
v___y_3720_ = v___y_3788_;
v___y_3721_ = v___y_3789_;
v___y_3722_ = v___y_3792_;
v___y_3723_ = v___y_3791_;
v___y_3724_ = v___x_3802_;
goto v___jp_3710_;
}
v___jp_3803_:
{
lean_object* v___x_3820_; lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3874_; 
v___x_3820_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_3805_);
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3823_ = v___x_3820_;
v_isShared_3824_ = v_isSharedCheck_3874_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3820_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3874_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
uint8_t v___x_3825_; 
v___x_3825_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_3804_, v___x_3431_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = lean_io_mono_nanos_now();
v___x_3827_ = l_IO_lazyPure___redArg(v___f_3433_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3823_);
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set_tag(v___x_3830_, 1);
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
v___y_3747_ = v___y_3804_;
v___y_3748_ = v___y_3805_;
v___y_3749_ = v___x_3826_;
v___y_3750_ = v___y_3807_;
v___y_3751_ = v___y_3808_;
v___y_3752_ = v___y_3810_;
v___y_3753_ = v___y_3809_;
v___y_3754_ = v___y_3811_;
v___y_3755_ = v___y_3812_;
v___y_3756_ = v___y_3813_;
v___y_3757_ = v___y_3814_;
v___y_3758_ = v___y_3815_;
v___y_3759_ = v___y_3816_;
v___y_3760_ = v___y_3817_;
v___y_3761_ = v___y_3818_;
v___y_3762_ = v___y_3819_;
v___y_3763_ = v_a_3821_;
v_a_3764_ = v___x_3833_;
goto v___jp_3746_;
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3849_; 
v_a_3836_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3838_ = v___x_3827_;
v_isShared_3839_ = v_isSharedCheck_3849_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3827_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3849_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3840_ = lean_io_error_to_string(v_a_3836_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set_tag(v___x_3838_, 3);
lean_ctor_set(v___x_3838_, 0, v___x_3840_);
v___x_3842_ = v___x_3838_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3846_; 
v___x_3843_ = l_Lean_MessageData_ofFormat(v___x_3842_);
lean_inc(v___y_3806_);
v___x_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___y_3806_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v___x_3844_);
v___x_3846_ = v___x_3823_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
v___y_3747_ = v___y_3804_;
v___y_3748_ = v___y_3805_;
v___y_3749_ = v___x_3826_;
v___y_3750_ = v___y_3807_;
v___y_3751_ = v___y_3808_;
v___y_3752_ = v___y_3810_;
v___y_3753_ = v___y_3809_;
v___y_3754_ = v___y_3811_;
v___y_3755_ = v___y_3812_;
v___y_3756_ = v___y_3813_;
v___y_3757_ = v___y_3814_;
v___y_3758_ = v___y_3815_;
v___y_3759_ = v___y_3816_;
v___y_3760_ = v___y_3817_;
v___y_3761_ = v___y_3818_;
v___y_3762_ = v___y_3819_;
v___y_3763_ = v_a_3821_;
v_a_3764_ = v___x_3846_;
goto v___jp_3746_;
}
}
}
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = lean_io_get_num_heartbeats();
v___x_3851_ = l_IO_lazyPure___redArg(v___f_3433_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_del_object(v___x_3823_);
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3851_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3851_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set_tag(v___x_3854_, 1);
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
v___y_3777_ = v___y_3804_;
v___y_3778_ = v___y_3805_;
v___y_3779_ = v___y_3807_;
v___y_3780_ = v___y_3808_;
v___y_3781_ = v___y_3810_;
v___y_3782_ = v___y_3809_;
v___y_3783_ = v___y_3811_;
v___y_3784_ = v___y_3812_;
v___y_3785_ = v___y_3813_;
v___y_3786_ = v___y_3814_;
v___y_3787_ = v___y_3815_;
v___y_3788_ = v___y_3816_;
v___y_3789_ = v___y_3817_;
v___y_3790_ = v___x_3850_;
v___y_3791_ = v___y_3818_;
v___y_3792_ = v___y_3819_;
v___y_3793_ = v_a_3821_;
v_a_3794_ = v___x_3857_;
goto v___jp_3776_;
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3873_; 
v_a_3860_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3862_ = v___x_3851_;
v_isShared_3863_ = v_isSharedCheck_3873_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3851_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3873_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3864_; lean_object* v___x_3866_; 
v___x_3864_ = lean_io_error_to_string(v_a_3860_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set_tag(v___x_3862_, 3);
lean_ctor_set(v___x_3862_, 0, v___x_3864_);
v___x_3866_ = v___x_3862_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3867_ = l_Lean_MessageData_ofFormat(v___x_3866_);
lean_inc(v___y_3806_);
v___x_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___y_3806_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v___x_3868_);
v___x_3870_ = v___x_3823_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
v___y_3777_ = v___y_3804_;
v___y_3778_ = v___y_3805_;
v___y_3779_ = v___y_3807_;
v___y_3780_ = v___y_3808_;
v___y_3781_ = v___y_3810_;
v___y_3782_ = v___y_3809_;
v___y_3783_ = v___y_3811_;
v___y_3784_ = v___y_3812_;
v___y_3785_ = v___y_3813_;
v___y_3786_ = v___y_3814_;
v___y_3787_ = v___y_3815_;
v___y_3788_ = v___y_3816_;
v___y_3789_ = v___y_3817_;
v___y_3790_ = v___x_3850_;
v___y_3791_ = v___y_3818_;
v___y_3792_ = v___y_3819_;
v___y_3793_ = v_a_3821_;
v_a_3794_ = v___x_3870_;
goto v___jp_3776_;
}
}
}
}
}
}
}
v___jp_3875_:
{
lean_object* v_options_3890_; lean_object* v_inheritedTraceOptions_3891_; uint8_t v_hasTrace_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_options_3890_ = lean_ctor_get(v_toCold_3887_, 2);
v_inheritedTraceOptions_3891_ = lean_ctor_get(v_toCold_3887_, 11);
v_hasTrace_3892_ = lean_ctor_get_uint8(v_options_3890_, sizeof(void*)*1);
v___x_3893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__2));
v___x_3894_ = l_Lean_Name_mkStr3(v___x_3434_, v___x_3435_, v___x_3893_);
if (v_hasTrace_3892_ == 0)
{
lean_object* v___x_3895_; 
lean_dec_ref(v___f_3433_);
lean_dec_ref(v___f_3432_);
lean_inc(v___y_3889_);
lean_inc_ref(v___y_3886_);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3880_);
lean_inc(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
v___x_3895_ = lean_apply_12(v___f_3436_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3889_, lean_box(0));
v___y_3711_ = v___y_3889_;
v___y_3712_ = v___y_3879_;
v___y_3713_ = v___y_3882_;
v___y_3714_ = v___y_3877_;
v___y_3715_ = v___y_3885_;
v___y_3716_ = v___y_3883_;
v___y_3717_ = v___y_3884_;
v___y_3718_ = v___y_3886_;
v___y_3719_ = v___y_3880_;
v___y_3720_ = v___y_3876_;
v___y_3721_ = v___y_3881_;
v___y_3722_ = v___y_3878_;
v___y_3723_ = v___x_3894_;
v___y_3724_ = v___x_3895_;
goto v___jp_3710_;
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v___x_3896_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___x_3894_);
v___x_3897_ = l_Lean_Name_append(v___x_3896_, v___x_3894_);
v___x_3898_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3891_, v_options_3890_, v___x_3897_);
lean_dec(v___x_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3899_ = l_Lean_trace_profiler;
v___x_3900_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_3890_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
lean_dec_ref(v___f_3433_);
lean_dec_ref(v___f_3432_);
lean_inc(v___y_3889_);
lean_inc_ref(v___y_3886_);
lean_inc(v___y_3885_);
lean_inc_ref(v___y_3884_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3880_);
lean_inc(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
v___x_3901_ = lean_apply_12(v___f_3436_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3889_, lean_box(0));
v___y_3711_ = v___y_3889_;
v___y_3712_ = v___y_3879_;
v___y_3713_ = v___y_3882_;
v___y_3714_ = v___y_3877_;
v___y_3715_ = v___y_3885_;
v___y_3716_ = v___y_3883_;
v___y_3717_ = v___y_3884_;
v___y_3718_ = v___y_3886_;
v___y_3719_ = v___y_3880_;
v___y_3720_ = v___y_3876_;
v___y_3721_ = v___y_3881_;
v___y_3722_ = v___y_3878_;
v___y_3723_ = v___x_3894_;
v___y_3724_ = v___x_3901_;
goto v___jp_3710_;
}
else
{
lean_dec_ref(v___f_3436_);
v___y_3804_ = v_options_3890_;
v___y_3805_ = v___y_3889_;
v___y_3806_ = v_ref_3888_;
v___y_3807_ = v___y_3879_;
v___y_3808_ = v___y_3882_;
v___y_3809_ = v___y_3877_;
v___y_3810_ = v___y_3885_;
v___y_3811_ = v___x_3898_;
v___y_3812_ = v___y_3883_;
v___y_3813_ = v___y_3884_;
v___y_3814_ = v___y_3886_;
v___y_3815_ = v___y_3880_;
v___y_3816_ = v___y_3876_;
v___y_3817_ = v___y_3881_;
v___y_3818_ = v___x_3894_;
v___y_3819_ = v___y_3878_;
goto v___jp_3803_;
}
}
else
{
lean_dec_ref(v___f_3436_);
v___y_3804_ = v_options_3890_;
v___y_3805_ = v___y_3889_;
v___y_3806_ = v_ref_3888_;
v___y_3807_ = v___y_3879_;
v___y_3808_ = v___y_3882_;
v___y_3809_ = v___y_3877_;
v___y_3810_ = v___y_3885_;
v___y_3811_ = v___x_3898_;
v___y_3812_ = v___y_3883_;
v___y_3813_ = v___y_3884_;
v___y_3814_ = v___y_3886_;
v___y_3815_ = v___y_3880_;
v___y_3816_ = v___y_3876_;
v___y_3817_ = v___y_3881_;
v___y_3818_ = v___x_3894_;
v___y_3819_ = v___y_3878_;
goto v___jp_3803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13___boxed(lean_object** _args){
lean_object* v_ctx_3921_ = _args[0];
lean_object* v_aig_3922_ = _args[1];
lean_object* v_goal_3923_ = _args[2];
lean_object* v_unusedHypotheses_3924_ = _args[3];
lean_object* v_reflectionResult_3925_ = _args[4];
lean_object* v_satExpr_3926_ = _args[5];
lean_object* v___x_3927_ = _args[6];
lean_object* v___x_3928_ = _args[7];
lean_object* v___f_3929_ = _args[8];
lean_object* v___x_3930_ = _args[9];
lean_object* v___f_3931_ = _args[10];
lean_object* v___f_3932_ = _args[11];
lean_object* v___x_3933_ = _args[12];
lean_object* v___x_3934_ = _args[13];
lean_object* v___f_3935_ = _args[14];
lean_object* v_a_3936_ = _args[15];
lean_object* v_____r_3937_ = _args[16];
lean_object* v___y_3938_ = _args[17];
lean_object* v___y_3939_ = _args[18];
lean_object* v___y_3940_ = _args[19];
lean_object* v___y_3941_ = _args[20];
lean_object* v___y_3942_ = _args[21];
lean_object* v___y_3943_ = _args[22];
lean_object* v___y_3944_ = _args[23];
lean_object* v___y_3945_ = _args[24];
lean_object* v___y_3946_ = _args[25];
lean_object* v___y_3947_ = _args[26];
lean_object* v___y_3948_ = _args[27];
lean_object* v___y_3949_ = _args[28];
lean_object* v___y_3950_ = _args[29];
_start:
{
uint8_t v___x_656017__boxed_3951_; lean_object* v_res_3952_; 
v___x_656017__boxed_3951_ = lean_unbox(v___x_3927_);
v_res_3952_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_3921_, v_aig_3922_, v_goal_3923_, v_unusedHypotheses_3924_, v_reflectionResult_3925_, v_satExpr_3926_, v___x_656017__boxed_3951_, v___x_3928_, v___f_3929_, v___x_3930_, v___f_3931_, v___f_3932_, v___x_3933_, v___x_3934_, v___f_3935_, v_a_3936_, v_____r_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___x_3930_);
return v_res_3952_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(lean_object* v_e_3953_){
_start:
{
if (lean_obj_tag(v_e_3953_) == 0)
{
uint8_t v___x_3954_; 
v___x_3954_ = 2;
return v___x_3954_;
}
else
{
uint8_t v___x_3955_; 
v___x_3955_ = 0;
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21___boxed(lean_object* v_e_3956_){
_start:
{
uint8_t v_res_3957_; lean_object* v_r_3958_; 
v_res_3957_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_e_3956_);
lean_dec_ref(v_e_3956_);
v_r_3958_ = lean_box(v_res_3957_);
return v_r_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(lean_object* v_cls_3959_, uint8_t v_collapsed_3960_, lean_object* v_tag_3961_, lean_object* v_opts_3962_, uint8_t v_clsEnabled_3963_, lean_object* v_oldTraces_3964_, lean_object* v_msg_3965_, lean_object* v_resStartStop_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_fst_3980_; lean_object* v_snd_3981_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v_data_3985_; lean_object* v_fst_3996_; lean_object* v_snd_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; lean_object* v___y_4001_; lean_object* v_a_4002_; uint8_t v___y_4017_; double v___y_4049_; 
v_fst_3980_ = lean_ctor_get(v_resStartStop_3966_, 0);
lean_inc(v_fst_3980_);
v_snd_3981_ = lean_ctor_get(v_resStartStop_3966_, 1);
lean_inc(v_snd_3981_);
lean_dec_ref(v_resStartStop_3966_);
v_fst_3996_ = lean_ctor_get(v_snd_3981_, 0);
lean_inc(v_fst_3996_);
v_snd_3997_ = lean_ctor_get(v_snd_3981_, 1);
lean_inc(v_snd_3997_);
lean_dec(v_snd_3981_);
v___x_3998_ = l_Lean_trace_profiler;
v___x_3999_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_3962_, v___x_3998_);
if (v___x_3999_ == 0)
{
v___y_4017_ = v___x_3999_;
goto v___jp_4016_;
}
else
{
lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4054_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4055_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_3962_, v___x_4054_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; lean_object* v___x_4057_; double v___x_4058_; double v___x_4059_; double v___x_4060_; 
v___x_4056_ = l_Lean_trace_profiler_threshold;
v___x_4057_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_3962_, v___x_4056_);
v___x_4058_ = lean_float_of_nat(v___x_4057_);
v___x_4059_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_4060_ = lean_float_div(v___x_4058_, v___x_4059_);
v___y_4049_ = v___x_4060_;
goto v___jp_4048_;
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; double v___x_4063_; 
v___x_4061_ = l_Lean_trace_profiler_threshold;
v___x_4062_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_3962_, v___x_4061_);
v___x_4063_ = lean_float_of_nat(v___x_4062_);
v___y_4049_ = v___x_4063_;
goto v___jp_4048_;
}
}
v___jp_3982_:
{
lean_object* v___x_3986_; 
lean_inc(v___y_3983_);
v___x_3986_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_3964_, v_data_3985_, v___y_3983_, v___y_3984_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v___x_3987_; 
lean_dec_ref_known(v___x_3986_, 1);
v___x_3987_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_3980_);
return v___x_3987_;
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_fst_3980_);
v_a_3988_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3986_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3986_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
v___jp_4000_:
{
uint8_t v_result_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; double v___x_4006_; lean_object* v_data_4007_; 
v_result_4003_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9_spec__21(v_fst_3980_);
v___x_4004_ = lean_box(v_result_4003_);
v___x_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
v___x_4006_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_3961_);
lean_inc_ref(v___x_4005_);
lean_inc(v_cls_3959_);
v_data_4007_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4007_, 0, v_cls_3959_);
lean_ctor_set(v_data_4007_, 1, v___x_4005_);
lean_ctor_set(v_data_4007_, 2, v_tag_3961_);
lean_ctor_set_float(v_data_4007_, sizeof(void*)*3, v___x_4006_);
lean_ctor_set_float(v_data_4007_, sizeof(void*)*3 + 8, v___x_4006_);
lean_ctor_set_uint8(v_data_4007_, sizeof(void*)*3 + 16, v_collapsed_3960_);
if (v___x_3999_ == 0)
{
lean_dec_ref_known(v___x_4005_, 1);
lean_dec(v_snd_3997_);
lean_dec(v_fst_3996_);
lean_dec_ref(v_tag_3961_);
lean_dec(v_cls_3959_);
v___y_3983_ = v___y_4001_;
v___y_3984_ = v_a_4002_;
v_data_3985_ = v_data_4007_;
goto v___jp_3982_;
}
else
{
lean_object* v_data_4008_; double v___x_4009_; double v___x_4010_; 
lean_dec_ref_known(v_data_4007_, 3);
v_data_4008_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4008_, 0, v_cls_3959_);
lean_ctor_set(v_data_4008_, 1, v___x_4005_);
lean_ctor_set(v_data_4008_, 2, v_tag_3961_);
v___x_4009_ = lean_unbox_float(v_fst_3996_);
lean_dec(v_fst_3996_);
lean_ctor_set_float(v_data_4008_, sizeof(void*)*3, v___x_4009_);
v___x_4010_ = lean_unbox_float(v_snd_3997_);
lean_dec(v_snd_3997_);
lean_ctor_set_float(v_data_4008_, sizeof(void*)*3 + 8, v___x_4010_);
lean_ctor_set_uint8(v_data_4008_, sizeof(void*)*3 + 16, v_collapsed_3960_);
v___y_3983_ = v___y_4001_;
v___y_3984_ = v_a_4002_;
v_data_3985_ = v_data_4008_;
goto v___jp_3982_;
}
}
v___jp_4011_:
{
lean_object* v_ref_4012_; lean_object* v___x_4013_; 
v_ref_4012_ = lean_ctor_get(v___y_3977_, 2);
lean_inc(v___y_3978_);
lean_inc_ref(v___y_3977_);
lean_inc(v___y_3976_);
lean_inc_ref(v___y_3975_);
lean_inc(v___y_3974_);
lean_inc_ref(v___y_3973_);
lean_inc(v___y_3972_);
lean_inc_ref(v___y_3971_);
lean_inc(v___y_3970_);
lean_inc(v___y_3969_);
lean_inc_ref(v___y_3968_);
lean_inc(v___y_3967_);
lean_inc(v_fst_3980_);
v___x_4013_ = lean_apply_14(v_msg_3965_, v_fst_3980_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, lean_box(0));
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref_known(v___x_4013_, 1);
v___y_4001_ = v_ref_4012_;
v_a_4002_ = v_a_4014_;
goto v___jp_4000_;
}
else
{
lean_object* v___x_4015_; 
lean_dec_ref_known(v___x_4013_, 1);
v___x_4015_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_4001_ = v_ref_4012_;
v_a_4002_ = v___x_4015_;
goto v___jp_4000_;
}
}
v___jp_4016_:
{
if (v_clsEnabled_3963_ == 0)
{
if (v___y_4017_ == 0)
{
lean_object* v___x_4018_; lean_object* v_traceState_4019_; lean_object* v_env_4020_; lean_object* v_nextMacroScope_4021_; lean_object* v_ngen_4022_; lean_object* v_auxDeclNGen_4023_; lean_object* v_cache_4024_; lean_object* v_recordedDeps_4025_; lean_object* v_messages_4026_; lean_object* v_infoState_4027_; lean_object* v_snapshotTasks_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4047_; 
lean_dec(v_snd_3997_);
lean_dec(v_fst_3996_);
lean_dec_ref(v_msg_3965_);
lean_dec_ref(v_tag_3961_);
lean_dec(v_cls_3959_);
v___x_4018_ = lean_st_ref_take(v___y_3978_);
v_traceState_4019_ = lean_ctor_get(v___x_4018_, 4);
v_env_4020_ = lean_ctor_get(v___x_4018_, 0);
v_nextMacroScope_4021_ = lean_ctor_get(v___x_4018_, 1);
v_ngen_4022_ = lean_ctor_get(v___x_4018_, 2);
v_auxDeclNGen_4023_ = lean_ctor_get(v___x_4018_, 3);
v_cache_4024_ = lean_ctor_get(v___x_4018_, 5);
v_recordedDeps_4025_ = lean_ctor_get(v___x_4018_, 6);
v_messages_4026_ = lean_ctor_get(v___x_4018_, 7);
v_infoState_4027_ = lean_ctor_get(v___x_4018_, 8);
v_snapshotTasks_4028_ = lean_ctor_get(v___x_4018_, 9);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4030_ = v___x_4018_;
v_isShared_4031_ = v_isSharedCheck_4047_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_snapshotTasks_4028_);
lean_inc(v_infoState_4027_);
lean_inc(v_messages_4026_);
lean_inc(v_recordedDeps_4025_);
lean_inc(v_cache_4024_);
lean_inc(v_traceState_4019_);
lean_inc(v_auxDeclNGen_4023_);
lean_inc(v_ngen_4022_);
lean_inc(v_nextMacroScope_4021_);
lean_inc(v_env_4020_);
lean_dec(v___x_4018_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4047_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
uint64_t v_tid_4032_; lean_object* v_traces_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4046_; 
v_tid_4032_ = lean_ctor_get_uint64(v_traceState_4019_, sizeof(void*)*1);
v_traces_4033_ = lean_ctor_get(v_traceState_4019_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_traceState_4019_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4035_ = v_traceState_4019_;
v_isShared_4036_ = v_isSharedCheck_4046_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_traces_4033_);
lean_dec(v_traceState_4019_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4046_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
v___x_4037_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3964_, v_traces_4033_);
lean_dec_ref(v_traces_4033_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4037_);
v___x_4039_ = v___x_4035_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4037_);
lean_ctor_set_uint64(v_reuseFailAlloc_4045_, sizeof(void*)*1, v_tid_4032_);
v___x_4039_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
lean_object* v___x_4041_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 4, v___x_4039_);
v___x_4041_ = v___x_4030_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_env_4020_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_nextMacroScope_4021_);
lean_ctor_set(v_reuseFailAlloc_4044_, 2, v_ngen_4022_);
lean_ctor_set(v_reuseFailAlloc_4044_, 3, v_auxDeclNGen_4023_);
lean_ctor_set(v_reuseFailAlloc_4044_, 4, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4044_, 5, v_cache_4024_);
lean_ctor_set(v_reuseFailAlloc_4044_, 6, v_recordedDeps_4025_);
lean_ctor_set(v_reuseFailAlloc_4044_, 7, v_messages_4026_);
lean_ctor_set(v_reuseFailAlloc_4044_, 8, v_infoState_4027_);
lean_ctor_set(v_reuseFailAlloc_4044_, 9, v_snapshotTasks_4028_);
v___x_4041_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_st_ref_put(v___y_3978_, v___x_4041_);
v___x_4043_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_fst_3980_);
return v___x_4043_;
}
}
}
}
}
else
{
goto v___jp_4011_;
}
}
else
{
goto v___jp_4011_;
}
}
v___jp_4048_:
{
double v___x_4050_; double v___x_4051_; double v___x_4052_; uint8_t v___x_4053_; 
v___x_4050_ = lean_unbox_float(v_snd_3997_);
v___x_4051_ = lean_unbox_float(v_fst_3996_);
v___x_4052_ = lean_float_sub(v___x_4050_, v___x_4051_);
v___x_4053_ = lean_float_decLt(v___y_4049_, v___x_4052_);
v___y_4017_ = v___x_4053_;
goto v___jp_4016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9___boxed(lean_object** _args){
lean_object* v_cls_4064_ = _args[0];
lean_object* v_collapsed_4065_ = _args[1];
lean_object* v_tag_4066_ = _args[2];
lean_object* v_opts_4067_ = _args[3];
lean_object* v_clsEnabled_4068_ = _args[4];
lean_object* v_oldTraces_4069_ = _args[5];
lean_object* v_msg_4070_ = _args[6];
lean_object* v_resStartStop_4071_ = _args[7];
lean_object* v___y_4072_ = _args[8];
lean_object* v___y_4073_ = _args[9];
lean_object* v___y_4074_ = _args[10];
lean_object* v___y_4075_ = _args[11];
lean_object* v___y_4076_ = _args[12];
lean_object* v___y_4077_ = _args[13];
lean_object* v___y_4078_ = _args[14];
lean_object* v___y_4079_ = _args[15];
lean_object* v___y_4080_ = _args[16];
lean_object* v___y_4081_ = _args[17];
lean_object* v___y_4082_ = _args[18];
lean_object* v___y_4083_ = _args[19];
lean_object* v___y_4084_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_4085_; uint8_t v_clsEnabled_boxed_4086_; lean_object* v_res_4087_; 
v_collapsed_boxed_4085_ = lean_unbox(v_collapsed_4065_);
v_clsEnabled_boxed_4086_ = lean_unbox(v_clsEnabled_4068_);
v_res_4087_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4064_, v_collapsed_boxed_4085_, v_tag_4066_, v_opts_4067_, v_clsEnabled_boxed_4086_, v_oldTraces_4069_, v_msg_4070_, v_resStartStop_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v_opts_4067_);
return v_res_4087_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6(void){
_start:
{
lean_object* v_cls_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v_cls_4097_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
v___x_4098_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
v___x_4099_ = l_Lean_Name_append(v___x_4098_, v_cls_4097_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster(lean_object* v_ctx_4103_, lean_object* v_goal_4104_, lean_object* v_reflectionResult_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v_satExpr_4119_; lean_object* v_unusedHypotheses_4120_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v_toCold_4254_; lean_object* v_options_4255_; lean_object* v_bvExpr_4256_; lean_object* v_ref_4257_; lean_object* v_inheritedTraceOptions_4258_; uint8_t v_hasTrace_4259_; lean_object* v___f_4260_; lean_object* v___f_4261_; lean_object* v___f_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v_cls_4266_; lean_object* v___f_4267_; lean_object* v___f_4268_; uint8_t v___x_4269_; lean_object* v___x_4270_; uint8_t v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v_a_4290_; uint8_t v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v_a_4318_; uint8_t v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; uint8_t v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; uint8_t v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; uint8_t v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; uint8_t v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v_a_4464_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; uint8_t v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v_a_4492_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; uint8_t v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v_toCold_4594_; lean_object* v_ref_4595_; lean_object* v___y_4596_; lean_object* v___y_4608_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v_entry_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; 
v_satExpr_4119_ = lean_ctor_get(v_reflectionResult_4105_, 0);
v_unusedHypotheses_4120_ = lean_ctor_get(v_reflectionResult_4105_, 1);
v_toCold_4254_ = lean_ctor_get(v_a_4116_, 0);
v_options_4255_ = lean_ctor_get(v_toCold_4254_, 2);
v_bvExpr_4256_ = lean_ctor_get(v_satExpr_4119_, 0);
v_ref_4257_ = lean_ctor_get(v_a_4116_, 2);
v_inheritedTraceOptions_4258_ = lean_ctor_get(v_toCold_4254_, 11);
v_hasTrace_4259_ = lean_ctor_get_uint8(v_options_4255_, sizeof(void*)*1);
v___f_4260_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__0));
v___f_4261_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__1));
v___f_4262_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__2));
v___x_4263_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__3));
v___x_4264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__0));
v___x_4265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__1));
v_cls_4266_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__5));
lean_inc_ref(v_bvExpr_4256_);
v___f_4267_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__3), 2, 1);
lean_closure_set(v___f_4267_, 0, v_bvExpr_4256_);
lean_inc_ref(v___f_4267_);
v___f_4268_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4___boxed), 13, 1);
lean_closure_set(v___f_4268_, 0, v___f_4267_);
v___x_4269_ = 1;
v___x_4270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
if (v_hasTrace_4259_ == 0)
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4268_, v_cls_4266_, v___x_4269_, v___x_4270_, v___f_4262_, v___f_4267_, v_options_4255_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v_entry_4654_ = v_a_4696_;
v___y_4655_ = v_a_4106_;
v___y_4656_ = v_a_4107_;
v___y_4657_ = v_a_4108_;
v___y_4658_ = v_a_4109_;
v___y_4659_ = v_a_4110_;
v___y_4660_ = v_a_4111_;
v___y_4661_ = v_a_4112_;
v___y_4662_ = v_a_4113_;
v___y_4663_ = v_a_4114_;
v___y_4664_ = v_a_4115_;
v___y_4665_ = v_a_4116_;
v___y_4666_ = v_a_4117_;
goto v___jp_4653_;
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4697_ = lean_ctor_get(v___x_4695_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4695_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4695_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
else
{
lean_object* v___f_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v_a_4711_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v_a_4723_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; uint8_t v___y_4739_; lean_object* v___y_4740_; lean_object* v___y_4741_; lean_object* v___y_4742_; lean_object* v___y_4743_; uint8_t v___y_4773_; lean_object* v___y_4774_; lean_object* v___y_4775_; uint8_t v___y_4776_; lean_object* v___y_4777_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v_a_4780_; uint8_t v___y_4793_; lean_object* v___y_4794_; uint8_t v___y_4795_; lean_object* v___y_4796_; lean_object* v___y_4797_; lean_object* v___y_4798_; lean_object* v___y_4799_; lean_object* v_a_4800_; uint8_t v___y_4810_; lean_object* v___y_4811_; uint8_t v___y_4812_; uint8_t v___y_4813_; lean_object* v___y_4814_; lean_object* v___y_4815_; lean_object* v___y_4876_; lean_object* v___y_4877_; lean_object* v_a_4878_; lean_object* v___y_4891_; lean_object* v___y_4892_; lean_object* v_a_4893_; lean_object* v___y_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; uint8_t v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; lean_object* v___y_4913_; uint8_t v___y_4943_; lean_object* v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; uint8_t v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4949_; lean_object* v_a_4950_; uint8_t v___y_4963_; lean_object* v___y_4964_; lean_object* v___y_4965_; uint8_t v___y_4966_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v_a_4970_; uint8_t v___y_4980_; lean_object* v___y_4981_; uint8_t v___y_4982_; uint8_t v___y_4983_; lean_object* v___y_4984_; lean_object* v___y_4985_; 
v___f_4705_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__9));
v___x_4706_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4707_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4258_, v_options_4255_, v___x_4706_);
if (v___x_4707_ == 0)
{
lean_object* v___x_5058_; uint8_t v___x_5059_; 
v___x_5058_ = l_Lean_trace_profiler;
v___x_5059_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4255_, v___x_5058_);
if (v___x_5059_ == 0)
{
lean_object* v___x_5060_; 
v___x_5060_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__5(v___f_4268_, v_cls_4266_, v___x_4269_, v___x_4270_, v___f_4262_, v___f_4267_, v_options_4255_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v_entry_4654_ = v_a_5061_;
v___y_4655_ = v_a_4106_;
v___y_4656_ = v_a_4107_;
v___y_4657_ = v_a_4108_;
v___y_4658_ = v_a_4109_;
v___y_4659_ = v_a_4110_;
v___y_4660_ = v_a_4111_;
v___y_4661_ = v_a_4112_;
v___y_4662_ = v_a_4113_;
v___y_4663_ = v_a_4114_;
v___y_4664_ = v_a_4115_;
v___y_4665_ = v_a_4116_;
v___y_4666_ = v_a_4117_;
goto v___jp_4653_;
}
else
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5069_; 
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_5062_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5064_ = v___x_5060_;
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5060_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5069_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5067_; 
if (v_isShared_5065_ == 0)
{
v___x_5067_ = v___x_5064_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_a_5062_);
v___x_5067_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
return v___x_5067_;
}
}
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4120_);
lean_inc_ref(v_satExpr_4119_);
lean_dec_ref(v___f_4268_);
goto v___jp_5045_;
}
}
else
{
lean_inc_ref(v_unusedHypotheses_4120_);
lean_inc_ref(v_satExpr_4119_);
lean_dec_ref(v___f_4268_);
goto v___jp_5045_;
}
v___jp_4708_:
{
lean_object* v___x_4712_; double v___x_4713_; double v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4712_ = lean_io_get_num_heartbeats();
v___x_4713_ = lean_float_of_nat(v___y_4709_);
v___x_4714_ = lean_float_of_nat(v___x_4712_);
v___x_4715_ = lean_box_float(v___x_4713_);
v___x_4716_ = lean_box_float(v___x_4714_);
v___x_4717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4718_, 0, v_a_4711_);
lean_ctor_set(v___x_4718_, 1, v___x_4717_);
v___x_4719_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4266_, v___x_4269_, v___x_4270_, v_options_4255_, v___x_4707_, v___y_4710_, v___f_4705_, v___x_4718_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4719_;
}
v___jp_4720_:
{
lean_object* v___x_4724_; 
v___x_4724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4724_, 0, v_a_4723_);
v___y_4709_ = v___y_4721_;
v___y_4710_ = v___y_4722_;
v_a_4711_ = v___x_4724_;
goto v___jp_4708_;
}
v___jp_4725_:
{
if (lean_obj_tag(v___y_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
v_a_4729_ = lean_ctor_get(v___y_4728_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___y_4728_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___y_4728_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___y_4728_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
lean_ctor_set_tag(v___x_4731_, 1);
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
v___y_4709_ = v___y_4726_;
v___y_4710_ = v___y_4727_;
v_a_4711_ = v___x_4734_;
goto v___jp_4708_;
}
}
}
else
{
lean_object* v_a_4737_; 
v_a_4737_ = lean_ctor_get(v___y_4728_, 0);
lean_inc(v_a_4737_);
lean_dec_ref_known(v___y_4728_, 1);
v___y_4721_ = v___y_4726_;
v___y_4722_ = v___y_4727_;
v_a_4723_ = v_a_4737_;
goto v___jp_4720_;
}
}
v___jp_4738_:
{
if (lean_obj_tag(v___y_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4770_; 
v_a_4744_ = lean_ctor_get(v___y_4743_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___y_4743_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4746_ = v___y_4743_;
v_isShared_4747_ = v_isSharedCheck_4770_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___y_4743_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4770_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v_aig_4748_; lean_object* v_ref_4749_; lean_object* v_decls_4750_; lean_object* v___x_4751_; lean_object* v___f_4752_; lean_object* v___f_4753_; 
v_aig_4748_ = lean_ctor_get(v_a_4744_, 0);
lean_inc_ref_n(v_aig_4748_, 2);
v_ref_4749_ = lean_ctor_get(v_a_4744_, 1);
v_decls_4750_ = lean_ctor_get(v_aig_4748_, 0);
v___x_4751_ = lean_box(v___y_4739_);
lean_inc_ref(v_ref_4749_);
lean_inc(v_a_4744_);
v___f_4752_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__9___boxed), 6, 5);
lean_closure_set(v___f_4752_, 0, v_aig_4748_);
lean_closure_set(v___f_4752_, 1, v___x_4263_);
lean_closure_set(v___f_4752_, 2, v_a_4744_);
lean_closure_set(v___f_4752_, 3, v_ref_4749_);
lean_closure_set(v___f_4752_, 4, v___x_4751_);
lean_inc_ref(v___f_4752_);
v___f_4753_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4753_, 0, v___f_4752_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
lean_del_object(v___x_4746_);
v___x_4754_ = lean_box(0);
v___x_4755_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4103_, v_aig_4748_, v_goal_4104_, v_unusedHypotheses_4120_, v_reflectionResult_4105_, v_satExpr_4119_, v___x_4269_, v___x_4270_, v___f_4260_, v___y_4740_, v___f_4261_, v___f_4752_, v___x_4264_, v___x_4265_, v___f_4753_, v_a_4744_, v___x_4754_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4726_ = v___y_4741_;
v___y_4727_ = v___y_4742_;
v___y_4728_ = v___x_4755_;
goto v___jp_4725_;
}
else
{
lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4763_; 
v___x_4756_ = lean_array_get_size(v_decls_4750_);
v___x_4757_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4758_ = l_Nat_reprFast(v___x_4756_);
v___x_4759_ = lean_string_append(v___x_4757_, v___x_4758_);
lean_dec_ref(v___x_4758_);
v___x_4760_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4761_ = lean_string_append(v___x_4759_, v___x_4760_);
if (v_isShared_4747_ == 0)
{
lean_ctor_set_tag(v___x_4746_, 3);
lean_ctor_set(v___x_4746_, 0, v___x_4761_);
v___x_4763_ = v___x_4746_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4761_);
v___x_4763_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = l_Lean_MessageData_ofFormat(v___x_4763_);
v___x_4765_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4266_, v___x_4764_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4767_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref_known(v___x_4765_, 1);
v___x_4767_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__13(v_ctx_4103_, v_aig_4748_, v_goal_4104_, v_unusedHypotheses_4120_, v_reflectionResult_4105_, v_satExpr_4119_, v___x_4269_, v___x_4270_, v___f_4260_, v___y_4740_, v___f_4261_, v___f_4752_, v___x_4264_, v___x_4265_, v___f_4753_, v_a_4744_, v_a_4766_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4726_ = v___y_4741_;
v___y_4727_ = v___y_4742_;
v___y_4728_ = v___x_4767_;
goto v___jp_4725_;
}
else
{
lean_object* v_a_4768_; 
lean_dec_ref(v___f_4753_);
lean_dec_ref(v___f_4752_);
lean_dec_ref(v_aig_4748_);
lean_dec(v_a_4744_);
lean_dec_ref(v_unusedHypotheses_4120_);
lean_dec_ref(v_satExpr_4119_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4768_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4768_);
lean_dec_ref_known(v___x_4765_, 1);
v___y_4721_ = v___y_4741_;
v___y_4722_ = v___y_4742_;
v_a_4723_ = v_a_4768_;
goto v___jp_4720_;
}
}
}
}
}
else
{
lean_object* v_a_4771_; 
lean_dec_ref(v_unusedHypotheses_4120_);
lean_dec_ref(v_satExpr_4119_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4771_ = lean_ctor_get(v___y_4743_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v___y_4743_, 1);
v___y_4721_ = v___y_4741_;
v___y_4722_ = v___y_4742_;
v_a_4723_ = v_a_4771_;
goto v___jp_4720_;
}
}
v___jp_4772_:
{
lean_object* v___x_4781_; double v___x_4782_; double v___x_4783_; double v___x_4784_; double v___x_4785_; double v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4781_ = lean_io_mono_nanos_now();
v___x_4782_ = lean_float_of_nat(v___y_4775_);
v___x_4783_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4784_ = lean_float_div(v___x_4782_, v___x_4783_);
v___x_4785_ = lean_float_of_nat(v___x_4781_);
v___x_4786_ = lean_float_div(v___x_4785_, v___x_4783_);
v___x_4787_ = lean_box_float(v___x_4784_);
v___x_4788_ = lean_box_float(v___x_4786_);
v___x_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4787_);
lean_ctor_set(v___x_4789_, 1, v___x_4788_);
v___x_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4790_, 0, v_a_4780_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
v___x_4791_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4266_, v___x_4269_, v___x_4270_, v_options_4255_, v___y_4776_, v___y_4778_, v___f_4262_, v___x_4790_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4739_ = v___y_4773_;
v___y_4740_ = v___y_4774_;
v___y_4741_ = v___y_4777_;
v___y_4742_ = v___y_4779_;
v___y_4743_ = v___x_4791_;
goto v___jp_4738_;
}
v___jp_4792_:
{
lean_object* v___x_4801_; double v___x_4802_; double v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4801_ = lean_io_get_num_heartbeats();
v___x_4802_ = lean_float_of_nat(v___y_4796_);
v___x_4803_ = lean_float_of_nat(v___x_4801_);
v___x_4804_ = lean_box_float(v___x_4802_);
v___x_4805_ = lean_box_float(v___x_4803_);
v___x_4806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4804_);
lean_ctor_set(v___x_4806_, 1, v___x_4805_);
v___x_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4807_, 0, v_a_4800_);
lean_ctor_set(v___x_4807_, 1, v___x_4806_);
v___x_4808_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4266_, v___x_4269_, v___x_4270_, v_options_4255_, v___y_4795_, v___y_4798_, v___f_4262_, v___x_4807_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4739_ = v___y_4793_;
v___y_4740_ = v___y_4794_;
v___y_4741_ = v___y_4797_;
v___y_4742_ = v___y_4799_;
v___y_4743_ = v___x_4808_;
goto v___jp_4738_;
}
v___jp_4809_:
{
lean_object* v___x_4816_; 
v___x_4816_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4117_);
if (v___y_4813_ == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4845_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4819_ = v___x_4816_;
v_isShared_4820_ = v_isSharedCheck_4845_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4816_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4845_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4821_ = lean_io_mono_nanos_now();
v___x_4822_ = l_IO_lazyPure___redArg(v___f_4267_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4830_; 
lean_del_object(v___x_4819_);
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4825_ = v___x_4822_;
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4822_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4828_; 
if (v_isShared_4826_ == 0)
{
lean_ctor_set_tag(v___x_4825_, 1);
v___x_4828_ = v___x_4825_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_a_4823_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
v___y_4773_ = v___y_4810_;
v___y_4774_ = v___y_4811_;
v___y_4775_ = v___x_4821_;
v___y_4776_ = v___y_4812_;
v___y_4777_ = v___y_4814_;
v___y_4778_ = v_a_4817_;
v___y_4779_ = v___y_4815_;
v_a_4780_ = v___x_4828_;
goto v___jp_4772_;
}
}
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4844_; 
v_a_4831_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4833_ = v___x_4822_;
v_isShared_4834_ = v_isSharedCheck_4844_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4822_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4844_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4835_; lean_object* v___x_4837_; 
v___x_4835_ = lean_io_error_to_string(v_a_4831_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set_tag(v___x_4833_, 3);
lean_ctor_set(v___x_4833_, 0, v___x_4835_);
v___x_4837_ = v___x_4833_;
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
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4841_; 
v___x_4838_ = l_Lean_MessageData_ofFormat(v___x_4837_);
lean_inc(v_ref_4257_);
v___x_4839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4839_, 0, v_ref_4257_);
lean_ctor_set(v___x_4839_, 1, v___x_4838_);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 0, v___x_4839_);
v___x_4841_ = v___x_4819_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4839_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
v___y_4773_ = v___y_4810_;
v___y_4774_ = v___y_4811_;
v___y_4775_ = v___x_4821_;
v___y_4776_ = v___y_4812_;
v___y_4777_ = v___y_4814_;
v___y_4778_ = v_a_4817_;
v___y_4779_ = v___y_4815_;
v_a_4780_ = v___x_4841_;
goto v___jp_4772_;
}
}
}
}
}
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4874_; 
v_a_4846_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4848_ = v___x_4816_;
v_isShared_4849_ = v_isSharedCheck_4874_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4816_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4874_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; 
v___x_4850_ = lean_io_get_num_heartbeats();
v___x_4851_ = l_IO_lazyPure___redArg(v___f_4267_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
lean_del_object(v___x_4848_);
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
lean_ctor_set_tag(v___x_4854_, 1);
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
v___y_4793_ = v___y_4810_;
v___y_4794_ = v___y_4811_;
v___y_4795_ = v___y_4812_;
v___y_4796_ = v___x_4850_;
v___y_4797_ = v___y_4814_;
v___y_4798_ = v_a_4846_;
v___y_4799_ = v___y_4815_;
v_a_4800_ = v___x_4857_;
goto v___jp_4792_;
}
}
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4873_; 
v_a_4860_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4862_ = v___x_4851_;
v_isShared_4863_ = v_isSharedCheck_4873_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4851_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4873_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4864_; lean_object* v___x_4866_; 
v___x_4864_ = lean_io_error_to_string(v_a_4860_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set_tag(v___x_4862_, 3);
lean_ctor_set(v___x_4862_, 0, v___x_4864_);
v___x_4866_ = v___x_4862_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4870_; 
v___x_4867_ = l_Lean_MessageData_ofFormat(v___x_4866_);
lean_inc(v_ref_4257_);
v___x_4868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4868_, 0, v_ref_4257_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 0, v___x_4868_);
v___x_4870_ = v___x_4848_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4868_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
v___y_4793_ = v___y_4810_;
v___y_4794_ = v___y_4811_;
v___y_4795_ = v___y_4812_;
v___y_4796_ = v___x_4850_;
v___y_4797_ = v___y_4814_;
v___y_4798_ = v_a_4846_;
v___y_4799_ = v___y_4815_;
v_a_4800_ = v___x_4870_;
goto v___jp_4792_;
}
}
}
}
}
}
}
v___jp_4875_:
{
lean_object* v___x_4879_; double v___x_4880_; double v___x_4881_; double v___x_4882_; double v___x_4883_; double v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4879_ = lean_io_mono_nanos_now();
v___x_4880_ = lean_float_of_nat(v___y_4876_);
v___x_4881_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4882_ = lean_float_div(v___x_4880_, v___x_4881_);
v___x_4883_ = lean_float_of_nat(v___x_4879_);
v___x_4884_ = lean_float_div(v___x_4883_, v___x_4881_);
v___x_4885_ = lean_box_float(v___x_4882_);
v___x_4886_ = lean_box_float(v___x_4884_);
v___x_4887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4885_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
v___x_4888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4888_, 0, v_a_4878_);
lean_ctor_set(v___x_4888_, 1, v___x_4887_);
v___x_4889_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__9(v_cls_4266_, v___x_4269_, v___x_4270_, v_options_4255_, v___x_4707_, v___y_4877_, v___f_4705_, v___x_4888_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4889_;
}
v___jp_4890_:
{
lean_object* v___x_4894_; 
v___x_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4894_, 0, v_a_4893_);
v___y_4876_ = v___y_4891_;
v___y_4877_ = v___y_4892_;
v_a_4878_ = v___x_4894_;
goto v___jp_4875_;
}
v___jp_4895_:
{
if (lean_obj_tag(v___y_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
v_a_4899_ = lean_ctor_get(v___y_4898_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___y_4898_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___y_4898_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___y_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set_tag(v___x_4901_, 1);
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
v___y_4876_ = v___y_4896_;
v___y_4877_ = v___y_4897_;
v_a_4878_ = v___x_4904_;
goto v___jp_4875_;
}
}
}
else
{
lean_object* v_a_4907_; 
v_a_4907_ = lean_ctor_get(v___y_4898_, 0);
lean_inc(v_a_4907_);
lean_dec_ref_known(v___y_4898_, 1);
v___y_4891_ = v___y_4896_;
v___y_4892_ = v___y_4897_;
v_a_4893_ = v_a_4907_;
goto v___jp_4890_;
}
}
v___jp_4908_:
{
if (lean_obj_tag(v___y_4913_) == 0)
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4940_; 
v_a_4914_ = lean_ctor_get(v___y_4913_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___y_4913_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4916_ = v___y_4913_;
v_isShared_4917_ = v_isSharedCheck_4940_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___y_4913_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4940_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v_aig_4918_; lean_object* v_ref_4919_; lean_object* v_decls_4920_; lean_object* v___x_4921_; lean_object* v___f_4922_; lean_object* v___f_4923_; 
v_aig_4918_ = lean_ctor_get(v_a_4914_, 0);
lean_inc_ref_n(v_aig_4918_, 2);
v_ref_4919_ = lean_ctor_get(v_a_4914_, 1);
v_decls_4920_ = lean_ctor_get(v_aig_4918_, 0);
v___x_4921_ = lean_box(v___y_4909_);
lean_inc_ref(v_ref_4919_);
lean_inc(v_a_4914_);
v___f_4922_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__8___boxed), 6, 5);
lean_closure_set(v___f_4922_, 0, v_aig_4918_);
lean_closure_set(v___f_4922_, 1, v___x_4263_);
lean_closure_set(v___f_4922_, 2, v_a_4914_);
lean_closure_set(v___f_4922_, 3, v_ref_4919_);
lean_closure_set(v___f_4922_, 4, v___x_4921_);
lean_inc_ref(v___f_4922_);
v___f_4923_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4923_, 0, v___f_4922_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
lean_del_object(v___x_4916_);
v___x_4924_ = lean_box(0);
v___x_4925_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4103_, v_aig_4918_, v_goal_4104_, v_unusedHypotheses_4120_, v_reflectionResult_4105_, v_satExpr_4119_, v___x_4269_, v___x_4270_, v___f_4260_, v___y_4910_, v___f_4261_, v___f_4922_, v___x_4264_, v___x_4265_, v___f_4923_, v_a_4914_, v___x_4924_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4896_ = v___y_4911_;
v___y_4897_ = v___y_4912_;
v___y_4898_ = v___x_4925_;
goto v___jp_4895_;
}
else
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
v___x_4926_ = lean_array_get_size(v_decls_4920_);
v___x_4927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4928_ = l_Nat_reprFast(v___x_4926_);
v___x_4929_ = lean_string_append(v___x_4927_, v___x_4928_);
lean_dec_ref(v___x_4928_);
v___x_4930_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4931_ = lean_string_append(v___x_4929_, v___x_4930_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set_tag(v___x_4916_, 3);
lean_ctor_set(v___x_4916_, 0, v___x_4931_);
v___x_4933_ = v___x_4916_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
v___x_4934_ = l_Lean_MessageData_ofFormat(v___x_4933_);
v___x_4935_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4266_, v___x_4934_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v_a_4936_; lean_object* v___x_4937_; 
v_a_4936_ = lean_ctor_get(v___x_4935_, 0);
lean_inc(v_a_4936_);
lean_dec_ref_known(v___x_4935_, 1);
v___x_4937_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10(v_ctx_4103_, v_aig_4918_, v_goal_4104_, v_unusedHypotheses_4120_, v_reflectionResult_4105_, v_satExpr_4119_, v___x_4269_, v___x_4270_, v___f_4260_, v___y_4910_, v___f_4261_, v___f_4922_, v___x_4264_, v___x_4265_, v___f_4923_, v_a_4914_, v_a_4936_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4896_ = v___y_4911_;
v___y_4897_ = v___y_4912_;
v___y_4898_ = v___x_4937_;
goto v___jp_4895_;
}
else
{
lean_object* v_a_4938_; 
lean_dec_ref(v___f_4923_);
lean_dec_ref(v___f_4922_);
lean_dec_ref(v_aig_4918_);
lean_dec(v_a_4914_);
lean_dec_ref(v_unusedHypotheses_4120_);
lean_dec_ref(v_satExpr_4119_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4938_ = lean_ctor_get(v___x_4935_, 0);
lean_inc(v_a_4938_);
lean_dec_ref_known(v___x_4935_, 1);
v___y_4891_ = v___y_4911_;
v___y_4892_ = v___y_4912_;
v_a_4893_ = v_a_4938_;
goto v___jp_4890_;
}
}
}
}
}
else
{
lean_object* v_a_4941_; 
lean_dec_ref(v_unusedHypotheses_4120_);
lean_dec_ref(v_satExpr_4119_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4941_ = lean_ctor_get(v___y_4913_, 0);
lean_inc(v_a_4941_);
lean_dec_ref_known(v___y_4913_, 1);
v___y_4891_ = v___y_4911_;
v___y_4892_ = v___y_4912_;
v_a_4893_ = v_a_4941_;
goto v___jp_4890_;
}
}
v___jp_4942_:
{
lean_object* v___x_4951_; double v___x_4952_; double v___x_4953_; double v___x_4954_; double v___x_4955_; double v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4951_ = lean_io_mono_nanos_now();
v___x_4952_ = lean_float_of_nat(v___y_4946_);
v___x_4953_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4954_ = lean_float_div(v___x_4952_, v___x_4953_);
v___x_4955_ = lean_float_of_nat(v___x_4951_);
v___x_4956_ = lean_float_div(v___x_4955_, v___x_4953_);
v___x_4957_ = lean_box_float(v___x_4954_);
v___x_4958_ = lean_box_float(v___x_4956_);
v___x_4959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4957_);
lean_ctor_set(v___x_4959_, 1, v___x_4958_);
v___x_4960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4960_, 0, v_a_4950_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4266_, v___x_4269_, v___x_4270_, v_options_4255_, v___y_4947_, v___y_4945_, v___f_4262_, v___x_4960_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4909_ = v___y_4943_;
v___y_4910_ = v___y_4944_;
v___y_4911_ = v___y_4948_;
v___y_4912_ = v___y_4949_;
v___y_4913_ = v___x_4961_;
goto v___jp_4908_;
}
v___jp_4962_:
{
lean_object* v___x_4971_; double v___x_4972_; double v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4971_ = lean_io_get_num_heartbeats();
v___x_4972_ = lean_float_of_nat(v___y_4968_);
v___x_4973_ = lean_float_of_nat(v___x_4971_);
v___x_4974_ = lean_box_float(v___x_4972_);
v___x_4975_ = lean_box_float(v___x_4973_);
v___x_4976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4974_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4977_, 0, v_a_4970_);
lean_ctor_set(v___x_4977_, 1, v___x_4976_);
v___x_4978_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__8(v_cls_4266_, v___x_4269_, v___x_4270_, v_options_4255_, v___y_4966_, v___y_4965_, v___f_4262_, v___x_4977_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4909_ = v___y_4963_;
v___y_4910_ = v___y_4964_;
v___y_4911_ = v___y_4967_;
v___y_4912_ = v___y_4969_;
v___y_4913_ = v___x_4978_;
goto v___jp_4908_;
}
v___jp_4979_:
{
lean_object* v___x_4986_; 
v___x_4986_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4117_);
if (v___y_4982_ == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_5015_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_4989_ = v___x_4986_;
v_isShared_4990_ = v_isSharedCheck_5015_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4986_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_5015_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4991_ = lean_io_mono_nanos_now();
v___x_4992_ = l_IO_lazyPure___redArg(v___f_4267_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
lean_del_object(v___x_4989_);
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4992_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4992_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
lean_ctor_set_tag(v___x_4995_, 1);
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
v___y_4943_ = v___y_4980_;
v___y_4944_ = v___y_4981_;
v___y_4945_ = v_a_4987_;
v___y_4946_ = v___x_4991_;
v___y_4947_ = v___y_4983_;
v___y_4948_ = v___y_4984_;
v___y_4949_ = v___y_4985_;
v_a_4950_ = v___x_4998_;
goto v___jp_4942_;
}
}
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5014_; 
v_a_5001_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5003_ = v___x_4992_;
v_isShared_5004_ = v_isSharedCheck_5014_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_4992_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5014_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5005_; lean_object* v___x_5007_; 
v___x_5005_ = lean_io_error_to_string(v_a_5001_);
if (v_isShared_5004_ == 0)
{
lean_ctor_set_tag(v___x_5003_, 3);
lean_ctor_set(v___x_5003_, 0, v___x_5005_);
v___x_5007_ = v___x_5003_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5011_; 
v___x_5008_ = l_Lean_MessageData_ofFormat(v___x_5007_);
lean_inc(v_ref_4257_);
v___x_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5009_, 0, v_ref_4257_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 0, v___x_5009_);
v___x_5011_ = v___x_4989_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_5009_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
v___y_4943_ = v___y_4980_;
v___y_4944_ = v___y_4981_;
v___y_4945_ = v_a_4987_;
v___y_4946_ = v___x_4991_;
v___y_4947_ = v___y_4983_;
v___y_4948_ = v___y_4984_;
v___y_4949_ = v___y_4985_;
v_a_4950_ = v___x_5011_;
goto v___jp_4942_;
}
}
}
}
}
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5044_; 
v_a_5016_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5018_ = v___x_4986_;
v_isShared_5019_ = v_isSharedCheck_5044_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_4986_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5044_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = lean_io_get_num_heartbeats();
v___x_5021_ = l_IO_lazyPure___redArg(v___f_4267_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
lean_del_object(v___x_5018_);
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_5021_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5021_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 1);
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
v___y_4963_ = v___y_4980_;
v___y_4964_ = v___y_4981_;
v___y_4965_ = v_a_5016_;
v___y_4966_ = v___y_4983_;
v___y_4967_ = v___y_4984_;
v___y_4968_ = v___x_5020_;
v___y_4969_ = v___y_4985_;
v_a_4970_ = v___x_5027_;
goto v___jp_4962_;
}
}
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5043_; 
v_a_5030_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5032_ = v___x_5021_;
v_isShared_5033_ = v_isSharedCheck_5043_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_5021_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5043_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5034_ = lean_io_error_to_string(v_a_5030_);
if (v_isShared_5033_ == 0)
{
lean_ctor_set_tag(v___x_5032_, 3);
lean_ctor_set(v___x_5032_, 0, v___x_5034_);
v___x_5036_ = v___x_5032_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5040_; 
v___x_5037_ = l_Lean_MessageData_ofFormat(v___x_5036_);
lean_inc(v_ref_4257_);
v___x_5038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5038_, 0, v_ref_4257_);
lean_ctor_set(v___x_5038_, 1, v___x_5037_);
if (v_isShared_5019_ == 0)
{
lean_ctor_set(v___x_5018_, 0, v___x_5038_);
v___x_5040_ = v___x_5018_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v___x_5038_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
v___y_4963_ = v___y_4980_;
v___y_4964_ = v___y_4981_;
v___y_4965_ = v_a_5016_;
v___y_4966_ = v___y_4983_;
v___y_4967_ = v___y_4984_;
v___y_4968_ = v___x_5020_;
v___y_4969_ = v___y_4985_;
v_a_4970_ = v___x_5040_;
goto v___jp_4962_;
}
}
}
}
}
}
}
v___jp_5045_:
{
lean_object* v___x_5046_; lean_object* v_a_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; 
v___x_5046_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v_a_4117_);
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc(v_a_5047_);
lean_dec_ref(v___x_5046_);
v___x_5048_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5049_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4255_, v___x_5048_);
if (v___x_5049_ == 0)
{
lean_object* v___x_5050_; 
v___x_5050_ = lean_io_mono_nanos_now();
if (v___x_4707_ == 0)
{
lean_object* v___x_5051_; uint8_t v___x_5052_; 
v___x_5051_ = l_Lean_trace_profiler;
v___x_5052_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4255_, v___x_5051_);
if (v___x_5052_ == 0)
{
lean_object* v___x_5053_; 
v___x_5053_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4267_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4909_ = v___x_5049_;
v___y_4910_ = v___x_5048_;
v___y_4911_ = v___x_5050_;
v___y_4912_ = v_a_5047_;
v___y_4913_ = v___x_5053_;
goto v___jp_4908_;
}
else
{
v___y_4980_ = v___x_5049_;
v___y_4981_ = v___x_5048_;
v___y_4982_ = v___x_5049_;
v___y_4983_ = v___x_4707_;
v___y_4984_ = v___x_5050_;
v___y_4985_ = v_a_5047_;
goto v___jp_4979_;
}
}
else
{
v___y_4980_ = v___x_5049_;
v___y_4981_ = v___x_5048_;
v___y_4982_ = v___x_5049_;
v___y_4983_ = v___x_4707_;
v___y_4984_ = v___x_5050_;
v___y_4985_ = v_a_5047_;
goto v___jp_4979_;
}
}
else
{
lean_object* v___x_5054_; 
v___x_5054_ = lean_io_get_num_heartbeats();
if (v___x_4707_ == 0)
{
lean_object* v___x_5055_; uint8_t v___x_5056_; 
v___x_5055_ = l_Lean_trace_profiler;
v___x_5056_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4255_, v___x_5055_);
if (v___x_5056_ == 0)
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__4(v___f_4267_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
v___y_4739_ = v___x_5049_;
v___y_4740_ = v___x_5048_;
v___y_4741_ = v___x_5054_;
v___y_4742_ = v_a_5047_;
v___y_4743_ = v___x_5057_;
goto v___jp_4738_;
}
else
{
v___y_4810_ = v___x_5049_;
v___y_4811_ = v___x_5048_;
v___y_4812_ = v___x_4707_;
v___y_4813_ = v___x_5049_;
v___y_4814_ = v___x_5054_;
v___y_4815_ = v_a_5047_;
goto v___jp_4809_;
}
}
else
{
v___y_4810_ = v___x_5049_;
v___y_4811_ = v___x_5048_;
v___y_4812_ = v___x_4707_;
v___y_4813_ = v___x_5049_;
v___y_4814_ = v___x_5054_;
v___y_4815_ = v_a_5047_;
goto v___jp_4809_;
}
}
}
}
v___jp_4121_:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v___y_4124_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4140_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4128_ = v___x_4125_;
v_isShared_4129_ = v_isSharedCheck_4140_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4140_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4130_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(v___y_4123_, v___y_4122_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v___y_4122_);
v___x_4131_ = lean_unsigned_to_nat(0u);
v___x_4132_ = lean_array_get_size(v___x_4130_);
v___x_4133_ = l_Array_filterMapM___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__1(v___x_4130_, v___x_4131_, v___x_4132_);
lean_dec_ref(v___x_4130_);
v___x_4134_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__0));
v___x_4135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4135_, 0, v_goal_4104_);
lean_ctor_set(v___x_4135_, 1, v_unusedHypotheses_4120_);
lean_ctor_set(v___x_4135_, 2, v___x_4133_);
lean_ctor_set(v___x_4135_, 3, v___x_4134_);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4136_);
v___x_4138_ = v___x_4128_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec_ref(v_unusedHypotheses_4120_);
lean_dec(v_goal_4104_);
v_a_4141_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4125_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4125_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
v___jp_4149_:
{
lean_object* v___x_4162_; 
lean_inc_ref(v___y_4150_);
v___x_4162_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v___y_4150_, v_ctx_4103_, v_reflectionResult_4105_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4164_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v___x_4164_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_4119_, v_a_4163_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4174_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_goal_4104_, v_a_4165_, v___y_4159_);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4174_ == 0)
{
lean_object* v_unused_4175_; 
v_unused_4175_ = lean_ctor_get(v___x_4166_, 0);
lean_dec(v_unused_4175_);
v___x_4168_ = v___x_4166_;
v_isShared_4169_ = v_isSharedCheck_4174_;
goto v_resetjp_4167_;
}
else
{
lean_dec(v___x_4166_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4174_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___y_4150_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v___x_4170_);
v___x_4172_ = v___x_4168_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec_ref(v___y_4150_);
lean_dec(v_goal_4104_);
v_a_4176_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4164_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4164_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec_ref(v___y_4150_);
lean_dec_ref(v_satExpr_4119_);
lean_dec(v_goal_4104_);
v_a_4184_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4162_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4162_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
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
if (lean_obj_tag(v___y_4206_) == 0)
{
lean_object* v_a_4207_; 
v_a_4207_ = lean_ctor_get(v___y_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v___y_4206_, 1);
if (lean_obj_tag(v_a_4207_) == 0)
{
lean_object* v_toCold_4208_; lean_object* v_options_4209_; uint8_t v_hasTrace_4210_; 
lean_inc_ref(v_unusedHypotheses_4120_);
lean_dec_ref(v_satExpr_4119_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec_ref(v_ctx_4103_);
v_toCold_4208_ = lean_ctor_get(v___y_4204_, 0);
v_options_4209_ = lean_ctor_get(v_toCold_4208_, 2);
v_hasTrace_4210_ = lean_ctor_get_uint8(v_options_4209_, sizeof(void*)*1);
if (v_hasTrace_4210_ == 0)
{
lean_object* v_a_4211_; 
v_a_4211_ = lean_ctor_get(v_a_4207_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v_a_4207_, 1);
v___y_4122_ = v_a_4211_;
v___y_4123_ = v___y_4205_;
v___y_4124_ = v___y_4193_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4212_; lean_object* v_inheritedTraceOptions_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; 
v_a_4212_ = lean_ctor_get(v_a_4207_, 0);
lean_inc(v_a_4212_);
lean_dec_ref_known(v_a_4207_, 1);
v_inheritedTraceOptions_4213_ = lean_ctor_get(v_toCold_4208_, 11);
v___x_4214_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4195_);
v___x_4215_ = l_Lean_Name_append(v___x_4214_, v___y_4195_);
v___x_4216_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4213_, v_options_4209_, v___x_4215_);
lean_dec(v___x_4215_);
if (v___x_4216_ == 0)
{
v___y_4122_ = v_a_4212_;
v___y_4123_ = v___y_4205_;
v___y_4124_ = v___y_4193_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__2);
lean_inc(v___y_4195_);
v___x_4218_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4195_, v___x_4217_, v___y_4194_, v___y_4198_, v___y_4204_, v___y_4201_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_dec_ref_known(v___x_4218_, 1);
v___y_4122_ = v_a_4212_;
v___y_4123_ = v___y_4205_;
v___y_4124_ = v___y_4193_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec(v_a_4212_);
lean_dec_ref(v___y_4205_);
lean_dec_ref(v_unusedHypotheses_4120_);
lean_dec(v_goal_4104_);
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4227_; lean_object* v_options_4228_; uint8_t v_hasTrace_4229_; 
lean_dec_ref(v___y_4205_);
v_toCold_4227_ = lean_ctor_get(v___y_4204_, 0);
v_options_4228_ = lean_ctor_get(v_toCold_4227_, 2);
v_hasTrace_4229_ = lean_ctor_get_uint8(v_options_4228_, sizeof(void*)*1);
if (v_hasTrace_4229_ == 0)
{
lean_object* v_a_4230_; 
v_a_4230_ = lean_ctor_get(v_a_4207_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v_a_4207_, 1);
v___y_4150_ = v_a_4230_;
v___y_4151_ = v___y_4196_;
v___y_4152_ = v___y_4193_;
v___y_4153_ = v___y_4199_;
v___y_4154_ = v___y_4200_;
v___y_4155_ = v___y_4197_;
v___y_4156_ = v___y_4202_;
v___y_4157_ = v___y_4203_;
v___y_4158_ = v___y_4194_;
v___y_4159_ = v___y_4198_;
v___y_4160_ = v___y_4204_;
v___y_4161_ = v___y_4201_;
goto v___jp_4149_;
}
else
{
lean_object* v_a_4231_; lean_object* v_inheritedTraceOptions_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; uint8_t v___x_4235_; 
v_a_4231_ = lean_ctor_get(v_a_4207_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v_a_4207_, 1);
v_inheritedTraceOptions_4232_ = lean_ctor_get(v_toCold_4227_, 11);
v___x_4233_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4195_);
v___x_4234_ = l_Lean_Name_append(v___x_4233_, v___y_4195_);
v___x_4235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4232_, v_options_4228_, v___x_4234_);
lean_dec(v___x_4234_);
if (v___x_4235_ == 0)
{
v___y_4150_ = v_a_4231_;
v___y_4151_ = v___y_4196_;
v___y_4152_ = v___y_4193_;
v___y_4153_ = v___y_4199_;
v___y_4154_ = v___y_4200_;
v___y_4155_ = v___y_4197_;
v___y_4156_ = v___y_4202_;
v___y_4157_ = v___y_4203_;
v___y_4158_ = v___y_4194_;
v___y_4159_ = v___y_4198_;
v___y_4160_ = v___y_4204_;
v___y_4161_ = v___y_4201_;
goto v___jp_4149_;
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__4);
lean_inc(v___y_4195_);
v___x_4237_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v___y_4195_, v___x_4236_, v___y_4194_, v___y_4198_, v___y_4204_, v___y_4201_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_dec_ref_known(v___x_4237_, 1);
v___y_4150_ = v_a_4231_;
v___y_4151_ = v___y_4196_;
v___y_4152_ = v___y_4193_;
v___y_4153_ = v___y_4199_;
v___y_4154_ = v___y_4200_;
v___y_4155_ = v___y_4197_;
v___y_4156_ = v___y_4202_;
v___y_4157_ = v___y_4203_;
v___y_4158_ = v___y_4194_;
v___y_4159_ = v___y_4198_;
v___y_4160_ = v___y_4204_;
v___y_4161_ = v___y_4201_;
goto v___jp_4149_;
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec(v_a_4231_);
lean_dec_ref(v_satExpr_4119_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v___y_4205_);
lean_dec_ref(v_satExpr_4119_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4246_ = lean_ctor_get(v___y_4206_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___y_4206_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___y_4206_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___y_4206_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
v___jp_4271_:
{
lean_object* v___x_4291_; double v___x_4292_; double v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4291_ = lean_io_get_num_heartbeats();
v___x_4292_ = lean_float_of_nat(v___y_4286_);
v___x_4293_ = lean_float_of_nat(v___x_4291_);
v___x_4294_ = lean_box_float(v___x_4292_);
v___x_4295_ = lean_box_float(v___x_4293_);
v___x_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4294_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
v___x_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4297_, 0, v_a_4290_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
lean_inc(v___y_4276_);
v___x_4298_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4276_, v___x_4269_, v___x_4270_, v___y_4280_, v___y_4272_, v___y_4288_, v___f_4260_, v___x_4297_, v___y_4275_, v___y_4277_, v___y_4273_, v___y_4281_, v___y_4282_, v___y_4278_, v___y_4284_, v___y_4285_, v___y_4274_, v___y_4279_, v___y_4287_, v___y_4283_);
v___y_4193_ = v___y_4273_;
v___y_4194_ = v___y_4274_;
v___y_4195_ = v___y_4276_;
v___y_4196_ = v___y_4277_;
v___y_4197_ = v___y_4278_;
v___y_4198_ = v___y_4279_;
v___y_4199_ = v___y_4281_;
v___y_4200_ = v___y_4282_;
v___y_4201_ = v___y_4283_;
v___y_4202_ = v___y_4284_;
v___y_4203_ = v___y_4285_;
v___y_4204_ = v___y_4287_;
v___y_4205_ = v___y_4289_;
v___y_4206_ = v___x_4298_;
goto v___jp_4192_;
}
v___jp_4299_:
{
lean_object* v___x_4319_; double v___x_4320_; double v___x_4321_; double v___x_4322_; double v___x_4323_; double v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4319_ = lean_io_mono_nanos_now();
v___x_4320_ = lean_float_of_nat(v___y_4312_);
v___x_4321_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4322_ = lean_float_div(v___x_4320_, v___x_4321_);
v___x_4323_ = lean_float_of_nat(v___x_4319_);
v___x_4324_ = lean_float_div(v___x_4323_, v___x_4321_);
v___x_4325_ = lean_box_float(v___x_4322_);
v___x_4326_ = lean_box_float(v___x_4324_);
v___x_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4328_, 0, v_a_4318_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
lean_inc(v___y_4304_);
v___x_4329_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5(v___y_4304_, v___x_4269_, v___x_4270_, v___y_4308_, v___y_4300_, v___y_4316_, v___f_4260_, v___x_4328_, v___y_4303_, v___y_4305_, v___y_4301_, v___y_4309_, v___y_4310_, v___y_4306_, v___y_4313_, v___y_4314_, v___y_4302_, v___y_4307_, v___y_4315_, v___y_4311_);
v___y_4193_ = v___y_4301_;
v___y_4194_ = v___y_4302_;
v___y_4195_ = v___y_4304_;
v___y_4196_ = v___y_4305_;
v___y_4197_ = v___y_4306_;
v___y_4198_ = v___y_4307_;
v___y_4199_ = v___y_4309_;
v___y_4200_ = v___y_4310_;
v___y_4201_ = v___y_4311_;
v___y_4202_ = v___y_4313_;
v___y_4203_ = v___y_4314_;
v___y_4204_ = v___y_4315_;
v___y_4205_ = v___y_4317_;
v___y_4206_ = v___x_4329_;
goto v___jp_4192_;
}
v___jp_4330_:
{
lean_object* v___x_4354_; lean_object* v_a_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4354_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4347_);
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref(v___x_4354_);
v___x_4356_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4357_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4342_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = lean_io_mono_nanos_now();
v___x_4359_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4344_, v___y_4352_, v___y_4335_, v___y_4350_, v___y_4340_, v___y_4341_, v___y_4346_, v___y_4351_, v___y_4347_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4359_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4359_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
lean_ctor_set_tag(v___x_4362_, 1);
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
v___y_4300_ = v___y_4331_;
v___y_4301_ = v___y_4332_;
v___y_4302_ = v___y_4334_;
v___y_4303_ = v___y_4333_;
v___y_4304_ = v___y_4336_;
v___y_4305_ = v___y_4337_;
v___y_4306_ = v___y_4338_;
v___y_4307_ = v___y_4339_;
v___y_4308_ = v___y_4342_;
v___y_4309_ = v___y_4343_;
v___y_4310_ = v___y_4345_;
v___y_4311_ = v___y_4347_;
v___y_4312_ = v___x_4358_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4349_;
v___y_4315_ = v___y_4351_;
v___y_4316_ = v_a_4355_;
v___y_4317_ = v___y_4353_;
v_a_4318_ = v___x_4365_;
goto v___jp_4299_;
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
v_a_4368_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4359_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4359_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
lean_ctor_set_tag(v___x_4370_, 0);
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
v___y_4300_ = v___y_4331_;
v___y_4301_ = v___y_4332_;
v___y_4302_ = v___y_4334_;
v___y_4303_ = v___y_4333_;
v___y_4304_ = v___y_4336_;
v___y_4305_ = v___y_4337_;
v___y_4306_ = v___y_4338_;
v___y_4307_ = v___y_4339_;
v___y_4308_ = v___y_4342_;
v___y_4309_ = v___y_4343_;
v___y_4310_ = v___y_4345_;
v___y_4311_ = v___y_4347_;
v___y_4312_ = v___x_4358_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4349_;
v___y_4315_ = v___y_4351_;
v___y_4316_ = v_a_4355_;
v___y_4317_ = v___y_4353_;
v_a_4318_ = v___x_4373_;
goto v___jp_4299_;
}
}
}
}
else
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_io_get_num_heartbeats();
v___x_4377_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v___y_4344_, v___y_4352_, v___y_4335_, v___y_4350_, v___y_4340_, v___y_4341_, v___y_4346_, v___y_4351_, v___y_4347_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
lean_ctor_set_tag(v___x_4380_, 1);
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
v___y_4272_ = v___y_4331_;
v___y_4273_ = v___y_4332_;
v___y_4274_ = v___y_4334_;
v___y_4275_ = v___y_4333_;
v___y_4276_ = v___y_4336_;
v___y_4277_ = v___y_4337_;
v___y_4278_ = v___y_4338_;
v___y_4279_ = v___y_4339_;
v___y_4280_ = v___y_4342_;
v___y_4281_ = v___y_4343_;
v___y_4282_ = v___y_4345_;
v___y_4283_ = v___y_4347_;
v___y_4284_ = v___y_4348_;
v___y_4285_ = v___y_4349_;
v___y_4286_ = v___x_4376_;
v___y_4287_ = v___y_4351_;
v___y_4288_ = v_a_4355_;
v___y_4289_ = v___y_4353_;
v_a_4290_ = v___x_4383_;
goto v___jp_4271_;
}
}
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4377_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4377_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set_tag(v___x_4388_, 0);
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
v___y_4272_ = v___y_4331_;
v___y_4273_ = v___y_4332_;
v___y_4274_ = v___y_4334_;
v___y_4275_ = v___y_4333_;
v___y_4276_ = v___y_4336_;
v___y_4277_ = v___y_4337_;
v___y_4278_ = v___y_4338_;
v___y_4279_ = v___y_4339_;
v___y_4280_ = v___y_4342_;
v___y_4281_ = v___y_4343_;
v___y_4282_ = v___y_4345_;
v___y_4283_ = v___y_4347_;
v___y_4284_ = v___y_4348_;
v___y_4285_ = v___y_4349_;
v___y_4286_ = v___x_4376_;
v___y_4287_ = v___y_4351_;
v___y_4288_ = v_a_4355_;
v___y_4289_ = v___y_4353_;
v_a_4290_ = v___x_4391_;
goto v___jp_4271_;
}
}
}
}
}
v___jp_4394_:
{
if (lean_obj_tag(v___y_4409_) == 0)
{
lean_object* v_toCold_4410_; lean_object* v_options_4411_; uint8_t v_hasTrace_4412_; 
v_toCold_4410_ = lean_ctor_get(v___y_4407_, 0);
v_options_4411_ = lean_ctor_get(v_toCold_4410_, 2);
v_hasTrace_4412_ = lean_ctor_get_uint8(v_options_4411_, sizeof(void*)*1);
if (v_hasTrace_4412_ == 0)
{
lean_object* v_config_4413_; lean_object* v_a_4414_; lean_object* v_solver_4415_; lean_object* v_lratPath_4416_; lean_object* v_timeout_4417_; uint8_t v_trimProofs_4418_; uint8_t v_binaryProofs_4419_; uint8_t v_solverMode_4420_; lean_object* v___x_4421_; 
v_config_4413_ = lean_ctor_get(v_ctx_4103_, 5);
v_a_4414_ = lean_ctor_get(v___y_4409_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___y_4409_, 1);
v_solver_4415_ = lean_ctor_get(v_ctx_4103_, 3);
v_lratPath_4416_ = lean_ctor_get(v_ctx_4103_, 4);
v_timeout_4417_ = lean_ctor_get(v_config_4413_, 0);
v_trimProofs_4418_ = lean_ctor_get_uint8(v_config_4413_, sizeof(void*)*3);
v_binaryProofs_4419_ = lean_ctor_get_uint8(v_config_4413_, sizeof(void*)*3 + 1);
v_solverMode_4420_ = lean_ctor_get_uint8(v_config_4413_, sizeof(void*)*3 + 10);
lean_inc(v_timeout_4417_);
lean_inc_ref(v_lratPath_4416_);
lean_inc_ref(v_solver_4415_);
v___x_4421_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4414_, v_solver_4415_, v_lratPath_4416_, v_trimProofs_4418_, v_timeout_4417_, v_binaryProofs_4419_, v_solverMode_4420_, v___y_4407_, v___y_4404_);
v___y_4193_ = v___y_4395_;
v___y_4194_ = v___y_4397_;
v___y_4195_ = v___y_4398_;
v___y_4196_ = v___y_4399_;
v___y_4197_ = v___y_4400_;
v___y_4198_ = v___y_4401_;
v___y_4199_ = v___y_4402_;
v___y_4200_ = v___y_4403_;
v___y_4201_ = v___y_4404_;
v___y_4202_ = v___y_4405_;
v___y_4203_ = v___y_4406_;
v___y_4204_ = v___y_4407_;
v___y_4205_ = v___y_4408_;
v___y_4206_ = v___x_4421_;
goto v___jp_4192_;
}
else
{
lean_object* v_config_4422_; lean_object* v_a_4423_; lean_object* v_solver_4424_; lean_object* v_lratPath_4425_; lean_object* v_timeout_4426_; uint8_t v_trimProofs_4427_; uint8_t v_binaryProofs_4428_; uint8_t v_solverMode_4429_; lean_object* v_inheritedTraceOptions_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; uint8_t v___x_4433_; 
v_config_4422_ = lean_ctor_get(v_ctx_4103_, 5);
v_a_4423_ = lean_ctor_get(v___y_4409_, 0);
lean_inc(v_a_4423_);
lean_dec_ref_known(v___y_4409_, 1);
v_solver_4424_ = lean_ctor_get(v_ctx_4103_, 3);
v_lratPath_4425_ = lean_ctor_get(v_ctx_4103_, 4);
v_timeout_4426_ = lean_ctor_get(v_config_4422_, 0);
v_trimProofs_4427_ = lean_ctor_get_uint8(v_config_4422_, sizeof(void*)*3);
v_binaryProofs_4428_ = lean_ctor_get_uint8(v_config_4422_, sizeof(void*)*3 + 1);
v_solverMode_4429_ = lean_ctor_get_uint8(v_config_4422_, sizeof(void*)*3 + 10);
v_inheritedTraceOptions_4430_ = lean_ctor_get(v_toCold_4410_, 11);
v___x_4431_ = ((lean_object*)(l_Lean_Options_set___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__1___closed__1));
lean_inc(v___y_4398_);
v___x_4432_ = l_Lean_Name_append(v___x_4431_, v___y_4398_);
v___x_4433_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4430_, v_options_4411_, v___x_4432_);
lean_dec(v___x_4432_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4434_ = l_Lean_trace_profiler;
v___x_4435_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4411_, v___x_4434_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; 
lean_inc(v_timeout_4426_);
lean_inc_ref(v_lratPath_4425_);
lean_inc_ref(v_solver_4424_);
v___x_4436_ = l_Lean_Meta_Tactic_BVDecide_runExternal(v_a_4423_, v_solver_4424_, v_lratPath_4425_, v_trimProofs_4427_, v_timeout_4426_, v_binaryProofs_4428_, v_solverMode_4429_, v___y_4407_, v___y_4404_);
v___y_4193_ = v___y_4395_;
v___y_4194_ = v___y_4397_;
v___y_4195_ = v___y_4398_;
v___y_4196_ = v___y_4399_;
v___y_4197_ = v___y_4400_;
v___y_4198_ = v___y_4401_;
v___y_4199_ = v___y_4402_;
v___y_4200_ = v___y_4403_;
v___y_4201_ = v___y_4404_;
v___y_4202_ = v___y_4405_;
v___y_4203_ = v___y_4406_;
v___y_4204_ = v___y_4407_;
v___y_4205_ = v___y_4408_;
v___y_4206_ = v___x_4436_;
goto v___jp_4192_;
}
else
{
lean_inc_ref(v_solver_4424_);
lean_inc(v_timeout_4426_);
lean_inc_ref(v_lratPath_4425_);
v___y_4331_ = v___x_4433_;
v___y_4332_ = v___y_4395_;
v___y_4333_ = v___y_4396_;
v___y_4334_ = v___y_4397_;
v___y_4335_ = v_lratPath_4425_;
v___y_4336_ = v___y_4398_;
v___y_4337_ = v___y_4399_;
v___y_4338_ = v___y_4400_;
v___y_4339_ = v___y_4401_;
v___y_4340_ = v_timeout_4426_;
v___y_4341_ = v_binaryProofs_4428_;
v___y_4342_ = v_options_4411_;
v___y_4343_ = v___y_4402_;
v___y_4344_ = v_a_4423_;
v___y_4345_ = v___y_4403_;
v___y_4346_ = v_solverMode_4429_;
v___y_4347_ = v___y_4404_;
v___y_4348_ = v___y_4405_;
v___y_4349_ = v___y_4406_;
v___y_4350_ = v_trimProofs_4427_;
v___y_4351_ = v___y_4407_;
v___y_4352_ = v_solver_4424_;
v___y_4353_ = v___y_4408_;
goto v___jp_4330_;
}
}
else
{
lean_inc_ref(v_solver_4424_);
lean_inc(v_timeout_4426_);
lean_inc_ref(v_lratPath_4425_);
v___y_4331_ = v___x_4433_;
v___y_4332_ = v___y_4395_;
v___y_4333_ = v___y_4396_;
v___y_4334_ = v___y_4397_;
v___y_4335_ = v_lratPath_4425_;
v___y_4336_ = v___y_4398_;
v___y_4337_ = v___y_4399_;
v___y_4338_ = v___y_4400_;
v___y_4339_ = v___y_4401_;
v___y_4340_ = v_timeout_4426_;
v___y_4341_ = v_binaryProofs_4428_;
v___y_4342_ = v_options_4411_;
v___y_4343_ = v___y_4402_;
v___y_4344_ = v_a_4423_;
v___y_4345_ = v___y_4403_;
v___y_4346_ = v_solverMode_4429_;
v___y_4347_ = v___y_4404_;
v___y_4348_ = v___y_4405_;
v___y_4349_ = v___y_4406_;
v___y_4350_ = v_trimProofs_4427_;
v___y_4351_ = v___y_4407_;
v___y_4352_ = v_solver_4424_;
v___y_4353_ = v___y_4408_;
goto v___jp_4330_;
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec_ref(v___y_4408_);
lean_dec_ref(v_satExpr_4119_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4437_ = lean_ctor_get(v___y_4409_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___y_4409_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___y_4409_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___y_4409_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
v___jp_4445_:
{
lean_object* v___x_4465_; double v___x_4466_; double v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4465_ = lean_io_get_num_heartbeats();
v___x_4466_ = lean_float_of_nat(v___y_4454_);
v___x_4467_ = lean_float_of_nat(v___x_4465_);
v___x_4468_ = lean_box_float(v___x_4466_);
v___x_4469_ = lean_box_float(v___x_4467_);
v___x_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4468_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
v___x_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4471_, 0, v_a_4464_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
lean_inc(v___y_4449_);
v___x_4472_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4449_, v___x_4269_, v___x_4270_, v___y_4456_, v___y_4461_, v___y_4462_, v___f_4261_, v___x_4471_, v___y_4448_, v___y_4450_, v___y_4446_, v___y_4453_, v___y_4455_, v___y_4451_, v___y_4458_, v___y_4459_, v___y_4447_, v___y_4452_, v___y_4460_, v___y_4457_);
v___y_4395_ = v___y_4446_;
v___y_4396_ = v___y_4448_;
v___y_4397_ = v___y_4447_;
v___y_4398_ = v___y_4449_;
v___y_4399_ = v___y_4450_;
v___y_4400_ = v___y_4451_;
v___y_4401_ = v___y_4452_;
v___y_4402_ = v___y_4453_;
v___y_4403_ = v___y_4455_;
v___y_4404_ = v___y_4457_;
v___y_4405_ = v___y_4458_;
v___y_4406_ = v___y_4459_;
v___y_4407_ = v___y_4460_;
v___y_4408_ = v___y_4463_;
v___y_4409_ = v___x_4472_;
goto v___jp_4394_;
}
v___jp_4473_:
{
lean_object* v___x_4493_; double v___x_4494_; double v___x_4495_; double v___x_4496_; double v___x_4497_; double v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4493_ = lean_io_mono_nanos_now();
v___x_4494_ = lean_float_of_nat(v___y_4488_);
v___x_4495_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_4496_ = lean_float_div(v___x_4494_, v___x_4495_);
v___x_4497_ = lean_float_of_nat(v___x_4493_);
v___x_4498_ = lean_float_div(v___x_4497_, v___x_4495_);
v___x_4499_ = lean_box_float(v___x_4496_);
v___x_4500_ = lean_box_float(v___x_4498_);
v___x_4501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4499_);
lean_ctor_set(v___x_4501_, 1, v___x_4500_);
v___x_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4502_, 0, v_a_4492_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
lean_inc(v___y_4477_);
v___x_4503_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__6(v___y_4477_, v___x_4269_, v___x_4270_, v___y_4483_, v___y_4489_, v___y_4490_, v___f_4261_, v___x_4502_, v___y_4476_, v___y_4478_, v___y_4474_, v___y_4481_, v___y_4482_, v___y_4479_, v___y_4485_, v___y_4486_, v___y_4475_, v___y_4480_, v___y_4487_, v___y_4484_);
v___y_4395_ = v___y_4474_;
v___y_4396_ = v___y_4476_;
v___y_4397_ = v___y_4475_;
v___y_4398_ = v___y_4477_;
v___y_4399_ = v___y_4478_;
v___y_4400_ = v___y_4479_;
v___y_4401_ = v___y_4480_;
v___y_4402_ = v___y_4481_;
v___y_4403_ = v___y_4482_;
v___y_4404_ = v___y_4484_;
v___y_4405_ = v___y_4485_;
v___y_4406_ = v___y_4486_;
v___y_4407_ = v___y_4487_;
v___y_4408_ = v___y_4491_;
v___y_4409_ = v___x_4503_;
goto v___jp_4394_;
}
v___jp_4504_:
{
lean_object* v___x_4523_; lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4578_; 
v___x_4523_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__4___redArg(v___y_4516_);
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4526_ = v___x_4523_;
v_isShared_4527_ = v_isSharedCheck_4578_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4523_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4578_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4529_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v___y_4515_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = lean_io_mono_nanos_now();
v___x_4531_ = l_IO_lazyPure___redArg(v___y_4519_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4539_; 
lean_del_object(v___x_4526_);
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4534_ = v___x_4531_;
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4531_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4537_; 
if (v_isShared_4535_ == 0)
{
lean_ctor_set_tag(v___x_4534_, 1);
v___x_4537_ = v___x_4534_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4532_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
v___y_4474_ = v___y_4505_;
v___y_4475_ = v___y_4507_;
v___y_4476_ = v___y_4506_;
v___y_4477_ = v___y_4508_;
v___y_4478_ = v___y_4509_;
v___y_4479_ = v___y_4510_;
v___y_4480_ = v___y_4511_;
v___y_4481_ = v___y_4512_;
v___y_4482_ = v___y_4514_;
v___y_4483_ = v___y_4515_;
v___y_4484_ = v___y_4516_;
v___y_4485_ = v___y_4517_;
v___y_4486_ = v___y_4518_;
v___y_4487_ = v___y_4520_;
v___y_4488_ = v___x_4530_;
v___y_4489_ = v___y_4521_;
v___y_4490_ = v_a_4524_;
v___y_4491_ = v___y_4522_;
v_a_4492_ = v___x_4537_;
goto v___jp_4473_;
}
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4553_; 
v_a_4540_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4542_ = v___x_4531_;
v_isShared_4543_ = v_isSharedCheck_4553_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4531_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4553_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4544_; lean_object* v___x_4546_; 
v___x_4544_ = lean_io_error_to_string(v_a_4540_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set_tag(v___x_4542_, 3);
lean_ctor_set(v___x_4542_, 0, v___x_4544_);
v___x_4546_ = v___x_4542_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4544_);
v___x_4546_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4547_ = l_Lean_MessageData_ofFormat(v___x_4546_);
lean_inc(v___y_4513_);
v___x_4548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___y_4513_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v___x_4548_);
v___x_4550_ = v___x_4526_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
v___y_4474_ = v___y_4505_;
v___y_4475_ = v___y_4507_;
v___y_4476_ = v___y_4506_;
v___y_4477_ = v___y_4508_;
v___y_4478_ = v___y_4509_;
v___y_4479_ = v___y_4510_;
v___y_4480_ = v___y_4511_;
v___y_4481_ = v___y_4512_;
v___y_4482_ = v___y_4514_;
v___y_4483_ = v___y_4515_;
v___y_4484_ = v___y_4516_;
v___y_4485_ = v___y_4517_;
v___y_4486_ = v___y_4518_;
v___y_4487_ = v___y_4520_;
v___y_4488_ = v___x_4530_;
v___y_4489_ = v___y_4521_;
v___y_4490_ = v_a_4524_;
v___y_4491_ = v___y_4522_;
v_a_4492_ = v___x_4550_;
goto v___jp_4473_;
}
}
}
}
}
else
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4554_ = lean_io_get_num_heartbeats();
v___x_4555_ = l_IO_lazyPure___redArg(v___y_4519_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_del_object(v___x_4526_);
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4555_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4555_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
lean_ctor_set_tag(v___x_4558_, 1);
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
v___y_4446_ = v___y_4505_;
v___y_4447_ = v___y_4507_;
v___y_4448_ = v___y_4506_;
v___y_4449_ = v___y_4508_;
v___y_4450_ = v___y_4509_;
v___y_4451_ = v___y_4510_;
v___y_4452_ = v___y_4511_;
v___y_4453_ = v___y_4512_;
v___y_4454_ = v___x_4554_;
v___y_4455_ = v___y_4514_;
v___y_4456_ = v___y_4515_;
v___y_4457_ = v___y_4516_;
v___y_4458_ = v___y_4517_;
v___y_4459_ = v___y_4518_;
v___y_4460_ = v___y_4520_;
v___y_4461_ = v___y_4521_;
v___y_4462_ = v_a_4524_;
v___y_4463_ = v___y_4522_;
v_a_4464_ = v___x_4561_;
goto v___jp_4445_;
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4577_; 
v_a_4564_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4566_ = v___x_4555_;
v_isShared_4567_ = v_isSharedCheck_4577_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4555_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4577_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4568_; lean_object* v___x_4570_; 
v___x_4568_ = lean_io_error_to_string(v_a_4564_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set_tag(v___x_4566_, 3);
lean_ctor_set(v___x_4566_, 0, v___x_4568_);
v___x_4570_ = v___x_4566_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4568_);
v___x_4570_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4574_; 
v___x_4571_ = l_Lean_MessageData_ofFormat(v___x_4570_);
lean_inc(v___y_4513_);
v___x_4572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___y_4513_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v___x_4572_);
v___x_4574_ = v___x_4526_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4572_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
v___y_4446_ = v___y_4505_;
v___y_4447_ = v___y_4507_;
v___y_4448_ = v___y_4506_;
v___y_4449_ = v___y_4508_;
v___y_4450_ = v___y_4509_;
v___y_4451_ = v___y_4510_;
v___y_4452_ = v___y_4511_;
v___y_4453_ = v___y_4512_;
v___y_4454_ = v___x_4554_;
v___y_4455_ = v___y_4514_;
v___y_4456_ = v___y_4515_;
v___y_4457_ = v___y_4516_;
v___y_4458_ = v___y_4517_;
v___y_4459_ = v___y_4518_;
v___y_4460_ = v___y_4520_;
v___y_4461_ = v___y_4521_;
v___y_4462_ = v_a_4524_;
v___y_4463_ = v___y_4522_;
v_a_4464_ = v___x_4574_;
goto v___jp_4445_;
}
}
}
}
}
}
}
v___jp_4579_:
{
lean_object* v_options_4597_; lean_object* v_inheritedTraceOptions_4598_; uint8_t v_hasTrace_4599_; lean_object* v___x_4600_; 
v_options_4597_ = lean_ctor_get(v_toCold_4594_, 2);
v_inheritedTraceOptions_4598_ = lean_ctor_get(v_toCold_4594_, 11);
v_hasTrace_4599_ = lean_ctor_get_uint8(v_options_4597_, sizeof(void*)*1);
v___x_4600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
if (v_hasTrace_4599_ == 0)
{
lean_object* v___x_4601_; 
lean_dec_ref(v___y_4580_);
lean_inc(v___y_4596_);
lean_inc_ref(v___y_4593_);
lean_inc(v___y_4592_);
lean_inc_ref(v___y_4591_);
lean_inc(v___y_4590_);
lean_inc_ref(v___y_4589_);
lean_inc(v___y_4588_);
lean_inc_ref(v___y_4587_);
lean_inc(v___y_4586_);
lean_inc(v___y_4585_);
lean_inc_ref(v___y_4584_);
v___x_4601_ = lean_apply_12(v___y_4581_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4596_, lean_box(0));
v___y_4395_ = v___y_4585_;
v___y_4396_ = v___y_4583_;
v___y_4397_ = v___y_4591_;
v___y_4398_ = v___x_4600_;
v___y_4399_ = v___y_4584_;
v___y_4400_ = v___y_4588_;
v___y_4401_ = v___y_4592_;
v___y_4402_ = v___y_4586_;
v___y_4403_ = v___y_4587_;
v___y_4404_ = v___y_4596_;
v___y_4405_ = v___y_4589_;
v___y_4406_ = v___y_4590_;
v___y_4407_ = v___y_4593_;
v___y_4408_ = v___y_4582_;
v___y_4409_ = v___x_4601_;
goto v___jp_4394_;
}
else
{
lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_4603_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4598_, v_options_4597_, v___x_4602_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; uint8_t v___x_4605_; 
v___x_4604_ = l_Lean_trace_profiler;
v___x_4605_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_4597_, v___x_4604_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; 
lean_dec_ref(v___y_4580_);
lean_inc(v___y_4596_);
lean_inc_ref(v___y_4593_);
lean_inc(v___y_4592_);
lean_inc_ref(v___y_4591_);
lean_inc(v___y_4590_);
lean_inc_ref(v___y_4589_);
lean_inc(v___y_4588_);
lean_inc_ref(v___y_4587_);
lean_inc(v___y_4586_);
lean_inc(v___y_4585_);
lean_inc_ref(v___y_4584_);
v___x_4606_ = lean_apply_12(v___y_4581_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4596_, lean_box(0));
v___y_4395_ = v___y_4585_;
v___y_4396_ = v___y_4583_;
v___y_4397_ = v___y_4591_;
v___y_4398_ = v___x_4600_;
v___y_4399_ = v___y_4584_;
v___y_4400_ = v___y_4588_;
v___y_4401_ = v___y_4592_;
v___y_4402_ = v___y_4586_;
v___y_4403_ = v___y_4587_;
v___y_4404_ = v___y_4596_;
v___y_4405_ = v___y_4589_;
v___y_4406_ = v___y_4590_;
v___y_4407_ = v___y_4593_;
v___y_4408_ = v___y_4582_;
v___y_4409_ = v___x_4606_;
goto v___jp_4394_;
}
else
{
lean_dec_ref(v___y_4581_);
v___y_4505_ = v___y_4585_;
v___y_4506_ = v___y_4583_;
v___y_4507_ = v___y_4591_;
v___y_4508_ = v___x_4600_;
v___y_4509_ = v___y_4584_;
v___y_4510_ = v___y_4588_;
v___y_4511_ = v___y_4592_;
v___y_4512_ = v___y_4586_;
v___y_4513_ = v_ref_4595_;
v___y_4514_ = v___y_4587_;
v___y_4515_ = v_options_4597_;
v___y_4516_ = v___y_4596_;
v___y_4517_ = v___y_4589_;
v___y_4518_ = v___y_4590_;
v___y_4519_ = v___y_4580_;
v___y_4520_ = v___y_4593_;
v___y_4521_ = v___x_4603_;
v___y_4522_ = v___y_4582_;
goto v___jp_4504_;
}
}
else
{
lean_dec_ref(v___y_4581_);
v___y_4505_ = v___y_4585_;
v___y_4506_ = v___y_4583_;
v___y_4507_ = v___y_4591_;
v___y_4508_ = v___x_4600_;
v___y_4509_ = v___y_4584_;
v___y_4510_ = v___y_4588_;
v___y_4511_ = v___y_4592_;
v___y_4512_ = v___y_4586_;
v___y_4513_ = v_ref_4595_;
v___y_4514_ = v___y_4587_;
v___y_4515_ = v_options_4597_;
v___y_4516_ = v___y_4596_;
v___y_4517_ = v___y_4589_;
v___y_4518_ = v___y_4590_;
v___y_4519_ = v___y_4580_;
v___y_4520_ = v___y_4593_;
v___y_4521_ = v___x_4603_;
v___y_4522_ = v___y_4582_;
goto v___jp_4504_;
}
}
}
v___jp_4607_:
{
lean_object* v_config_4624_; uint8_t v_graphviz_4625_; 
v_config_4624_ = lean_ctor_get(v_ctx_4103_, 5);
v_graphviz_4625_ = lean_ctor_get_uint8(v_config_4624_, sizeof(void*)*3 + 8);
if (v_graphviz_4625_ == 0)
{
lean_object* v_toCold_4626_; lean_object* v_ref_4627_; 
lean_inc_ref(v_satExpr_4119_);
lean_dec_ref(v___y_4608_);
v_toCold_4626_ = lean_ctor_get(v___y_4622_, 0);
v_ref_4627_ = lean_ctor_get(v___y_4622_, 2);
v___y_4580_ = v___y_4609_;
v___y_4581_ = v___y_4611_;
v___y_4582_ = v___y_4610_;
v___y_4583_ = v___y_4612_;
v___y_4584_ = v___y_4613_;
v___y_4585_ = v___y_4614_;
v___y_4586_ = v___y_4615_;
v___y_4587_ = v___y_4616_;
v___y_4588_ = v___y_4617_;
v___y_4589_ = v___y_4618_;
v___y_4590_ = v___y_4619_;
v___y_4591_ = v___y_4620_;
v___y_4592_ = v___y_4621_;
v___y_4593_ = v___y_4622_;
v_toCold_4594_ = v_toCold_4626_;
v_ref_4595_ = v_ref_4627_;
v___y_4596_ = v___y_4623_;
goto v___jp_4579_;
}
else
{
lean_object* v_toCold_4628_; lean_object* v_ref_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v_toCold_4628_ = lean_ctor_get(v___y_4622_, 0);
v_ref_4629_ = lean_ctor_get(v___y_4622_, 2);
v___x_4630_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__10___closed__7);
v___x_4631_ = l_Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7(v___y_4608_);
v___x_4632_ = l_IO_FS_writeFile(v___x_4630_, v___x_4631_);
lean_dec_ref(v___x_4631_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_inc_ref(v_satExpr_4119_);
lean_dec_ref_known(v___x_4632_, 1);
v___y_4580_ = v___y_4609_;
v___y_4581_ = v___y_4611_;
v___y_4582_ = v___y_4610_;
v___y_4583_ = v___y_4612_;
v___y_4584_ = v___y_4613_;
v___y_4585_ = v___y_4614_;
v___y_4586_ = v___y_4615_;
v___y_4587_ = v___y_4616_;
v___y_4588_ = v___y_4617_;
v___y_4589_ = v___y_4618_;
v___y_4590_ = v___y_4619_;
v___y_4591_ = v___y_4620_;
v___y_4592_ = v___y_4621_;
v___y_4593_ = v___y_4622_;
v_toCold_4594_ = v_toCold_4628_;
v_ref_4595_ = v_ref_4629_;
v___y_4596_ = v___y_4623_;
goto v___jp_4579_;
}
else
{
lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4650_; 
lean_dec_ref(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_reflectionResult_4105_);
if (v_isSharedCheck_4650_ == 0)
{
lean_object* v_unused_4651_; lean_object* v_unused_4652_; 
v_unused_4651_ = lean_ctor_get(v_reflectionResult_4105_, 1);
lean_dec(v_unused_4651_);
v_unused_4652_ = lean_ctor_get(v_reflectionResult_4105_, 0);
lean_dec(v_unused_4652_);
v___x_4634_ = v_reflectionResult_4105_;
v_isShared_4635_ = v_isSharedCheck_4650_;
goto v_resetjp_4633_;
}
else
{
lean_dec(v_reflectionResult_4105_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4650_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4649_; 
v_a_4636_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4638_ = v___x_4632_;
v_isShared_4639_ = v_isSharedCheck_4649_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4632_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4649_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4644_; 
v___x_4640_ = lean_io_error_to_string(v_a_4636_);
v___x_4641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4640_);
v___x_4642_ = l_Lean_MessageData_ofFormat(v___x_4641_);
lean_inc(v_ref_4629_);
if (v_isShared_4635_ == 0)
{
lean_ctor_set(v___x_4634_, 1, v___x_4642_);
lean_ctor_set(v___x_4634_, 0, v_ref_4629_);
v___x_4644_ = v___x_4634_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_ref_4629_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4646_; 
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 0, v___x_4644_);
v___x_4646_ = v___x_4638_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4644_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
}
}
}
v___jp_4653_:
{
lean_object* v_aig_4667_; lean_object* v_toCold_4668_; lean_object* v_options_4669_; lean_object* v_ref_4670_; lean_object* v_decls_4671_; lean_object* v_inheritedTraceOptions_4672_; uint8_t v_hasTrace_4673_; lean_object* v___f_4674_; lean_object* v___f_4675_; 
v_aig_4667_ = lean_ctor_get(v_entry_4654_, 0);
lean_inc_ref_n(v_aig_4667_, 2);
v_toCold_4668_ = lean_ctor_get(v___y_4665_, 0);
v_options_4669_ = lean_ctor_get(v_toCold_4668_, 2);
v_ref_4670_ = lean_ctor_get(v_entry_4654_, 1);
v_decls_4671_ = lean_ctor_get(v_aig_4667_, 0);
v_inheritedTraceOptions_4672_ = lean_ctor_get(v_toCold_4668_, 11);
v_hasTrace_4673_ = lean_ctor_get_uint8(v_options_4669_, sizeof(void*)*1);
lean_inc_ref(v_ref_4670_);
lean_inc_ref(v_entry_4654_);
v___f_4674_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__6___boxed), 5, 4);
lean_closure_set(v___f_4674_, 0, v_aig_4667_);
lean_closure_set(v___f_4674_, 1, v___x_4263_);
lean_closure_set(v___f_4674_, 2, v_entry_4654_);
lean_closure_set(v___f_4674_, 3, v_ref_4670_);
lean_inc_ref(v___f_4674_);
v___f_4675_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__7___boxed), 13, 1);
lean_closure_set(v___f_4675_, 0, v___f_4674_);
if (v_hasTrace_4673_ == 0)
{
v___y_4608_ = v_entry_4654_;
v___y_4609_ = v___f_4674_;
v___y_4610_ = v_aig_4667_;
v___y_4611_ = v___f_4675_;
v___y_4612_ = v___y_4655_;
v___y_4613_ = v___y_4656_;
v___y_4614_ = v___y_4657_;
v___y_4615_ = v___y_4658_;
v___y_4616_ = v___y_4659_;
v___y_4617_ = v___y_4660_;
v___y_4618_ = v___y_4661_;
v___y_4619_ = v___y_4662_;
v___y_4620_ = v___y_4663_;
v___y_4621_ = v___y_4664_;
v___y_4622_ = v___y_4665_;
v___y_4623_ = v___y_4666_;
goto v___jp_4607_;
}
else
{
lean_object* v___x_4676_; uint8_t v___x_4677_; 
v___x_4676_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__6);
v___x_4677_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4672_, v_options_4669_, v___x_4676_);
if (v___x_4677_ == 0)
{
v___y_4608_ = v_entry_4654_;
v___y_4609_ = v___f_4674_;
v___y_4610_ = v_aig_4667_;
v___y_4611_ = v___f_4675_;
v___y_4612_ = v___y_4655_;
v___y_4613_ = v___y_4656_;
v___y_4614_ = v___y_4657_;
v___y_4615_ = v___y_4658_;
v___y_4616_ = v___y_4659_;
v___y_4617_ = v___y_4660_;
v___y_4618_ = v___y_4661_;
v___y_4619_ = v___y_4662_;
v___y_4620_ = v___y_4663_;
v___y_4621_ = v___y_4664_;
v___y_4622_ = v___y_4665_;
v___y_4623_ = v___y_4666_;
goto v___jp_4607_;
}
else
{
lean_object* v_aigSize_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v_aigSize_4678_ = lean_array_get_size(v_decls_4671_);
v___x_4679_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__7));
v___x_4680_ = l_Nat_reprFast(v_aigSize_4678_);
v___x_4681_ = lean_string_append(v___x_4679_, v___x_4680_);
lean_dec_ref(v___x_4680_);
v___x_4682_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratBitblaster___closed__8));
v___x_4683_ = lean_string_append(v___x_4681_, v___x_4682_);
v___x_4684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
v___x_4685_ = l_Lean_MessageData_ofFormat(v___x_4684_);
v___x_4686_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_4266_, v___x_4685_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_dec_ref_known(v___x_4686_, 1);
v___y_4608_ = v_entry_4654_;
v___y_4609_ = v___f_4674_;
v___y_4610_ = v_aig_4667_;
v___y_4611_ = v___f_4675_;
v___y_4612_ = v___y_4655_;
v___y_4613_ = v___y_4656_;
v___y_4614_ = v___y_4657_;
v___y_4615_ = v___y_4658_;
v___y_4616_ = v___y_4659_;
v___y_4617_ = v___y_4660_;
v___y_4618_ = v___y_4661_;
v___y_4619_ = v___y_4662_;
v___y_4620_ = v___y_4663_;
v___y_4621_ = v___y_4664_;
v___y_4622_ = v___y_4665_;
v___y_4623_ = v___y_4666_;
goto v___jp_4607_;
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v___f_4675_);
lean_dec_ref(v___f_4674_);
lean_dec_ref(v_aig_4667_);
lean_dec_ref(v_entry_4654_);
lean_dec_ref(v_reflectionResult_4105_);
lean_dec(v_goal_4104_);
lean_dec_ref(v_ctx_4103_);
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4686_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4686_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratBitblaster___boxed(lean_object* v_ctx_5070_, lean_object* v_goal_5071_, lean_object* v_reflectionResult_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_Meta_Tactic_BVDecide_lratBitblaster(v_ctx_5070_, v_goal_5071_, v_reflectionResult_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_);
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
lean_dec(v_a_5082_);
lean_dec_ref(v_a_5081_);
lean_dec(v_a_5080_);
lean_dec_ref(v_a_5079_);
lean_dec(v_a_5078_);
lean_dec_ref(v_a_5077_);
lean_dec(v_a_5076_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
lean_dec(v_a_5073_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(lean_object* v_cls_5087_, lean_object* v_msg_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v___x_5102_; 
v___x_5102_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___redArg(v_cls_5087_, v_msg_5088_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2___boxed(lean_object* v_cls_5103_, lean_object* v_msg_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__2(v_cls_5103_, v_msg_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
lean_dec(v___y_5116_);
lean_dec_ref(v___y_5115_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
lean_dec(v___y_5108_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
lean_dec(v___y_5105_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(lean_object* v_mvarId_5119_, lean_object* v_val_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___redArg(v_mvarId_5119_, v_val_5120_, v___y_5130_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3___boxed(lean_object* v_mvarId_5135_, lean_object* v_val_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3(v_mvarId_5135_, v_val_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
lean_dec(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(lean_object* v_00_u03b1_5151_, lean_object* v_x_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___redArg(v_x_5152_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9___boxed(lean_object* v_00_u03b1_5167_, lean_object* v_x_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
lean_object* v_res_5182_; 
v_res_5182_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__9(v_00_u03b1_5167_, v_x_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5179_);
lean_dec(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
lean_dec(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v___y_5169_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5(lean_object* v_00_u03b2_5183_, lean_object* v_x_5184_, lean_object* v_x_5185_, lean_object* v_x_5186_){
_start:
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_x_5184_, v_x_5185_, v_x_5186_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(lean_object* v_oldTraces_5188_, lean_object* v_data_5189_, lean_object* v_ref_5190_, lean_object* v_msg_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v___x_5205_; 
v___x_5205_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___redArg(v_oldTraces_5188_, v_data_5189_, v_ref_5190_, v_msg_5191_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_5206_ = _args[0];
lean_object* v_data_5207_ = _args[1];
lean_object* v_ref_5208_ = _args[2];
lean_object* v_msg_5209_ = _args[3];
lean_object* v___y_5210_ = _args[4];
lean_object* v___y_5211_ = _args[5];
lean_object* v___y_5212_ = _args[6];
lean_object* v___y_5213_ = _args[7];
lean_object* v___y_5214_ = _args[8];
lean_object* v___y_5215_ = _args[9];
lean_object* v___y_5216_ = _args[10];
lean_object* v___y_5217_ = _args[11];
lean_object* v___y_5218_ = _args[12];
lean_object* v___y_5219_ = _args[13];
lean_object* v___y_5220_ = _args[14];
lean_object* v___y_5221_ = _args[15];
lean_object* v___y_5222_ = _args[16];
_start:
{
lean_object* v_res_5223_; 
v_res_5223_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__5_spec__8(v_oldTraces_5206_, v_data_5207_, v_ref_5208_, v_msg_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
lean_dec(v___y_5219_);
lean_dec_ref(v___y_5218_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(lean_object* v_acc_5224_, lean_object* v_decls_5225_, lean_object* v_hinv_5226_, lean_object* v_idx_5227_, lean_object* v_hidx_5228_, lean_object* v_a_5229_){
_start:
{
lean_object* v___x_5230_; 
v___x_5230_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___redArg(v_acc_5224_, v_decls_5225_, v_idx_5227_, v_a_5229_);
return v___x_5230_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15___boxed(lean_object* v_acc_5231_, lean_object* v_decls_5232_, lean_object* v_hinv_5233_, lean_object* v_idx_5234_, lean_object* v_hidx_5235_, lean_object* v_a_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15(v_acc_5231_, v_decls_5232_, v_hinv_5233_, v_idx_5234_, v_hidx_5235_, v_a_5236_);
lean_dec_ref(v_decls_5232_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_5238_, lean_object* v_x_5239_, size_t v_x_5240_, size_t v_x_5241_, lean_object* v_x_5242_, lean_object* v_x_5243_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___redArg(v_x_5239_, v_x_5240_, v_x_5241_, v_x_5242_, v_x_5243_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_5245_, lean_object* v_x_5246_, lean_object* v_x_5247_, lean_object* v_x_5248_, lean_object* v_x_5249_, lean_object* v_x_5250_){
_start:
{
size_t v_x_659274__boxed_5251_; size_t v_x_659275__boxed_5252_; lean_object* v_res_5253_; 
v_x_659274__boxed_5251_ = lean_unbox_usize(v_x_5247_);
lean_dec(v_x_5247_);
v_x_659275__boxed_5252_ = lean_unbox_usize(v_x_5248_);
lean_dec(v_x_5248_);
v_res_5253_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7(v_00_u03b2_5245_, v_x_5246_, v_x_659274__boxed_5251_, v_x_659275__boxed_5252_, v_x_5249_, v_x_5250_);
return v_res_5253_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(lean_object* v___x_5254_, lean_object* v_00_u03b2_5255_, lean_object* v_m_5256_, lean_object* v_a_5257_){
_start:
{
uint8_t v___x_5258_; 
v___x_5258_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___redArg(v___x_5254_, v_m_5256_, v_a_5257_);
return v___x_5258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17___boxed(lean_object* v___x_5259_, lean_object* v_00_u03b2_5260_, lean_object* v_m_5261_, lean_object* v_a_5262_){
_start:
{
uint8_t v_res_5263_; lean_object* v_r_5264_; 
v_res_5263_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17(v___x_5259_, v_00_u03b2_5260_, v_m_5261_, v_a_5262_);
lean_dec(v_a_5262_);
lean_dec_ref(v_m_5261_);
lean_dec(v___x_5259_);
v_r_5264_ = lean_box(v_res_5263_);
return v_r_5264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(lean_object* v___x_5265_, lean_object* v_00_u03b2_5266_, lean_object* v_m_5267_, lean_object* v_a_5268_, lean_object* v_b_5269_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___redArg(v___x_5265_, v_m_5267_, v_a_5268_, v_b_5269_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18___boxed(lean_object* v___x_5271_, lean_object* v_00_u03b2_5272_, lean_object* v_m_5273_, lean_object* v_a_5274_, lean_object* v_b_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18(v___x_5271_, v_00_u03b2_5272_, v_m_5273_, v_a_5274_, v_b_5275_);
lean_dec(v___x_5271_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19(lean_object* v_00_u03b2_5277_, lean_object* v_n_5278_, lean_object* v_k_5279_, lean_object* v_v_5280_){
_start:
{
lean_object* v___x_5281_; 
v___x_5281_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19___redArg(v_n_5278_, v_k_5279_, v_v_5280_);
return v___x_5281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(lean_object* v_00_u03b2_5282_, size_t v_depth_5283_, lean_object* v_keys_5284_, lean_object* v_vals_5285_, lean_object* v_heq_5286_, lean_object* v_i_5287_, lean_object* v_entries_5288_){
_start:
{
lean_object* v___x_5289_; 
v___x_5289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___redArg(v_depth_5283_, v_keys_5284_, v_vals_5285_, v_i_5287_, v_entries_5288_);
return v___x_5289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20___boxed(lean_object* v_00_u03b2_5290_, lean_object* v_depth_5291_, lean_object* v_keys_5292_, lean_object* v_vals_5293_, lean_object* v_heq_5294_, lean_object* v_i_5295_, lean_object* v_entries_5296_){
_start:
{
size_t v_depth_boxed_5297_; lean_object* v_res_5298_; 
v_depth_boxed_5297_ = lean_unbox_usize(v_depth_5291_);
lean_dec(v_depth_5291_);
v_res_5298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__20(v_00_u03b2_5290_, v_depth_boxed_5297_, v_keys_5292_, v_vals_5293_, v_heq_5294_, v_i_5295_, v_entries_5296_);
lean_dec_ref(v_vals_5293_);
lean_dec_ref(v_keys_5292_);
return v_res_5298_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(lean_object* v___x_5299_, lean_object* v_00_u03b2_5300_, lean_object* v_a_5301_, lean_object* v_x_5302_){
_start:
{
uint8_t v___x_5303_; 
v___x_5303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___redArg(v_a_5301_, v_x_5302_);
return v___x_5303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24___boxed(lean_object* v___x_5304_, lean_object* v_00_u03b2_5305_, lean_object* v_a_5306_, lean_object* v_x_5307_){
_start:
{
uint8_t v_res_5308_; lean_object* v_r_5309_; 
v_res_5308_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__17_spec__24(v___x_5304_, v_00_u03b2_5305_, v_a_5306_, v_x_5307_);
lean_dec(v_x_5307_);
lean_dec(v_a_5306_);
lean_dec(v___x_5304_);
v_r_5309_ = lean_box(v_res_5308_);
return v_r_5309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(lean_object* v___x_5310_, lean_object* v_00_u03b2_5311_, lean_object* v_data_5312_){
_start:
{
lean_object* v___x_5313_; 
v___x_5313_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___redArg(v___x_5310_, v_data_5312_);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26___boxed(lean_object* v___x_5314_, lean_object* v_00_u03b2_5315_, lean_object* v_data_5316_){
_start:
{
lean_object* v_res_5317_; 
v_res_5317_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26(v___x_5314_, v_00_u03b2_5315_, v_data_5316_);
lean_dec(v___x_5314_);
return v_res_5317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24(lean_object* v_00_u03b2_5318_, lean_object* v_x_5319_, lean_object* v_x_5320_, lean_object* v_x_5321_, lean_object* v_x_5322_){
_start:
{
lean_object* v___x_5323_; 
v___x_5323_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5_spec__7_spec__19_spec__24___redArg(v_x_5319_, v_x_5320_, v_x_5321_, v_x_5322_);
return v___x_5323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(lean_object* v___x_5324_, lean_object* v_00_u03b2_5325_, lean_object* v_i_5326_, lean_object* v_source_5327_, lean_object* v_target_5328_){
_start:
{
lean_object* v___x_5329_; 
v___x_5329_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___redArg(v_i_5326_, v_source_5327_, v_target_5328_);
return v___x_5329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30___boxed(lean_object* v___x_5330_, lean_object* v_00_u03b2_5331_, lean_object* v_i_5332_, lean_object* v_source_5333_, lean_object* v_target_5334_){
_start:
{
lean_object* v_res_5335_; 
v_res_5335_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30(v___x_5330_, v_00_u03b2_5331_, v_i_5332_, v_source_5333_, v_target_5334_);
lean_dec(v___x_5330_);
return v_res_5335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31(lean_object* v_00_u03b2_5336_, lean_object* v_x_5337_, lean_object* v_x_5338_){
_start:
{
lean_object* v___x_5339_; 
v___x_5339_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_Sat_AIG_toGraphviz_go___at___00Std_Sat_AIG_toGraphviz___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__7_spec__15_spec__18_spec__26_spec__30_spec__31___redArg(v_x_5337_, v_x_5338_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(lean_object* v___y_5340_){
_start:
{
lean_object* v___x_5342_; lean_object* v_traceState_5343_; lean_object* v_traces_5344_; lean_object* v___x_5345_; lean_object* v_traceState_5346_; lean_object* v_env_5347_; lean_object* v_nextMacroScope_5348_; lean_object* v_ngen_5349_; lean_object* v_auxDeclNGen_5350_; lean_object* v_cache_5351_; lean_object* v_recordedDeps_5352_; lean_object* v_messages_5353_; lean_object* v_infoState_5354_; lean_object* v_snapshotTasks_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5376_; 
v___x_5342_ = lean_st_ref_get(v___y_5340_);
v_traceState_5343_ = lean_ctor_get(v___x_5342_, 4);
lean_inc_ref(v_traceState_5343_);
lean_dec(v___x_5342_);
v_traces_5344_ = lean_ctor_get(v_traceState_5343_, 0);
lean_inc_ref(v_traces_5344_);
lean_dec_ref(v_traceState_5343_);
v___x_5345_ = lean_st_ref_take(v___y_5340_);
v_traceState_5346_ = lean_ctor_get(v___x_5345_, 4);
v_env_5347_ = lean_ctor_get(v___x_5345_, 0);
v_nextMacroScope_5348_ = lean_ctor_get(v___x_5345_, 1);
v_ngen_5349_ = lean_ctor_get(v___x_5345_, 2);
v_auxDeclNGen_5350_ = lean_ctor_get(v___x_5345_, 3);
v_cache_5351_ = lean_ctor_get(v___x_5345_, 5);
v_recordedDeps_5352_ = lean_ctor_get(v___x_5345_, 6);
v_messages_5353_ = lean_ctor_get(v___x_5345_, 7);
v_infoState_5354_ = lean_ctor_get(v___x_5345_, 8);
v_snapshotTasks_5355_ = lean_ctor_get(v___x_5345_, 9);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5357_ = v___x_5345_;
v_isShared_5358_ = v_isSharedCheck_5376_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_snapshotTasks_5355_);
lean_inc(v_infoState_5354_);
lean_inc(v_messages_5353_);
lean_inc(v_recordedDeps_5352_);
lean_inc(v_cache_5351_);
lean_inc(v_traceState_5346_);
lean_inc(v_auxDeclNGen_5350_);
lean_inc(v_ngen_5349_);
lean_inc(v_nextMacroScope_5348_);
lean_inc(v_env_5347_);
lean_dec(v___x_5345_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5376_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
uint64_t v_tid_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5374_; 
v_tid_5359_ = lean_ctor_get_uint64(v_traceState_5346_, sizeof(void*)*1);
v_isSharedCheck_5374_ = !lean_is_exclusive(v_traceState_5346_);
if (v_isSharedCheck_5374_ == 0)
{
lean_object* v_unused_5375_; 
v_unused_5375_ = lean_ctor_get(v_traceState_5346_, 0);
lean_dec(v_unused_5375_);
v___x_5361_ = v_traceState_5346_;
v_isShared_5362_ = v_isSharedCheck_5374_;
goto v_resetjp_5360_;
}
else
{
lean_dec(v_traceState_5346_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5374_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5367_; 
v___x_5363_ = lean_unsigned_to_nat(32u);
v___x_5364_ = lean_mk_empty_array_with_capacity(v___x_5363_);
lean_dec_ref(v___x_5364_);
v___x_5365_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__0___redArg___closed__1);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 0, v___x_5365_);
v___x_5367_ = v___x_5361_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5365_);
lean_ctor_set_uint64(v_reuseFailAlloc_5373_, sizeof(void*)*1, v_tid_5359_);
v___x_5367_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
lean_object* v___x_5369_; 
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 4, v___x_5367_);
v___x_5369_ = v___x_5357_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_env_5347_);
lean_ctor_set(v_reuseFailAlloc_5372_, 1, v_nextMacroScope_5348_);
lean_ctor_set(v_reuseFailAlloc_5372_, 2, v_ngen_5349_);
lean_ctor_set(v_reuseFailAlloc_5372_, 3, v_auxDeclNGen_5350_);
lean_ctor_set(v_reuseFailAlloc_5372_, 4, v___x_5367_);
lean_ctor_set(v_reuseFailAlloc_5372_, 5, v_cache_5351_);
lean_ctor_set(v_reuseFailAlloc_5372_, 6, v_recordedDeps_5352_);
lean_ctor_set(v_reuseFailAlloc_5372_, 7, v_messages_5353_);
lean_ctor_set(v_reuseFailAlloc_5372_, 8, v_infoState_5354_);
lean_ctor_set(v_reuseFailAlloc_5372_, 9, v_snapshotTasks_5355_);
v___x_5369_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
lean_object* v___x_5370_; lean_object* v___x_5371_; 
v___x_5370_ = lean_st_ref_put(v___y_5340_, v___x_5369_);
v___x_5371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5371_, 0, v_traces_5344_);
return v___x_5371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg___boxed(lean_object* v___y_5377_, lean_object* v___y_5378_){
_start:
{
lean_object* v_res_5379_; 
v_res_5379_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5377_);
lean_dec(v___y_5377_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v___x_5392_; 
v___x_5392_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v___y_5390_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___boxed(lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1(v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
lean_dec(v___y_5399_);
lean_dec_ref(v___y_5398_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5396_);
lean_dec(v___y_5395_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(lean_object* v_x_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_){
_start:
{
lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5419_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2, &l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_lratBitblaster___lam__12___closed__2);
v___x_5420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5420_, 0, v___x_5419_);
return v___x_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0___boxed(lean_object* v_x_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___lam__0(v_x_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
lean_dec(v___y_5428_);
lean_dec_ref(v___y_5427_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
lean_dec(v___y_5424_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec_ref(v_x_5421_);
return v_res_5434_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(lean_object* v_e_5435_){
_start:
{
if (lean_obj_tag(v_e_5435_) == 0)
{
uint8_t v___x_5436_; 
v___x_5436_ = 2;
return v___x_5436_;
}
else
{
uint8_t v___x_5437_; 
v___x_5437_ = 0;
return v___x_5437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4___boxed(lean_object* v_e_5438_){
_start:
{
uint8_t v_res_5439_; lean_object* v_r_5440_; 
v_res_5439_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_e_5438_);
lean_dec_ref(v_e_5438_);
v_r_5440_ = lean_box(v_res_5439_);
return v_r_5440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(lean_object* v_oldTraces_5441_, lean_object* v_data_5442_, lean_object* v_ref_5443_, lean_object* v_msg_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_){
_start:
{
lean_object* v_toCold_5450_; lean_object* v_currRecDepth_5451_; lean_object* v_ref_5452_; uint16_t v_optionFlags_5453_; uint8_t v_suppressElabErrors_5454_; uint8_t v_isRecordingDeps_5455_; lean_object* v_ref_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v_traceState_5459_; lean_object* v_traces_5460_; lean_object* v___x_5461_; size_t v_sz_5462_; size_t v___x_5463_; lean_object* v___x_5464_; lean_object* v_msg_5465_; lean_object* v___x_5466_; lean_object* v_a_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5505_; 
v_toCold_5450_ = lean_ctor_get(v___y_5447_, 0);
v_currRecDepth_5451_ = lean_ctor_get(v___y_5447_, 1);
v_ref_5452_ = lean_ctor_get(v___y_5447_, 2);
v_optionFlags_5453_ = lean_ctor_get_uint16(v___y_5447_, sizeof(void*)*3);
v_suppressElabErrors_5454_ = lean_ctor_get_uint8(v___y_5447_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5455_ = lean_ctor_get_uint8(v___y_5447_, sizeof(void*)*3 + 3);
v_ref_5456_ = l_Lean_replaceRef(v_ref_5443_, v_ref_5452_);
lean_inc(v_currRecDepth_5451_);
lean_inc_ref(v_toCold_5450_);
v___x_5457_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5457_, 0, v_toCold_5450_);
lean_ctor_set(v___x_5457_, 1, v_currRecDepth_5451_);
lean_ctor_set(v___x_5457_, 2, v_ref_5456_);
lean_ctor_set_uint16(v___x_5457_, sizeof(void*)*3, v_optionFlags_5453_);
lean_ctor_set_uint8(v___x_5457_, sizeof(void*)*3 + 2, v_suppressElabErrors_5454_);
lean_ctor_set_uint8(v___x_5457_, sizeof(void*)*3 + 3, v_isRecordingDeps_5455_);
v___x_5458_ = lean_st_ref_get(v___y_5448_);
v_traceState_5459_ = lean_ctor_get(v___x_5458_, 4);
lean_inc_ref(v_traceState_5459_);
lean_dec(v___x_5458_);
v_traces_5460_ = lean_ctor_get(v_traceState_5459_, 0);
lean_inc_ref(v_traces_5460_);
lean_dec_ref(v_traceState_5459_);
v___x_5461_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5460_);
lean_dec_ref(v_traces_5460_);
v_sz_5462_ = lean_array_size(v___x_5461_);
v___x_5463_ = ((size_t)0ULL);
v___x_5464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__2_spec__2_spec__3(v_sz_5462_, v___x_5463_, v___x_5461_);
v_msg_5465_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5465_, 0, v_data_5442_);
lean_ctor_set(v_msg_5465_, 1, v_msg_5444_);
lean_ctor_set(v_msg_5465_, 2, v___x_5464_);
v___x_5466_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__3_spec__6(v_msg_5465_, v___y_5445_, v___y_5446_, v___x_5457_, v___y_5448_);
lean_dec_ref_known(v___x_5457_, 3);
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5469_ = v___x_5466_;
v_isShared_5470_ = v_isSharedCheck_5505_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_a_5467_);
lean_dec(v___x_5466_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5505_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v___x_5471_; lean_object* v_traceState_5472_; lean_object* v_env_5473_; lean_object* v_nextMacroScope_5474_; lean_object* v_ngen_5475_; lean_object* v_auxDeclNGen_5476_; lean_object* v_cache_5477_; lean_object* v_recordedDeps_5478_; lean_object* v_messages_5479_; lean_object* v_infoState_5480_; lean_object* v_snapshotTasks_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5504_; 
v___x_5471_ = lean_st_ref_take(v___y_5448_);
v_traceState_5472_ = lean_ctor_get(v___x_5471_, 4);
v_env_5473_ = lean_ctor_get(v___x_5471_, 0);
v_nextMacroScope_5474_ = lean_ctor_get(v___x_5471_, 1);
v_ngen_5475_ = lean_ctor_get(v___x_5471_, 2);
v_auxDeclNGen_5476_ = lean_ctor_get(v___x_5471_, 3);
v_cache_5477_ = lean_ctor_get(v___x_5471_, 5);
v_recordedDeps_5478_ = lean_ctor_get(v___x_5471_, 6);
v_messages_5479_ = lean_ctor_get(v___x_5471_, 7);
v_infoState_5480_ = lean_ctor_get(v___x_5471_, 8);
v_snapshotTasks_5481_ = lean_ctor_get(v___x_5471_, 9);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5483_ = v___x_5471_;
v_isShared_5484_ = v_isSharedCheck_5504_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_snapshotTasks_5481_);
lean_inc(v_infoState_5480_);
lean_inc(v_messages_5479_);
lean_inc(v_recordedDeps_5478_);
lean_inc(v_cache_5477_);
lean_inc(v_traceState_5472_);
lean_inc(v_auxDeclNGen_5476_);
lean_inc(v_ngen_5475_);
lean_inc(v_nextMacroScope_5474_);
lean_inc(v_env_5473_);
lean_dec(v___x_5471_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5504_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
uint64_t v_tid_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5502_; 
v_tid_5485_ = lean_ctor_get_uint64(v_traceState_5472_, sizeof(void*)*1);
v_isSharedCheck_5502_ = !lean_is_exclusive(v_traceState_5472_);
if (v_isSharedCheck_5502_ == 0)
{
lean_object* v_unused_5503_; 
v_unused_5503_ = lean_ctor_get(v_traceState_5472_, 0);
lean_dec(v_unused_5503_);
v___x_5487_ = v_traceState_5472_;
v_isShared_5488_ = v_isSharedCheck_5502_;
goto v_resetjp_5486_;
}
else
{
lean_dec(v_traceState_5472_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5502_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5493_; 
v___x_5489_ = lean_box(0);
v___x_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5490_, 0, v_ref_5443_);
lean_ctor_set(v___x_5490_, 1, v_a_5467_);
v___x_5491_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5441_, v___x_5490_);
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 0, v___x_5491_);
v___x_5493_ = v___x_5487_;
goto v_reusejp_5492_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v___x_5491_);
lean_ctor_set_uint64(v_reuseFailAlloc_5501_, sizeof(void*)*1, v_tid_5485_);
v___x_5493_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5492_;
}
v_reusejp_5492_:
{
lean_object* v___x_5495_; 
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 4, v___x_5493_);
v___x_5495_ = v___x_5483_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_env_5473_);
lean_ctor_set(v_reuseFailAlloc_5500_, 1, v_nextMacroScope_5474_);
lean_ctor_set(v_reuseFailAlloc_5500_, 2, v_ngen_5475_);
lean_ctor_set(v_reuseFailAlloc_5500_, 3, v_auxDeclNGen_5476_);
lean_ctor_set(v_reuseFailAlloc_5500_, 4, v___x_5493_);
lean_ctor_set(v_reuseFailAlloc_5500_, 5, v_cache_5477_);
lean_ctor_set(v_reuseFailAlloc_5500_, 6, v_recordedDeps_5478_);
lean_ctor_set(v_reuseFailAlloc_5500_, 7, v_messages_5479_);
lean_ctor_set(v_reuseFailAlloc_5500_, 8, v_infoState_5480_);
lean_ctor_set(v_reuseFailAlloc_5500_, 9, v_snapshotTasks_5481_);
v___x_5495_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
lean_object* v___x_5496_; lean_object* v___x_5498_; 
v___x_5496_ = lean_st_ref_put(v___y_5448_, v___x_5495_);
if (v_isShared_5470_ == 0)
{
lean_ctor_set(v___x_5469_, 0, v___x_5489_);
v___x_5498_ = v___x_5469_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5489_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_5506_, lean_object* v_data_5507_, lean_object* v_ref_5508_, lean_object* v_msg_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_){
_start:
{
lean_object* v_res_5515_; 
v_res_5515_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5506_, v_data_5507_, v_ref_5508_, v_msg_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_);
lean_dec(v___y_5513_);
lean_dec_ref(v___y_5512_);
lean_dec(v___y_5511_);
lean_dec_ref(v___y_5510_);
return v_res_5515_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(lean_object* v_x_5516_){
_start:
{
if (lean_obj_tag(v_x_5516_) == 0)
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
v_a_5518_ = lean_ctor_get(v_x_5516_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v_x_5516_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v_x_5516_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v_x_5516_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
lean_ctor_set_tag(v___x_5520_, 1);
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5533_; 
v_a_5526_ = lean_ctor_get(v_x_5516_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v_x_5516_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5528_ = v_x_5516_;
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v_x_5516_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5531_; 
if (v_isShared_5529_ == 0)
{
lean_ctor_set_tag(v___x_5528_, 0);
v___x_5531_ = v___x_5528_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5526_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg___boxed(lean_object* v_x_5534_, lean_object* v___y_5535_){
_start:
{
lean_object* v_res_5536_; 
v_res_5536_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5534_);
return v_res_5536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(lean_object* v_cls_5537_, uint8_t v_collapsed_5538_, lean_object* v_tag_5539_, lean_object* v_opts_5540_, uint8_t v_clsEnabled_5541_, lean_object* v_oldTraces_5542_, lean_object* v_msg_5543_, lean_object* v_resStartStop_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
lean_object* v_fst_5557_; lean_object* v_snd_5558_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v_data_5562_; lean_object* v_fst_5573_; lean_object* v_snd_5574_; lean_object* v___x_5575_; uint8_t v___x_5576_; lean_object* v___y_5578_; lean_object* v_a_5579_; uint8_t v___y_5594_; double v___y_5626_; 
v_fst_5557_ = lean_ctor_get(v_resStartStop_5544_, 0);
lean_inc(v_fst_5557_);
v_snd_5558_ = lean_ctor_get(v_resStartStop_5544_, 1);
lean_inc(v_snd_5558_);
lean_dec_ref(v_resStartStop_5544_);
v_fst_5573_ = lean_ctor_get(v_snd_5558_, 0);
lean_inc(v_fst_5573_);
v_snd_5574_ = lean_ctor_get(v_snd_5558_, 1);
lean_inc(v_snd_5574_);
lean_dec(v_snd_5558_);
v___x_5575_ = l_Lean_trace_profiler;
v___x_5576_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5540_, v___x_5575_);
if (v___x_5576_ == 0)
{
v___y_5594_ = v___x_5576_;
goto v___jp_5593_;
}
else
{
lean_object* v___x_5631_; uint8_t v___x_5632_; 
v___x_5631_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5632_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_opts_5540_, v___x_5631_);
if (v___x_5632_ == 0)
{
lean_object* v___x_5633_; lean_object* v___x_5634_; double v___x_5635_; double v___x_5636_; double v___x_5637_; 
v___x_5633_ = l_Lean_trace_profiler_threshold;
v___x_5634_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5540_, v___x_5633_);
v___x_5635_ = lean_float_of_nat(v___x_5634_);
v___x_5636_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__3);
v___x_5637_ = lean_float_div(v___x_5635_, v___x_5636_);
v___y_5626_ = v___x_5637_;
goto v___jp_5625_;
}
else
{
lean_object* v___x_5638_; lean_object* v___x_5639_; double v___x_5640_; 
v___x_5638_ = l_Lean_trace_profiler_threshold;
v___x_5639_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_mkAuxDecl_spec__0(v_opts_5540_, v___x_5638_);
v___x_5640_ = lean_float_of_nat(v___x_5639_);
v___y_5626_ = v___x_5640_;
goto v___jp_5625_;
}
}
v___jp_5559_:
{
lean_object* v___x_5563_; 
lean_inc(v___y_5561_);
v___x_5563_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5542_, v_data_5562_, v___y_5561_, v___y_5560_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_);
if (lean_obj_tag(v___x_5563_) == 0)
{
lean_object* v___x_5564_; 
lean_dec_ref_known(v___x_5563_, 1);
v___x_5564_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5557_);
return v___x_5564_;
}
else
{
lean_object* v_a_5565_; lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5572_; 
lean_dec(v_fst_5557_);
v_a_5565_ = lean_ctor_get(v___x_5563_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5567_ = v___x_5563_;
v_isShared_5568_ = v_isSharedCheck_5572_;
goto v_resetjp_5566_;
}
else
{
lean_inc(v_a_5565_);
lean_dec(v___x_5563_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5572_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
lean_object* v___x_5570_; 
if (v_isShared_5568_ == 0)
{
v___x_5570_ = v___x_5567_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_a_5565_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
}
v___jp_5577_:
{
uint8_t v_result_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; double v___x_5583_; lean_object* v_data_5584_; 
v_result_5580_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__4(v_fst_5557_);
v___x_5581_ = lean_box(v_result_5580_);
v___x_5582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
v___x_5583_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__0);
lean_inc_ref(v_tag_5539_);
lean_inc_ref(v___x_5582_);
lean_inc(v_cls_5537_);
v_data_5584_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5584_, 0, v_cls_5537_);
lean_ctor_set(v_data_5584_, 1, v___x_5582_);
lean_ctor_set(v_data_5584_, 2, v_tag_5539_);
lean_ctor_set_float(v_data_5584_, sizeof(void*)*3, v___x_5583_);
lean_ctor_set_float(v_data_5584_, sizeof(void*)*3 + 8, v___x_5583_);
lean_ctor_set_uint8(v_data_5584_, sizeof(void*)*3 + 16, v_collapsed_5538_);
if (v___x_5576_ == 0)
{
lean_dec_ref_known(v___x_5582_, 1);
lean_dec(v_snd_5574_);
lean_dec(v_fst_5573_);
lean_dec_ref(v_tag_5539_);
lean_dec(v_cls_5537_);
v___y_5560_ = v_a_5579_;
v___y_5561_ = v___y_5578_;
v_data_5562_ = v_data_5584_;
goto v___jp_5559_;
}
else
{
lean_object* v_data_5585_; double v___x_5586_; double v___x_5587_; 
lean_dec_ref_known(v_data_5584_, 3);
v_data_5585_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5585_, 0, v_cls_5537_);
lean_ctor_set(v_data_5585_, 1, v___x_5582_);
lean_ctor_set(v_data_5585_, 2, v_tag_5539_);
v___x_5586_ = lean_unbox_float(v_fst_5573_);
lean_dec(v_fst_5573_);
lean_ctor_set_float(v_data_5585_, sizeof(void*)*3, v___x_5586_);
v___x_5587_ = lean_unbox_float(v_snd_5574_);
lean_dec(v_snd_5574_);
lean_ctor_set_float(v_data_5585_, sizeof(void*)*3 + 8, v___x_5587_);
lean_ctor_set_uint8(v_data_5585_, sizeof(void*)*3 + 16, v_collapsed_5538_);
v___y_5560_ = v_a_5579_;
v___y_5561_ = v___y_5578_;
v_data_5562_ = v_data_5585_;
goto v___jp_5559_;
}
}
v___jp_5588_:
{
lean_object* v_ref_5589_; lean_object* v___x_5590_; 
v_ref_5589_ = lean_ctor_get(v___y_5554_, 2);
lean_inc(v___y_5555_);
lean_inc_ref(v___y_5554_);
lean_inc(v___y_5553_);
lean_inc_ref(v___y_5552_);
lean_inc(v___y_5551_);
lean_inc_ref(v___y_5550_);
lean_inc(v___y_5549_);
lean_inc_ref(v___y_5548_);
lean_inc(v___y_5547_);
lean_inc(v___y_5546_);
lean_inc_ref(v___y_5545_);
lean_inc(v_fst_5557_);
v___x_5590_ = lean_apply_13(v_msg_5543_, v_fst_5557_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, lean_box(0));
if (lean_obj_tag(v___x_5590_) == 0)
{
lean_object* v_a_5591_; 
v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
lean_inc(v_a_5591_);
lean_dec_ref_known(v___x_5590_, 1);
v___y_5578_ = v_ref_5589_;
v_a_5579_ = v_a_5591_;
goto v___jp_5577_;
}
else
{
lean_object* v___x_5592_; 
lean_dec_ref_known(v___x_5590_, 1);
v___x_5592_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__4___closed__2);
v___y_5578_ = v_ref_5589_;
v_a_5579_ = v___x_5592_;
goto v___jp_5577_;
}
}
v___jp_5593_:
{
if (v_clsEnabled_5541_ == 0)
{
if (v___y_5594_ == 0)
{
lean_object* v___x_5595_; lean_object* v_traceState_5596_; lean_object* v_env_5597_; lean_object* v_nextMacroScope_5598_; lean_object* v_ngen_5599_; lean_object* v_auxDeclNGen_5600_; lean_object* v_cache_5601_; lean_object* v_recordedDeps_5602_; lean_object* v_messages_5603_; lean_object* v_infoState_5604_; lean_object* v_snapshotTasks_5605_; lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5624_; 
lean_dec(v_snd_5574_);
lean_dec(v_fst_5573_);
lean_dec_ref(v_msg_5543_);
lean_dec_ref(v_tag_5539_);
lean_dec(v_cls_5537_);
v___x_5595_ = lean_st_ref_take(v___y_5555_);
v_traceState_5596_ = lean_ctor_get(v___x_5595_, 4);
v_env_5597_ = lean_ctor_get(v___x_5595_, 0);
v_nextMacroScope_5598_ = lean_ctor_get(v___x_5595_, 1);
v_ngen_5599_ = lean_ctor_get(v___x_5595_, 2);
v_auxDeclNGen_5600_ = lean_ctor_get(v___x_5595_, 3);
v_cache_5601_ = lean_ctor_get(v___x_5595_, 5);
v_recordedDeps_5602_ = lean_ctor_get(v___x_5595_, 6);
v_messages_5603_ = lean_ctor_get(v___x_5595_, 7);
v_infoState_5604_ = lean_ctor_get(v___x_5595_, 8);
v_snapshotTasks_5605_ = lean_ctor_get(v___x_5595_, 9);
v_isSharedCheck_5624_ = !lean_is_exclusive(v___x_5595_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5607_ = v___x_5595_;
v_isShared_5608_ = v_isSharedCheck_5624_;
goto v_resetjp_5606_;
}
else
{
lean_inc(v_snapshotTasks_5605_);
lean_inc(v_infoState_5604_);
lean_inc(v_messages_5603_);
lean_inc(v_recordedDeps_5602_);
lean_inc(v_cache_5601_);
lean_inc(v_traceState_5596_);
lean_inc(v_auxDeclNGen_5600_);
lean_inc(v_ngen_5599_);
lean_inc(v_nextMacroScope_5598_);
lean_inc(v_env_5597_);
lean_dec(v___x_5595_);
v___x_5607_ = lean_box(0);
v_isShared_5608_ = v_isSharedCheck_5624_;
goto v_resetjp_5606_;
}
v_resetjp_5606_:
{
uint64_t v_tid_5609_; lean_object* v_traces_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5623_; 
v_tid_5609_ = lean_ctor_get_uint64(v_traceState_5596_, sizeof(void*)*1);
v_traces_5610_ = lean_ctor_get(v_traceState_5596_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v_traceState_5596_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5612_ = v_traceState_5596_;
v_isShared_5613_ = v_isSharedCheck_5623_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_traces_5610_);
lean_dec(v_traceState_5596_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5623_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v___x_5614_; lean_object* v___x_5616_; 
v___x_5614_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5542_, v_traces_5610_);
lean_dec_ref(v_traces_5610_);
if (v_isShared_5613_ == 0)
{
lean_ctor_set(v___x_5612_, 0, v___x_5614_);
v___x_5616_ = v___x_5612_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5614_);
lean_ctor_set_uint64(v_reuseFailAlloc_5622_, sizeof(void*)*1, v_tid_5609_);
v___x_5616_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
lean_object* v___x_5618_; 
if (v_isShared_5608_ == 0)
{
lean_ctor_set(v___x_5607_, 4, v___x_5616_);
v___x_5618_ = v___x_5607_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_env_5597_);
lean_ctor_set(v_reuseFailAlloc_5621_, 1, v_nextMacroScope_5598_);
lean_ctor_set(v_reuseFailAlloc_5621_, 2, v_ngen_5599_);
lean_ctor_set(v_reuseFailAlloc_5621_, 3, v_auxDeclNGen_5600_);
lean_ctor_set(v_reuseFailAlloc_5621_, 4, v___x_5616_);
lean_ctor_set(v_reuseFailAlloc_5621_, 5, v_cache_5601_);
lean_ctor_set(v_reuseFailAlloc_5621_, 6, v_recordedDeps_5602_);
lean_ctor_set(v_reuseFailAlloc_5621_, 7, v_messages_5603_);
lean_ctor_set(v_reuseFailAlloc_5621_, 8, v_infoState_5604_);
lean_ctor_set(v_reuseFailAlloc_5621_, 9, v_snapshotTasks_5605_);
v___x_5618_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
lean_object* v___x_5619_; lean_object* v___x_5620_; 
v___x_5619_ = lean_st_ref_put(v___y_5555_, v___x_5618_);
v___x_5620_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_fst_5557_);
return v___x_5620_;
}
}
}
}
}
else
{
goto v___jp_5588_;
}
}
else
{
goto v___jp_5588_;
}
}
v___jp_5625_:
{
double v___x_5627_; double v___x_5628_; double v___x_5629_; uint8_t v___x_5630_; 
v___x_5627_ = lean_unbox_float(v_snd_5574_);
v___x_5628_ = lean_unbox_float(v_fst_5573_);
v___x_5629_ = lean_float_sub(v___x_5627_, v___x_5628_);
v___x_5630_ = lean_float_decLt(v___y_5626_, v___x_5629_);
v___y_5594_ = v___x_5630_;
goto v___jp_5593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2___boxed(lean_object** _args){
lean_object* v_cls_5641_ = _args[0];
lean_object* v_collapsed_5642_ = _args[1];
lean_object* v_tag_5643_ = _args[2];
lean_object* v_opts_5644_ = _args[3];
lean_object* v_clsEnabled_5645_ = _args[4];
lean_object* v_oldTraces_5646_ = _args[5];
lean_object* v_msg_5647_ = _args[6];
lean_object* v_resStartStop_5648_ = _args[7];
lean_object* v___y_5649_ = _args[8];
lean_object* v___y_5650_ = _args[9];
lean_object* v___y_5651_ = _args[10];
lean_object* v___y_5652_ = _args[11];
lean_object* v___y_5653_ = _args[12];
lean_object* v___y_5654_ = _args[13];
lean_object* v___y_5655_ = _args[14];
lean_object* v___y_5656_ = _args[15];
lean_object* v___y_5657_ = _args[16];
lean_object* v___y_5658_ = _args[17];
lean_object* v___y_5659_ = _args[18];
lean_object* v___y_5660_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_5661_; uint8_t v_clsEnabled_boxed_5662_; lean_object* v_res_5663_; 
v_collapsed_boxed_5661_ = lean_unbox(v_collapsed_5642_);
v_clsEnabled_boxed_5662_ = lean_unbox(v_clsEnabled_5645_);
v_res_5663_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v_cls_5641_, v_collapsed_boxed_5661_, v_tag_5643_, v_opts_5644_, v_clsEnabled_boxed_5662_, v_oldTraces_5646_, v_msg_5647_, v_resStartStop_5648_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
lean_dec(v___y_5659_);
lean_dec_ref(v___y_5658_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
lean_dec(v___y_5655_);
lean_dec_ref(v___y_5654_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
lean_dec(v___y_5651_);
lean_dec(v___y_5650_);
lean_dec_ref(v___y_5649_);
lean_dec_ref(v_opts_5644_);
return v_res_5663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(lean_object* v_mvarId_5664_, lean_object* v_val_5665_, lean_object* v___y_5666_){
_start:
{
lean_object* v___x_5668_; lean_object* v_mctx_5669_; lean_object* v_cache_5670_; lean_object* v_zetaDeltaFVarIds_5671_; lean_object* v_postponed_5672_; lean_object* v_diag_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5703_; 
v___x_5668_ = lean_st_ref_take(v___y_5666_);
v_mctx_5669_ = lean_ctor_get(v___x_5668_, 0);
v_cache_5670_ = lean_ctor_get(v___x_5668_, 1);
v_zetaDeltaFVarIds_5671_ = lean_ctor_get(v___x_5668_, 2);
v_postponed_5672_ = lean_ctor_get(v___x_5668_, 3);
v_diag_5673_ = lean_ctor_get(v___x_5668_, 4);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___x_5668_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5675_ = v___x_5668_;
v_isShared_5676_ = v_isSharedCheck_5703_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_diag_5673_);
lean_inc(v_postponed_5672_);
lean_inc(v_zetaDeltaFVarIds_5671_);
lean_inc(v_cache_5670_);
lean_inc(v_mctx_5669_);
lean_dec(v___x_5668_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5703_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v_depth_5677_; lean_object* v_levelAssignDepth_5678_; lean_object* v_lmvarCounter_5679_; lean_object* v_mvarCounter_5680_; lean_object* v_lDecls_5681_; lean_object* v_decls_5682_; lean_object* v_userNames_5683_; lean_object* v_lAssignment_5684_; lean_object* v_eAssignment_5685_; lean_object* v_dAssignment_5686_; lean_object* v_instanceTypedMVars_5687_; lean_object* v_synthNormMemo_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5702_; 
v_depth_5677_ = lean_ctor_get(v_mctx_5669_, 0);
v_levelAssignDepth_5678_ = lean_ctor_get(v_mctx_5669_, 1);
v_lmvarCounter_5679_ = lean_ctor_get(v_mctx_5669_, 2);
v_mvarCounter_5680_ = lean_ctor_get(v_mctx_5669_, 3);
v_lDecls_5681_ = lean_ctor_get(v_mctx_5669_, 4);
v_decls_5682_ = lean_ctor_get(v_mctx_5669_, 5);
v_userNames_5683_ = lean_ctor_get(v_mctx_5669_, 6);
v_lAssignment_5684_ = lean_ctor_get(v_mctx_5669_, 7);
v_eAssignment_5685_ = lean_ctor_get(v_mctx_5669_, 8);
v_dAssignment_5686_ = lean_ctor_get(v_mctx_5669_, 9);
v_instanceTypedMVars_5687_ = lean_ctor_get(v_mctx_5669_, 10);
v_synthNormMemo_5688_ = lean_ctor_get(v_mctx_5669_, 11);
v_isSharedCheck_5702_ = !lean_is_exclusive(v_mctx_5669_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5690_ = v_mctx_5669_;
v_isShared_5691_ = v_isSharedCheck_5702_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_synthNormMemo_5688_);
lean_inc(v_instanceTypedMVars_5687_);
lean_inc(v_dAssignment_5686_);
lean_inc(v_eAssignment_5685_);
lean_inc(v_lAssignment_5684_);
lean_inc(v_userNames_5683_);
lean_inc(v_decls_5682_);
lean_inc(v_lDecls_5681_);
lean_inc(v_mvarCounter_5680_);
lean_inc(v_lmvarCounter_5679_);
lean_inc(v_levelAssignDepth_5678_);
lean_inc(v_depth_5677_);
lean_dec(v_mctx_5669_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5702_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5695_; 
v___x_5692_ = lean_box(0);
v___x_5693_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratBitblaster_spec__3_spec__5___redArg(v_eAssignment_5685_, v_mvarId_5664_, v_val_5665_);
if (v_isShared_5691_ == 0)
{
lean_ctor_set(v___x_5690_, 8, v___x_5693_);
v___x_5695_ = v___x_5690_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_depth_5677_);
lean_ctor_set(v_reuseFailAlloc_5701_, 1, v_levelAssignDepth_5678_);
lean_ctor_set(v_reuseFailAlloc_5701_, 2, v_lmvarCounter_5679_);
lean_ctor_set(v_reuseFailAlloc_5701_, 3, v_mvarCounter_5680_);
lean_ctor_set(v_reuseFailAlloc_5701_, 4, v_lDecls_5681_);
lean_ctor_set(v_reuseFailAlloc_5701_, 5, v_decls_5682_);
lean_ctor_set(v_reuseFailAlloc_5701_, 6, v_userNames_5683_);
lean_ctor_set(v_reuseFailAlloc_5701_, 7, v_lAssignment_5684_);
lean_ctor_set(v_reuseFailAlloc_5701_, 8, v___x_5693_);
lean_ctor_set(v_reuseFailAlloc_5701_, 9, v_dAssignment_5686_);
lean_ctor_set(v_reuseFailAlloc_5701_, 10, v_instanceTypedMVars_5687_);
lean_ctor_set(v_reuseFailAlloc_5701_, 11, v_synthNormMemo_5688_);
v___x_5695_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5697_; 
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 0, v___x_5695_);
v___x_5697_ = v___x_5675_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5695_);
lean_ctor_set(v_reuseFailAlloc_5700_, 1, v_cache_5670_);
lean_ctor_set(v_reuseFailAlloc_5700_, 2, v_zetaDeltaFVarIds_5671_);
lean_ctor_set(v_reuseFailAlloc_5700_, 3, v_postponed_5672_);
lean_ctor_set(v_reuseFailAlloc_5700_, 4, v_diag_5673_);
v___x_5697_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5698_ = lean_st_ref_put(v___y_5666_, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5692_);
return v___x_5699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg___boxed(lean_object* v_mvarId_5704_, lean_object* v_val_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_){
_start:
{
lean_object* v_res_5708_; 
v_res_5708_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5704_, v_val_5705_, v___y_5706_);
lean_dec(v___y_5706_);
return v_res_5708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(lean_object* v_ctx_5714_, lean_object* v_goal_5715_, lean_object* v_reflectionResult_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_){
_start:
{
lean_object* v_cert_5730_; lean_object* v___y_5731_; lean_object* v___y_5732_; lean_object* v___y_5733_; lean_object* v___y_5734_; lean_object* v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5740_; lean_object* v___y_5741_; lean_object* v_toCold_5773_; lean_object* v_options_5774_; uint8_t v_hasTrace_5775_; 
v_toCold_5773_ = lean_ctor_get(v_a_5726_, 0);
v_options_5774_ = lean_ctor_get(v_toCold_5773_, 2);
v_hasTrace_5775_ = lean_ctor_get_uint8(v_options_5774_, sizeof(void*)*1);
if (v_hasTrace_5775_ == 0)
{
lean_object* v_config_5776_; lean_object* v_lratPath_5777_; uint8_t v_trimProofs_5778_; lean_object* v___x_5779_; 
v_config_5776_ = lean_ctor_get(v_ctx_5714_, 5);
v_lratPath_5777_ = lean_ctor_get(v_ctx_5714_, 4);
v_trimProofs_5778_ = lean_ctor_get_uint8(v_config_5776_, sizeof(void*)*3);
v___x_5779_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5777_, v_trimProofs_5778_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5779_) == 0)
{
lean_object* v_a_5780_; 
v_a_5780_ = lean_ctor_get(v___x_5779_, 0);
lean_inc(v_a_5780_);
lean_dec_ref_known(v___x_5779_, 1);
v_cert_5730_ = v_a_5780_;
v___y_5731_ = v_a_5717_;
v___y_5732_ = v_a_5718_;
v___y_5733_ = v_a_5719_;
v___y_5734_ = v_a_5720_;
v___y_5735_ = v_a_5721_;
v___y_5736_ = v_a_5722_;
v___y_5737_ = v_a_5723_;
v___y_5738_ = v_a_5724_;
v___y_5739_ = v_a_5725_;
v___y_5740_ = v_a_5726_;
v___y_5741_ = v_a_5727_;
goto v___jp_5729_;
}
else
{
lean_object* v_a_5781_; lean_object* v___x_5783_; uint8_t v_isShared_5784_; uint8_t v_isSharedCheck_5788_; 
lean_dec_ref(v_reflectionResult_5716_);
lean_dec(v_goal_5715_);
lean_dec_ref(v_ctx_5714_);
v_a_5781_ = lean_ctor_get(v___x_5779_, 0);
v_isSharedCheck_5788_ = !lean_is_exclusive(v___x_5779_);
if (v_isSharedCheck_5788_ == 0)
{
v___x_5783_ = v___x_5779_;
v_isShared_5784_ = v_isSharedCheck_5788_;
goto v_resetjp_5782_;
}
else
{
lean_inc(v_a_5781_);
lean_dec(v___x_5779_);
v___x_5783_ = lean_box(0);
v_isShared_5784_ = v_isSharedCheck_5788_;
goto v_resetjp_5782_;
}
v_resetjp_5782_:
{
lean_object* v___x_5786_; 
if (v_isShared_5784_ == 0)
{
v___x_5786_ = v___x_5783_;
goto v_reusejp_5785_;
}
else
{
lean_object* v_reuseFailAlloc_5787_; 
v_reuseFailAlloc_5787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5787_, 0, v_a_5781_);
v___x_5786_ = v_reuseFailAlloc_5787_;
goto v_reusejp_5785_;
}
v_reusejp_5785_:
{
return v___x_5786_;
}
}
}
}
else
{
lean_object* v_config_5789_; lean_object* v_lratPath_5790_; uint8_t v_trimProofs_5791_; lean_object* v_inheritedTraceOptions_5792_; lean_object* v___f_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; uint8_t v___x_5797_; lean_object* v___y_5799_; lean_object* v___y_5800_; lean_object* v_a_5801_; lean_object* v___y_5814_; lean_object* v___y_5815_; lean_object* v_a_5816_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v_a_5821_; lean_object* v___y_5831_; lean_object* v___y_5832_; lean_object* v_a_5833_; 
v_config_5789_ = lean_ctor_get(v_ctx_5714_, 5);
v_lratPath_5790_ = lean_ctor_get(v_ctx_5714_, 4);
v_trimProofs_5791_ = lean_ctor_get_uint8(v_config_5789_, sizeof(void*)*3);
v_inheritedTraceOptions_5792_ = lean_ctor_get(v_toCold_5773_, 11);
v___f_5793_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__1));
v___x_5794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__3));
v___x_5795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__11));
v___x_5796_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__24);
v___x_5797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5792_, v_options_5774_, v___x_5796_);
if (v___x_5797_ == 0)
{
lean_object* v___x_5866_; uint8_t v___x_5867_; 
v___x_5866_ = l_Lean_trace_profiler;
v___x_5867_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5774_, v___x_5866_);
if (v___x_5867_ == 0)
{
lean_object* v___x_5868_; 
v___x_5868_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5790_, v_trimProofs_5791_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5868_) == 0)
{
lean_object* v_a_5869_; 
v_a_5869_ = lean_ctor_get(v___x_5868_, 0);
lean_inc(v_a_5869_);
lean_dec_ref_known(v___x_5868_, 1);
v_cert_5730_ = v_a_5869_;
v___y_5731_ = v_a_5717_;
v___y_5732_ = v_a_5718_;
v___y_5733_ = v_a_5719_;
v___y_5734_ = v_a_5720_;
v___y_5735_ = v_a_5721_;
v___y_5736_ = v_a_5722_;
v___y_5737_ = v_a_5723_;
v___y_5738_ = v_a_5724_;
v___y_5739_ = v_a_5725_;
v___y_5740_ = v_a_5726_;
v___y_5741_ = v_a_5727_;
goto v___jp_5729_;
}
else
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5877_; 
lean_dec_ref(v_reflectionResult_5716_);
lean_dec(v_goal_5715_);
lean_dec_ref(v_ctx_5714_);
v_a_5870_ = lean_ctor_get(v___x_5868_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5868_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5872_ = v___x_5868_;
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5868_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
}
}
}
else
{
goto v___jp_5835_;
}
}
else
{
goto v___jp_5835_;
}
v___jp_5798_:
{
lean_object* v___x_5802_; double v___x_5803_; double v___x_5804_; double v___x_5805_; double v___x_5806_; double v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v___x_5802_ = lean_io_mono_nanos_now();
v___x_5803_ = lean_float_of_nat(v___y_5799_);
v___x_5804_ = lean_float_once(&l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof___closed__12);
v___x_5805_ = lean_float_div(v___x_5803_, v___x_5804_);
v___x_5806_ = lean_float_of_nat(v___x_5802_);
v___x_5807_ = lean_float_div(v___x_5806_, v___x_5804_);
v___x_5808_ = lean_box_float(v___x_5805_);
v___x_5809_ = lean_box_float(v___x_5807_);
v___x_5810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5810_, 0, v___x_5808_);
lean_ctor_set(v___x_5810_, 1, v___x_5809_);
v___x_5811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5811_, 0, v_a_5801_);
lean_ctor_set(v___x_5811_, 1, v___x_5810_);
v___x_5812_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5794_, v_hasTrace_5775_, v___x_5795_, v_options_5774_, v___x_5797_, v___y_5800_, v___f_5793_, v___x_5811_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
return v___x_5812_;
}
v___jp_5813_:
{
lean_object* v___x_5817_; 
v___x_5817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5817_, 0, v_a_5816_);
v___y_5799_ = v___y_5814_;
v___y_5800_ = v___y_5815_;
v_a_5801_ = v___x_5817_;
goto v___jp_5798_;
}
v___jp_5818_:
{
lean_object* v___x_5822_; double v___x_5823_; double v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5822_ = lean_io_get_num_heartbeats();
v___x_5823_ = lean_float_of_nat(v___y_5819_);
v___x_5824_ = lean_float_of_nat(v___x_5822_);
v___x_5825_ = lean_box_float(v___x_5823_);
v___x_5826_ = lean_box_float(v___x_5824_);
v___x_5827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5827_, 0, v___x_5825_);
lean_ctor_set(v___x_5827_, 1, v___x_5826_);
v___x_5828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5828_, 0, v_a_5821_);
lean_ctor_set(v___x_5828_, 1, v___x_5827_);
v___x_5829_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2(v___x_5794_, v_hasTrace_5775_, v___x_5795_, v_options_5774_, v___x_5797_, v___y_5820_, v___f_5793_, v___x_5828_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
return v___x_5829_;
}
v___jp_5830_:
{
lean_object* v___x_5834_; 
v___x_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5834_, 0, v_a_5833_);
v___y_5819_ = v___y_5831_;
v___y_5820_ = v___y_5832_;
v_a_5821_ = v___x_5834_;
goto v___jp_5818_;
}
v___jp_5835_:
{
lean_object* v___x_5836_; lean_object* v_a_5837_; lean_object* v___x_5838_; uint8_t v___x_5839_; 
v___x_5836_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__1___redArg(v_a_5727_);
v_a_5837_ = lean_ctor_get(v___x_5836_, 0);
lean_inc(v_a_5837_);
lean_dec_ref(v___x_5836_);
v___x_5838_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5839_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof_spec__1(v_options_5774_, v___x_5838_);
if (v___x_5839_ == 0)
{
lean_object* v___x_5840_; lean_object* v___x_5841_; 
v___x_5840_ = lean_io_mono_nanos_now();
v___x_5841_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5790_, v_trimProofs_5791_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5841_) == 0)
{
lean_object* v_a_5842_; lean_object* v___x_5843_; 
v_a_5842_ = lean_ctor_get(v___x_5841_, 0);
lean_inc(v_a_5842_);
lean_dec_ref_known(v___x_5841_, 1);
lean_inc_ref(v_reflectionResult_5716_);
v___x_5843_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5842_, v_ctx_5714_, v_reflectionResult_5716_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5843_) == 0)
{
lean_object* v_a_5844_; lean_object* v_satExpr_5845_; lean_object* v___x_5846_; 
v_a_5844_ = lean_ctor_get(v___x_5843_, 0);
lean_inc(v_a_5844_);
lean_dec_ref_known(v___x_5843_, 1);
v_satExpr_5845_ = lean_ctor_get(v_reflectionResult_5716_, 0);
lean_inc_ref(v_satExpr_5845_);
lean_dec_ref(v_reflectionResult_5716_);
v___x_5846_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5845_, v_a_5844_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5846_) == 0)
{
lean_object* v_a_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; 
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
lean_inc(v_a_5847_);
lean_dec_ref_known(v___x_5846_, 1);
v___x_5848_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5715_, v_a_5847_, v_a_5725_);
lean_dec_ref(v___x_5848_);
v___x_5849_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5799_ = v___x_5840_;
v___y_5800_ = v_a_5837_;
v_a_5801_ = v___x_5849_;
goto v___jp_5798_;
}
else
{
lean_object* v_a_5850_; 
lean_dec(v_goal_5715_);
v_a_5850_ = lean_ctor_get(v___x_5846_, 0);
lean_inc(v_a_5850_);
lean_dec_ref_known(v___x_5846_, 1);
v___y_5814_ = v___x_5840_;
v___y_5815_ = v_a_5837_;
v_a_5816_ = v_a_5850_;
goto v___jp_5813_;
}
}
else
{
lean_object* v_a_5851_; 
lean_dec_ref(v_reflectionResult_5716_);
lean_dec(v_goal_5715_);
v_a_5851_ = lean_ctor_get(v___x_5843_, 0);
lean_inc(v_a_5851_);
lean_dec_ref_known(v___x_5843_, 1);
v___y_5814_ = v___x_5840_;
v___y_5815_ = v_a_5837_;
v_a_5816_ = v_a_5851_;
goto v___jp_5813_;
}
}
else
{
lean_object* v_a_5852_; 
lean_dec_ref(v_reflectionResult_5716_);
lean_dec(v_goal_5715_);
lean_dec_ref(v_ctx_5714_);
v_a_5852_ = lean_ctor_get(v___x_5841_, 0);
lean_inc(v_a_5852_);
lean_dec_ref_known(v___x_5841_, 1);
v___y_5814_ = v___x_5840_;
v___y_5815_ = v_a_5837_;
v_a_5816_ = v_a_5852_;
goto v___jp_5813_;
}
}
else
{
lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5853_ = lean_io_get_num_heartbeats();
v___x_5854_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(v_lratPath_5790_, v_trimProofs_5791_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5854_) == 0)
{
lean_object* v_a_5855_; lean_object* v___x_5856_; 
v_a_5855_ = lean_ctor_get(v___x_5854_, 0);
lean_inc(v_a_5855_);
lean_dec_ref_known(v___x_5854_, 1);
lean_inc_ref(v_reflectionResult_5716_);
v___x_5856_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_a_5855_, v_ctx_5714_, v_reflectionResult_5716_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5856_) == 0)
{
lean_object* v_a_5857_; lean_object* v_satExpr_5858_; lean_object* v___x_5859_; 
v_a_5857_ = lean_ctor_get(v___x_5856_, 0);
lean_inc(v_a_5857_);
lean_dec_ref_known(v___x_5856_, 1);
v_satExpr_5858_ = lean_ctor_get(v_reflectionResult_5716_, 0);
lean_inc_ref(v_satExpr_5858_);
lean_dec_ref(v_reflectionResult_5716_);
v___x_5859_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5858_, v_a_5857_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5859_) == 0)
{
lean_object* v_a_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; 
v_a_5860_ = lean_ctor_get(v___x_5859_, 0);
lean_inc(v_a_5860_);
lean_dec_ref_known(v___x_5859_, 1);
v___x_5861_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5715_, v_a_5860_, v_a_5725_);
lean_dec_ref(v___x_5861_);
v___x_5862_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__2));
v___y_5819_ = v___x_5853_;
v___y_5820_ = v_a_5837_;
v_a_5821_ = v___x_5862_;
goto v___jp_5818_;
}
else
{
lean_object* v_a_5863_; 
lean_dec(v_goal_5715_);
v_a_5863_ = lean_ctor_get(v___x_5859_, 0);
lean_inc(v_a_5863_);
lean_dec_ref_known(v___x_5859_, 1);
v___y_5831_ = v___x_5853_;
v___y_5832_ = v_a_5837_;
v_a_5833_ = v_a_5863_;
goto v___jp_5830_;
}
}
else
{
lean_object* v_a_5864_; 
lean_dec_ref(v_reflectionResult_5716_);
lean_dec(v_goal_5715_);
v_a_5864_ = lean_ctor_get(v___x_5856_, 0);
lean_inc(v_a_5864_);
lean_dec_ref_known(v___x_5856_, 1);
v___y_5831_ = v___x_5853_;
v___y_5832_ = v_a_5837_;
v_a_5833_ = v_a_5864_;
goto v___jp_5830_;
}
}
else
{
lean_object* v_a_5865_; 
lean_dec_ref(v_reflectionResult_5716_);
lean_dec(v_goal_5715_);
lean_dec_ref(v_ctx_5714_);
v_a_5865_ = lean_ctor_get(v___x_5854_, 0);
lean_inc(v_a_5865_);
lean_dec_ref_known(v___x_5854_, 1);
v___y_5831_ = v___x_5853_;
v___y_5832_ = v_a_5837_;
v_a_5833_ = v_a_5865_;
goto v___jp_5830_;
}
}
}
}
v___jp_5729_:
{
lean_object* v___x_5742_; 
lean_inc_ref(v_reflectionResult_5716_);
v___x_5742_ = l___private_Lean_Meta_Tactic_BVDecide_Prover_Bitblast_0__Lean_Meta_Tactic_BVDecide_LratCert_toReflectionProof(v_cert_5730_, v_ctx_5714_, v_reflectionResult_5716_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
if (lean_obj_tag(v___x_5742_) == 0)
{
lean_object* v_a_5743_; lean_object* v_satExpr_5744_; lean_object* v___x_5745_; 
v_a_5743_ = lean_ctor_get(v___x_5742_, 0);
lean_inc(v_a_5743_);
lean_dec_ref_known(v___x_5742_, 1);
v_satExpr_5744_ = lean_ctor_get(v_reflectionResult_5716_, 0);
lean_inc_ref(v_satExpr_5744_);
lean_dec_ref(v_reflectionResult_5716_);
v___x_5745_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_satExpr_5744_, v_a_5743_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
if (lean_obj_tag(v___x_5745_) == 0)
{
lean_object* v_a_5746_; lean_object* v___x_5747_; lean_object* v___x_5749_; uint8_t v_isShared_5750_; uint8_t v_isSharedCheck_5755_; 
v_a_5746_ = lean_ctor_get(v___x_5745_, 0);
lean_inc(v_a_5746_);
lean_dec_ref_known(v___x_5745_, 1);
v___x_5747_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_goal_5715_, v_a_5746_, v___y_5739_);
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5755_ == 0)
{
lean_object* v_unused_5756_; 
v_unused_5756_ = lean_ctor_get(v___x_5747_, 0);
lean_dec(v_unused_5756_);
v___x_5749_ = v___x_5747_;
v_isShared_5750_ = v_isSharedCheck_5755_;
goto v_resetjp_5748_;
}
else
{
lean_dec(v___x_5747_);
v___x_5749_ = lean_box(0);
v_isShared_5750_ = v_isSharedCheck_5755_;
goto v_resetjp_5748_;
}
v_resetjp_5748_:
{
lean_object* v___x_5751_; lean_object* v___x_5753_; 
v___x_5751_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___closed__0));
if (v_isShared_5750_ == 0)
{
lean_ctor_set(v___x_5749_, 0, v___x_5751_);
v___x_5753_ = v___x_5749_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5751_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
else
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5764_; 
lean_dec(v_goal_5715_);
v_a_5757_ = lean_ctor_get(v___x_5745_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5745_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5759_ = v___x_5745_;
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5745_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5762_; 
if (v_isShared_5760_ == 0)
{
v___x_5762_ = v___x_5759_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
}
else
{
lean_object* v_a_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5772_; 
lean_dec_ref(v_reflectionResult_5716_);
lean_dec(v_goal_5715_);
v_a_5765_ = lean_ctor_get(v___x_5742_, 0);
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5742_);
if (v_isSharedCheck_5772_ == 0)
{
v___x_5767_ = v___x_5742_;
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_a_5765_);
lean_dec(v___x_5742_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5770_; 
if (v_isShared_5768_ == 0)
{
v___x_5770_ = v___x_5767_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_a_5765_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg___boxed(lean_object* v_ctx_5878_, lean_object* v_goal_5879_, lean_object* v_reflectionResult_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_, lean_object* v_a_5892_){
_start:
{
lean_object* v_res_5893_; 
v_res_5893_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5878_, v_goal_5879_, v_reflectionResult_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_);
lean_dec(v_a_5891_);
lean_dec_ref(v_a_5890_);
lean_dec(v_a_5889_);
lean_dec_ref(v_a_5888_);
lean_dec(v_a_5887_);
lean_dec_ref(v_a_5886_);
lean_dec(v_a_5885_);
lean_dec_ref(v_a_5884_);
lean_dec(v_a_5883_);
lean_dec(v_a_5882_);
lean_dec_ref(v_a_5881_);
return v_res_5893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker(lean_object* v_ctx_5894_, lean_object* v_goal_5895_, lean_object* v_reflectionResult_5896_, lean_object* v_x_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_, lean_object* v_a_5901_, lean_object* v_a_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_, lean_object* v_a_5906_, lean_object* v_a_5907_, lean_object* v_a_5908_){
_start:
{
lean_object* v___x_5910_; 
v___x_5910_ = l_Lean_Meta_Tactic_BVDecide_lratChecker___redArg(v_ctx_5894_, v_goal_5895_, v_reflectionResult_5896_, v_a_5898_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_, v_a_5903_, v_a_5904_, v_a_5905_, v_a_5906_, v_a_5907_, v_a_5908_);
return v___x_5910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed(lean_object* v_ctx_5911_, lean_object* v_goal_5912_, lean_object* v_reflectionResult_5913_, lean_object* v_x_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_){
_start:
{
lean_object* v_res_5927_; 
v_res_5927_ = l_Lean_Meta_Tactic_BVDecide_lratChecker(v_ctx_5911_, v_goal_5912_, v_reflectionResult_5913_, v_x_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_);
lean_dec(v_a_5925_);
lean_dec_ref(v_a_5924_);
lean_dec(v_a_5923_);
lean_dec_ref(v_a_5922_);
lean_dec(v_a_5921_);
lean_dec_ref(v_a_5920_);
lean_dec(v_a_5919_);
lean_dec_ref(v_a_5918_);
lean_dec(v_a_5917_);
lean_dec(v_a_5916_);
lean_dec_ref(v_a_5915_);
lean_dec(v_x_5914_);
return v_res_5927_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(lean_object* v_mvarId_5928_, lean_object* v_val_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_){
_start:
{
lean_object* v___x_5942_; 
v___x_5942_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___redArg(v_mvarId_5928_, v_val_5929_, v___y_5938_);
return v___x_5942_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0___boxed(lean_object* v_mvarId_5943_, lean_object* v_val_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_){
_start:
{
lean_object* v_res_5957_; 
v_res_5957_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__0(v_mvarId_5943_, v_val_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_);
lean_dec(v___y_5955_);
lean_dec_ref(v___y_5954_);
lean_dec(v___y_5953_);
lean_dec_ref(v___y_5952_);
lean_dec(v___y_5951_);
lean_dec_ref(v___y_5950_);
lean_dec(v___y_5949_);
lean_dec_ref(v___y_5948_);
lean_dec(v___y_5947_);
lean_dec(v___y_5946_);
lean_dec_ref(v___y_5945_);
return v_res_5957_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(lean_object* v_00_u03b1_5958_, lean_object* v_x_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_){
_start:
{
lean_object* v___x_5972_; 
v___x_5972_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___redArg(v_x_5959_);
return v___x_5972_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5973_, lean_object* v_x_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_){
_start:
{
lean_object* v_res_5987_; 
v_res_5987_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__3(v_00_u03b1_5973_, v_x_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_);
lean_dec(v___y_5985_);
lean_dec_ref(v___y_5984_);
lean_dec(v___y_5983_);
lean_dec_ref(v___y_5982_);
lean_dec(v___y_5981_);
lean_dec_ref(v___y_5980_);
lean_dec(v___y_5979_);
lean_dec_ref(v___y_5978_);
lean_dec(v___y_5977_);
lean_dec(v___y_5976_);
lean_dec_ref(v___y_5975_);
return v_res_5987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(lean_object* v_oldTraces_5988_, lean_object* v_data_5989_, lean_object* v_ref_5990_, lean_object* v_msg_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_){
_start:
{
lean_object* v___x_6004_; 
v___x_6004_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___redArg(v_oldTraces_5988_, v_data_5989_, v_ref_5990_, v_msg_5991_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
return v___x_6004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2___boxed(lean_object* v_oldTraces_6005_, lean_object* v_data_6006_, lean_object* v_ref_6007_, lean_object* v_msg_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_){
_start:
{
lean_object* v_res_6021_; 
v_res_6021_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_lratChecker_spec__2_spec__2(v_oldTraces_6005_, v_data_6006_, v_ref_6007_, v_msg_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_);
lean_dec(v___y_6019_);
lean_dec_ref(v___y_6018_);
lean_dec(v___y_6017_);
lean_dec_ref(v___y_6016_);
lean_dec(v___y_6015_);
lean_dec_ref(v___y_6014_);
lean_dec(v___y_6013_);
lean_dec_ref(v___y_6012_);
lean_dec(v___y_6011_);
lean_dec(v___y_6010_);
lean_dec_ref(v___y_6009_);
return v_res_6021_;
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
